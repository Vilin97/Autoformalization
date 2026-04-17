#!/usr/bin/python3.9
"""
Refactoring loop for Grothendieck Vanishing formalization.
Adapted from the autonomous_loop.py (sorry-closing) for code quality refactoring.

Architecture:
  1. Git pull
  2. Count sorry's (gate: must stay 0)
  3. PLANNER: fresh Claude session picks next task, writes strategy.md
  4. WORKER: fresh Claude session implements the refactoring
  5. Verify: sorry count still 0, compilation passes
  6. EVALUATOR: cheap LLM judges progress against review + principles
  7. Gates: revert if sorry's introduced or build broken
  8. Commit, alert, cooldown

Usage:
  # Single cycle:
  python scripts/refactor_loop.py

  # Continuous loop:
  python scripts/refactor_loop.py --loop

  # Dry run:
  python scripts/refactor_loop.py --dry-run

  # Skip planner (use existing strategy.md):
  python scripts/refactor_loop.py --worker-only
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from string import Template

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

REPO_DIR = Path(__file__).resolve().parent.parent
SETUP_CACHE_SCRIPT = REPO_DIR / "scripts" / "setup_local_cache.sh"
STATE_DIR = REPO_DIR / ".refactor-state"
PROMPTS_DIR = REPO_DIR / "scripts" / "prompts"
LOCK_FILE = STATE_DIR / "run.lock"
HISTORY_FILE = STATE_DIR / "history.jsonl"
STRATEGY_FILE = STATE_DIR / "strategy.md"
CYCLE_FILE = STATE_DIR / "cycle"
PRINCIPLES_FILE = STATE_DIR / "principles.md"
REVIEW_TASKS_FILE = STATE_DIR / "review_tasks.md"
ATTEMPTS_FILE = STATE_DIR / "attempts.md"
TASK_RESULTS_DIR = STATE_DIR / "task_results"

WORKING_BRANCH = "wip/grothendieck-vanishing"
EVALUATOR_HISTORY_WINDOW = 5
STUCK_THRESHOLD = 4  # consecutive stalls before flagging

CLAUDE_BIN = os.environ.get("CLAUDE_BIN", "claude")

# Timeouts (seconds)
PLANNER_TIMEOUT = 1800    # 30 min
WORKER_TIMEOUT = 10800    # 3 hours
EVALUATOR_TIMEOUT = 1800  # 30 min
COOLDOWN = 300            # 5 min between cycles

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def load_env():
    env_path = REPO_DIR / ".env"
    if env_path.exists():
        for line in env_path.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                key, _, value = line.partition("=")
                os.environ[key.strip()] = value.strip()


def ensure_local_cache():
    """Move .lake to local NVMe for fast olean access (GPFS is ~10-100x slower)."""
    if SETUP_CACHE_SCRIPT.exists():
        result = subprocess.run(
            ["bash", str(SETUP_CACHE_SCRIPT)],
            cwd=REPO_DIR,
            capture_output=True,
            text=True,
            check=False,
            timeout=600,
        )
        if result.stdout:
            print(result.stdout.strip())
        if result.returncode != 0:
            print(f"  Warning: local cache setup failed: {result.stderr[:200]}", file=sys.stderr)


def git(*args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
    )
    if check and result.returncode != 0:
        print(f"  git {' '.join(args)} failed: {result.stderr[:300]}", file=sys.stderr)
    return result.stdout.strip()


def count_sorrys() -> int:
    """Count actual sorry tactics in .lean source files (not comments/docs/strings)."""
    import re
    sorry_re = re.compile(r'(?<!\w)sorry(?!\w)')
    count = 0
    for f in REPO_DIR.glob("Aristotle/GrothendieckVanishing/main/*.lean"):
        in_docstring = False
        for line in f.read_text().splitlines():
            stripped = line.strip()
            # Skip line comments
            if stripped.startswith("--"):
                continue
            # Track docstring blocks (/-! ... -/ and /-- ... -/)
            if "/-" in stripped:
                in_docstring = True
            if in_docstring:
                if "-/" in stripped:
                    in_docstring = False
                continue
            # Match actual sorry tactic usage
            if sorry_re.search(stripped):
                count += 1
    return count


def read_file_safe(path: Path, max_chars: int = 8000) -> str:
    if not path.exists():
        return ""
    text = path.read_text()
    if len(text) > max_chars:
        return text[:max_chars] + f"\n... [truncated, {len(text)} chars total]"
    return text


def get_cycle_number() -> int:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    n = 0
    if CYCLE_FILE.exists():
        try:
            n = int(CYCLE_FILE.read_text().strip())
        except ValueError:
            pass
    n += 1
    CYCLE_FILE.write_text(str(n))
    return n


def load_history(n: int = EVALUATOR_HISTORY_WINDOW) -> list[dict]:
    if not HISTORY_FILE.exists():
        return []
    records = []
    for line in HISTORY_FILE.read_text().splitlines():
        line = line.strip()
        if line:
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return records[-n:]


def append_history(record: dict):
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with open(HISTORY_FILE, "a") as f:
        f.write(json.dumps(record) + "\n")


def format_history(history: list[dict]) -> str:
    if not history:
        return "(no previous cycles)"
    lines = []
    for h in history:
        ev = h.get("evaluation", {})
        lines.append(
            f"- Cycle {h.get('cycle', '?')}: "
            f"score={ev.get('progress_score', '?')}, "
            f"{ev.get('summary', 'no summary')}"
        )
    return "\n".join(lines)


def consecutive_stuck(history: list[dict]) -> int:
    count = 0
    for record in reversed(history):
        if record.get("evaluation", {}).get("progress_score", 0) <= 0:
            count += 1
        else:
            break
    return count


# ---------------------------------------------------------------------------
# File lock
# ---------------------------------------------------------------------------

class FileLock:
    def __init__(self, path: Path):
        self.path = path
        self._fd = None

    def acquire(self) -> bool:
        import fcntl
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._fd = open(self.path, "w")
        try:
            fcntl.flock(self._fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self._fd.write(str(os.getpid()))
            self._fd.flush()
            return True
        except OSError:
            self._fd.close()
            self._fd = None
            return False

    def release(self):
        if self._fd:
            import fcntl
            fcntl.flock(self._fd, fcntl.LOCK_UN)
            self._fd.close()
            self._fd = None

    def __enter__(self):
        if not self.acquire():
            raise RuntimeError("Could not acquire lock — another cycle is running")
        return self

    def __exit__(self, *args):
        self.release()


# ---------------------------------------------------------------------------
# Claude invocations
# ---------------------------------------------------------------------------

def run_claude(
    prompt: str,
    timeout: int = WORKER_TIMEOUT,
    model: str | None = None,
    tools: str | None = None,
    json_schema: dict | None = None,
    skip_permissions: bool = True,
) -> tuple[int, str]:
    """Run a fresh Claude Code session. Returns (exit_code, stdout)."""
    mcp_config = str(REPO_DIR / ".mcp.json")
    cmd = [CLAUDE_BIN, "-p", prompt, "--no-session-persistence",
           "--mcp-config", mcp_config]

    if skip_permissions:
        cmd.append("--dangerously-skip-permissions")
    if model:
        cmd.extend(["--model", model])
    if tools is not None:
        cmd.extend(["--tools", tools])
    if json_schema is not None:
        cmd.extend(["--json-schema", json.dumps(json_schema)])
        cmd.extend(["--output-format", "json"])

    # Unset CLAUDECODE env var to allow nested sessions
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    result = subprocess.run(
        cmd,
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        env=env,
    )
    stdout = result.stdout[-5000:] if result.stdout else ""
    return result.returncode, stdout


# ---------------------------------------------------------------------------
# Planner
# ---------------------------------------------------------------------------

def run_planner(cycle: int, history: list[dict]) -> str:
    """Run the planner to produce strategy.md. Returns the strategy text."""
    template = Template((PROMPTS_DIR / "planner.md").read_text())
    prompt = template.safe_substitute(
        cycle=cycle,
        history=format_history(history),
    )

    print("  Running planner...")
    exit_code, output = run_claude(
        prompt,
        timeout=PLANNER_TIMEOUT,
        model="opus",
    )
    print(f"  Planner finished (exit={exit_code})")

    # The planner writes strategy.md directly; read it back
    strategy = read_file_safe(STRATEGY_FILE)
    if not strategy:
        # Fallback: use planner output as strategy
        strategy = output[-3000:] if output else "Pick the next uncompleted task from review_tasks.md Phase 1."
        STRATEGY_FILE.write_text(strategy)

    return strategy


# ---------------------------------------------------------------------------
# Worker
# ---------------------------------------------------------------------------

def run_worker(cycle: int, strategy: str) -> tuple[int, str]:
    """Run the worker to implement the refactoring. Returns (exit_code, output)."""
    template = Template((PROMPTS_DIR / "worker.md").read_text())
    principles = read_file_safe(PRINCIPLES_FILE)
    prompt = template.safe_substitute(
        cycle=cycle,
        strategy=strategy,
        principles=principles,
    )

    print(f"  Running worker (timeout: {WORKER_TIMEOUT}s)...")
    exit_code, output = run_claude(
        prompt,
        timeout=WORKER_TIMEOUT,
        model="opus",
    )
    print(f"  Worker finished (exit={exit_code})")
    return exit_code, output


# ---------------------------------------------------------------------------
# Evaluator
# ---------------------------------------------------------------------------

EVALUATOR_SCHEMA = {
    "type": "object",
    "properties": {
        "progress_score": {
            "type": "integer",
            "description": "-2 (regression) to +2 (breakthrough). 0 = stall.",
            "minimum": -2,
            "maximum": 2,
        },
        "summary": {
            "type": "string",
            "description": "One sentence: what happened this cycle.",
        },
        "principle_violations": {
            "type": "array",
            "items": {"type": "string"},
            "description": "List of principle violations found. Empty if none.",
        },
        "task_addressed": {
            "type": "boolean",
            "description": "Whether the worker addressed the assigned task.",
        },
        "task_complete": {
            "type": "boolean",
            "description": "Whether the task can be marked done.",
        },
        "stuck_on": {
            "type": "string",
            "description": "Current blocker, empty if not stuck.",
        },
        "strategy_recommendation": {
            "type": "string",
            "description": "Concrete instructions for the next planner cycle.",
        },
        "attempts_entry": {
            "type": "string",
            "description": "Compact 1-line entry for attempts.md.",
        },
    },
    "required": [
        "progress_score", "summary", "principle_violations",
        "task_addressed", "task_complete", "stuck_on",
        "strategy_recommendation", "attempts_entry",
    ],
}


def run_evaluator(
    cycle: int,
    strategy: str,
    diff: str,
    report: str,
    history: list[dict],
) -> dict:
    """Run the evaluator. Returns structured JSON."""
    template = Template((PROMPTS_DIR / "evaluator.md").read_text())
    principles = read_file_safe(PRINCIPLES_FILE)
    prompt = template.safe_substitute(
        cycle=cycle,
        principles=principles,
        strategy=strategy[:2000],
        diff=diff[:6000] if diff else "(no changes)",
        report=report[:3000] if report else "(no report)",
        history=format_history(history),
    )

    print("  Running evaluator...")
    exit_code, output = run_claude(
        prompt,
        timeout=EVALUATOR_TIMEOUT,
        model="opus",
        tools="",
        json_schema=EVALUATOR_SCHEMA,
    )

    if exit_code != 0:
        print(f"  Evaluator failed (exit={exit_code})", file=sys.stderr)
        return _default_eval("Evaluator failed to run.")

    try:
        outer = json.loads(output)
        # Claude --output-format json wraps structured output in a metadata envelope
        if "structured_output" in outer and isinstance(outer["structured_output"], dict):
            return outer["structured_output"]
        if "result" in outer and outer["result"]:
            return json.loads(outer["result"])
        return outer
    except (json.JSONDecodeError, KeyError):
        try:
            return json.loads(output)
        except json.JSONDecodeError:
            print(f"  Evaluator returned non-JSON: {output[:300]}", file=sys.stderr)
            return _default_eval("Evaluator output unparseable.")


def _default_eval(msg: str) -> dict:
    return {
        "progress_score": 0,
        "summary": msg,
        "principle_violations": [],
        "task_addressed": False,
        "task_complete": False,
        "stuck_on": "",
        "strategy_recommendation": "Re-attempt the same task with a clearer approach.",
        "attempts_entry": f"Cycle ?: {msg}",
    }


# ---------------------------------------------------------------------------
# Gates
# ---------------------------------------------------------------------------

def apply_gates(cycle: int, sorry_before: int, sorry_after: int, evaluation: dict) -> bool:
    """
    Apply mechanical gates. Returns True if cycle is accepted, False if reverted.
    """
    accepted = True

    # Gate 1: Sorry count must not increase from 0
    if sorry_after > sorry_before:
        print(f"  GATE FAIL: sorry count increased ({sorry_before} → {sorry_after}). Reverting.")
        git("checkout", "--", ".")
        evaluation["progress_score"] = -2
        evaluation["summary"] += " [REVERTED: sorry introduced]"
        accepted = False

    # Gate 2: Verify compilation of modified files
    if accepted:
        modified = git("diff", "--name-only", "HEAD", check=False)
        lean_files = [f for f in modified.splitlines() if f.endswith(".lean")]
        for f in lean_files[:5]:  # check up to 5 files
            result = subprocess.run(
                ["lake", "env", "lean", f],
                cwd=REPO_DIR,
                capture_output=True,
                text=True,
                check=False,
                timeout=300,
            )
            if result.returncode != 0:
                print(f"  GATE FAIL: {f} does not compile. Reverting.")
                print(f"    Error: {result.stderr[:300]}")
                git("checkout", "--", ".")
                evaluation["progress_score"] = -2
                evaluation["summary"] += f" [REVERTED: {f} failed to compile]"
                accepted = False
                break

    return accepted


# ---------------------------------------------------------------------------
# Telegram
# ---------------------------------------------------------------------------

def send_telegram(message: str):
    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "398863010")
    if not token:
        return
    try:
        result = subprocess.run(
            [
                "curl", "-s", "-X", "POST",
                f"https://api.telegram.org/bot{token}/sendMessage",
                "-d", f"chat_id={chat_id}",
                "--data-urlencode", f"text={message}",
            ],
            capture_output=True,
            text=True,
            check=False,
            timeout=10,
        )
        if '"ok":false' in (result.stdout or ""):
            print(f"  Telegram error: {result.stdout[:200]}", file=sys.stderr)
    except Exception as e:
        print(f"  Telegram send failed: {e}", file=sys.stderr)


# ---------------------------------------------------------------------------
# Main cycle
# ---------------------------------------------------------------------------

def run_cycle(dry_run: bool = False, worker_only: bool = False) -> dict:
    """Run one full cycle: planner → worker → gates → evaluator → commit."""
    load_env()
    cycle = get_cycle_number()
    ts = datetime.now(timezone.utc).isoformat()

    print(f"\n{'='*60}")
    print(f"REFACTOR Cycle {cycle} — {ts}")
    print(f"{'='*60}")

    # 0. Ensure .lake is on local NVMe (GPFS is too slow for olean I/O)
    ensure_local_cache()

    # 1. Git pull
    print("  Pulling latest...")
    git("checkout", WORKING_BRANCH, check=False)
    git("pull", "--rebase", "origin", WORKING_BRANCH, check=False)

    # 2. Pre-cycle sorry count
    sorry_before = count_sorrys()
    print(f"  Sorry count: {sorry_before}")
    if sorry_before > 0:
        print(f"  WARNING: {sorry_before} sorry's detected before cycle starts!")

    # 3. Load history
    history = load_history()
    stuck_count = consecutive_stuck(history)
    if stuck_count >= STUCK_THRESHOLD:
        print(f"  WARNING: stuck for {stuck_count} consecutive cycles")

    # 4. Planner
    if worker_only:
        strategy = read_file_safe(STRATEGY_FILE) or "Pick the next uncompleted task from review_tasks.md."
        print(f"  Using existing strategy ({len(strategy)} chars)")
    else:
        strategy = run_planner(cycle, history)
    print(f"  Strategy: {strategy[:200]}...")

    if dry_run:
        print("  [DRY RUN] Would run worker with above strategy.")
        return {"cycle": cycle, "dry_run": True}

    # 5. Worker
    worker_exit, worker_output = run_worker(cycle, strategy)

    # 6. Post-cycle checks
    sorry_after = count_sorrys()
    print(f"  Sorry count after: {sorry_after}")

    diff = git("diff", "--stat", check=False)
    diff_full = git("diff", check=False)

    # Read worker's task report
    report_path = TASK_RESULTS_DIR / f"cycle_{cycle}.md"
    report = read_file_safe(report_path)

    # 7. Gates (before evaluator, so we know if we reverted)
    accepted = apply_gates(cycle, sorry_before, sorry_after, _default_eval(""))

    # 8. Evaluator
    evaluation = run_evaluator(cycle, strategy, diff_full[:6000], report, history)
    print(f"  Evaluation: score={evaluation.get('progress_score')}, "
          f"{evaluation.get('summary', '')}")

    # If gates failed, override score
    if not accepted:
        evaluation["progress_score"] = min(evaluation.get("progress_score", 0), -1)

    # 9. Update attempts.md
    entry = evaluation.get("attempts_entry", "")
    if entry:
        with open(ATTEMPTS_FILE, "a") as f:
            f.write(f"\nCycle {cycle}: {entry}")

    # 10. Write strategy recommendation for next cycle
    rec = evaluation.get("strategy_recommendation", "")
    if rec:
        STRATEGY_FILE.write_text(rec)

    # 11. Record history
    record = {
        "cycle": cycle,
        "timestamp": ts,
        "sorry_before": sorry_before,
        "sorry_after": sorry_after,
        "worker_exit_code": worker_exit,
        "accepted": accepted,
        "evaluation": evaluation,
    }
    append_history(record)

    # 12. Commit if changes were accepted and there's something to commit
    if accepted:
        staged = git("diff", "--name-only", check=False)
        if staged:
            git("add", "-A")
            msg = f"refactor: cycle {cycle} — {evaluation.get('summary', 'no summary')}"
            git("commit", "-m", msg, check=False)
            git("push", "origin", WORKING_BRANCH, check=False)
            print("  Changes committed and pushed.")
        else:
            print("  No changes to commit.")

    # 13. Telegram
    score = evaluation.get("progress_score", 0)
    emoji = {-2: "🔴", -1: "🟠", 0: "⚪", 1: "🟢", 2: "🟢🟢"}.get(score, "?")
    msg = (
        f"{emoji} *Refactor Cycle {cycle}*\n"
        f"{evaluation.get('summary', 'no summary')}"
    )
    violations = evaluation.get("principle_violations", [])
    if violations:
        msg += f"\n⚠️ Violations: {', '.join(violations[:3])}"
    if stuck_count >= 3:
        msg += f"\n⏳ Stuck for {stuck_count} cycles"
    send_telegram(msg)

    print(f"  Cycle {cycle} complete (score={score}).")
    return record


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Refactoring loop")
    parser.add_argument("--loop", action="store_true", help="Run continuously")
    parser.add_argument("--interval", type=int, default=COOLDOWN,
                        help=f"Seconds between cycles (default: {COOLDOWN})")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show strategy without running worker")
    parser.add_argument("--worker-only", action="store_true",
                        help="Skip planner, use existing strategy.md")
    args = parser.parse_args()

    lock = FileLock(LOCK_FILE)
    if not lock.acquire():
        print("Another cycle is already running. Exiting.")
        sys.exit(0)

    try:
        if args.loop:
            print(f"Starting refactoring loop (interval={args.interval}s)")
            while True:
                try:
                    run_cycle(
                        dry_run=args.dry_run,
                        worker_only=args.worker_only,
                    )
                except subprocess.TimeoutExpired as e:
                    print(f"  Cycle timed out: {e}", file=sys.stderr)
                    send_telegram(f"⏰ Refactor cycle timed out")
                except Exception as e:
                    print(f"  Cycle failed: {e}", file=sys.stderr)
                    send_telegram(f"❌ Refactor cycle failed: {e}")
                print(f"  Sleeping {args.interval}s until next cycle...")
                time.sleep(args.interval)
        else:
            run_cycle(
                dry_run=args.dry_run,
                worker_only=args.worker_only,
            )
    finally:
        lock.release()


if __name__ == "__main__":
    # Unbuffered output for real-time logging
    sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', 1)
    sys.stderr = os.fdopen(sys.stderr.fileno(), 'w', 1)
    main()
