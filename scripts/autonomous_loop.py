#!/usr/bin/env python3
"""
Autonomous formalization loop.

Outer loop that manages fresh Claude Code sessions, uses an LLM evaluator
to assess progress, and escalates strategy when stuck. Designed to replace
the human in the loop for "keep going" / "look at plan.md" style prompts.

Architecture:
  1. Git pull (pick up other agents' work)
  2. Snapshot state (sorry list, plan.md, critique.md, LOG.md)
  3. WORKER: full Claude Code session (fresh, no context accumulation)
  4. Snapshot state again
  5. EVALUATOR: cheap LLM judges whether real progress was made
  6. Write strategy for next cycle (read by next worker)
  7. If stuck too long, consult Gemini for mathematical insight

Usage:
  # Single cycle (for cron):
  python scripts/autonomous_loop.py

  # Continuous loop (for tmux/screen):
  python scripts/autonomous_loop.py --loop --interval 600

  # Dry run (show what would happen without running worker):
  python scripts/autonomous_loop.py --dry-run
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

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

REPO_DIR = Path(__file__).resolve().parent.parent
STATE_DIR = REPO_DIR / ".prover-state"
LOCK_FILE = STATE_DIR / "run.lock"
HISTORY_FILE = STATE_DIR / "history.jsonl"  # one JSON object per cycle
STRATEGY_FILE = STATE_DIR / "strategy.md"
CYCLE_FILE = STATE_DIR / "cycle"

# Which branch the worker operates on
WORKING_BRANCH = "wip/grothendieck-vanishing"

# How many recent cycles the evaluator sees for trajectory context
EVALUATOR_HISTORY_WINDOW = 5

# After this many consecutive "stuck" evaluations, consult Gemini
GEMINI_ESCALATION_THRESHOLD = 6

# Claude CLI path (auto-detect)
CLAUDE_BIN = os.environ.get("CLAUDE_BIN", "claude")

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def load_env():
    """Load .env file into os.environ if it exists."""
    env_path = REPO_DIR / ".env"
    if env_path.exists():
        for line in env_path.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                key, _, value = line.partition("=")
                os.environ.setdefault(key.strip(), value.strip())


def git(*args: str, check: bool = True) -> str:
    """Run a git command in the repo directory, return stdout."""
    result = subprocess.run(
        ["git", *args],
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
    )
    if check and result.returncode != 0:
        print(f"git {' '.join(args)} failed: {result.stderr}", file=sys.stderr)
    return result.stdout.strip()


def find_sorry_locations() -> list[str]:
    """Return list of 'file:line: sorry' strings via grep."""
    result = subprocess.run(
        ["grep", "-rn", r"\bsorry\b", "--include=*.lean"],
        cwd=REPO_DIR / "Aristotle",
        capture_output=True,
        text=True,
        check=False,
    )
    lines = []
    for line in result.stdout.splitlines():
        # Skip comments
        stripped = line.split(":", 2)[-1].strip() if ":" in line else line.strip()
        if stripped.startswith("--"):
            continue
        # Skip string literals containing "sorry" in docstrings
        if '\"' in stripped and "sorry" in stripped:
            continue
        lines.append(line)
    return lines


def read_file_safe(path: Path, max_chars: int = 5000) -> str:
    """Read a file, truncating if too long. Return '' if missing."""
    if not path.exists():
        return ""
    text = path.read_text()
    if len(text) > max_chars:
        return text[:max_chars] + f"\n... [truncated, {len(text)} chars total]"
    return text


def get_cycle_number() -> int:
    """Get and increment the cycle counter."""
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
    """Load the last n cycle records from history."""
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
    """Append a cycle record to history."""
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with open(HISTORY_FILE, "a") as f:
        f.write(json.dumps(record) + "\n")


def consecutive_stuck_cycles(history: list[dict]) -> int:
    """Count how many recent cycles the evaluator judged as 'stuck'."""
    count = 0
    for record in reversed(history):
        eval_result = record.get("evaluation", {})
        if eval_result.get("progress_score", 0) <= 0:
            count += 1
        else:
            break
    return count


# ---------------------------------------------------------------------------
# File lock (prevent concurrent runs)
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
# Worker: run a full Claude Code session
# ---------------------------------------------------------------------------

def build_worker_prompt(cycle: int, strategy: str, sorry_list: list[str]) -> str:
    """Build the prompt for the worker Claude session."""
    sorry_summary = f"{len(sorry_list)} sorry's" if sorry_list else "0 sorry's"
    sorry_detail = "\n".join(sorry_list[:20]) if sorry_list else "(none)"

    return f"""\
You are cycle {cycle} of an autonomous proving loop. Each cycle is a fresh session —
you have no memory of previous cycles except what's in the persistent files.

## Current state
- Sorry count: {sorry_summary}
- Sorry locations:
{sorry_detail}

## Strategy for this cycle
{strategy}

## Your instructions
Read plan.md and critique.md in the active project directory for context.
Then execute the full /babysit protocol: /critique, /plan, /submit-aristotle,
/prove, /check-aristotle, /log, /cleanup, /simplify, /commit, /alert.

Rules:
- You MUST make concrete progress. Zero-diff cycles are forbidden.
- If Mathlib is missing something, build it. "Mathlib gap" is not an excuse.
- Don't poll Aristotle repeatedly. Submit jobs, then prove things yourself.
- Never increase maxHeartbeats above 200000. Decompose proofs instead.
"""


def run_worker(prompt: str, budget_usd: float = 5.0) -> tuple[int, str]:
    """Run a full Claude Code worker session. Returns (exit_code, output)."""
    cmd = [
        CLAUDE_BIN,
        "-p", prompt,
        "--dangerously-skip-permissions",
        "--no-session-persistence",
        "--model", "sonnet",
        "--max-budget-usd", str(budget_usd),
    ]
    print(f"  Starting worker (budget: ${budget_usd})...")
    result = subprocess.run(
        cmd,
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
        timeout=3600,  # 1 hour max
    )
    return result.returncode, result.stdout[-3000:] if result.stdout else ""


# ---------------------------------------------------------------------------
# Evaluator: cheap LLM judges progress
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
        "stuck_on": {
            "type": "string",
            "description": "What the agent is stuck on, if anything. Empty string if not stuck.",
        },
        "strategy_for_next_cycle": {
            "type": "string",
            "description": "Concrete instructions for the next cycle's worker. Be specific about what to try differently.",
        },
    },
    "required": ["progress_score", "summary", "stuck_on", "strategy_for_next_cycle"],
}


def build_evaluator_prompt(
    cycle: int,
    git_diff: str,
    log_entry: str,
    sorry_before: list[str],
    sorry_after: list[str],
    history: list[dict],
    worker_output: str,
) -> str:
    """Build the prompt for the evaluator."""
    history_text = ""
    if history:
        history_text = "## Recent cycle history\n"
        for h in history:
            ev = h.get("evaluation", {})
            history_text += (
                f"- Cycle {h.get('cycle', '?')}: "
                f"score={ev.get('progress_score', '?')}, "
                f"{ev.get('summary', 'no summary')}\n"
            )

    return f"""\
You are evaluating cycle {cycle} of an autonomous theorem-proving agent.
Your job: judge whether REAL progress was made, and decide what the next cycle should do.

## What counts as progress
- Closing a sorry (even a small one) = solid progress (+1 or +2)
- Decomposing a sorry into well-chosen sub-lemmas = progress (+1)
- Building Mathlib infrastructure needed for a proof = progress (+1)
- Meaningful refactoring that makes proofs tractable = minor progress (+1)
- Submitting to Aristotle without other work = stall (0)
- Changing comments/docs without proof progress = stall (0)
- Repeating a failed approach = regression (-1)
- Introducing errors or breaking the build = regression (-2)
- Zero git diff = stall (0)

## Sorry's before this cycle ({len(sorry_before)} total)
{chr(10).join(sorry_before[:15]) or '(none)'}

## Sorry's after this cycle ({len(sorry_after)} total)
{chr(10).join(sorry_after[:15]) or '(none)'}

## Git diff (this cycle)
{git_diff[:4000] if git_diff else '(empty — no changes)'}

## LOG.md entry (this cycle)
{log_entry[:2000] if log_entry else '(no log entry)'}

## Worker's own summary
{worker_output[:2000] if worker_output else '(no output)'}

{history_text}

## Your task
Judge this cycle and decide the strategy for the next one. Be specific and concrete
in your strategy — don't say "try harder", say "the stuck sorry at X.lean:42 has been
attempted via Y for 3 cycles; next cycle should try Z instead because...".

If the agent keeps failing on the same sorry, escalate: suggest building infrastructure,
trying a different proof approach, or restructuring the argument.
"""


def run_evaluator(prompt: str) -> dict:
    """Run the evaluator (cheap, fast, no tools)."""
    cmd = [
        CLAUDE_BIN,
        "-p", prompt,
        "--bare",
        "--tools", "",
        "--model", "haiku",
        "--no-session-persistence",
        "--json-schema", json.dumps(EVALUATOR_SCHEMA),
        "--output-format", "json",
    ]
    print("  Running evaluator...")
    result = subprocess.run(
        cmd,
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
        timeout=120,
    )
    if result.returncode != 0:
        print(f"  Evaluator failed: {result.stderr[:500]}", file=sys.stderr)
        return {
            "progress_score": 0,
            "summary": "Evaluator failed to run.",
            "stuck_on": "",
            "strategy_for_next_cycle": "Normal operation. Run the full /babysit protocol.",
        }
    try:
        # --output-format json wraps in {"result": ...}
        outer = json.loads(result.stdout)
        if "result" in outer:
            return json.loads(outer["result"])
        return outer
    except (json.JSONDecodeError, KeyError):
        # Try parsing the raw output
        try:
            return json.loads(result.stdout)
        except json.JSONDecodeError:
            print(f"  Evaluator returned non-JSON: {result.stdout[:300]}", file=sys.stderr)
            return {
                "progress_score": 0,
                "summary": "Evaluator output unparseable.",
                "stuck_on": "",
                "strategy_for_next_cycle": "Normal operation. Run the full /babysit protocol.",
            }


# ---------------------------------------------------------------------------
# Gemini consultation (escalation for deep stuck)
# ---------------------------------------------------------------------------

def consult_gemini(stuck_on: str, sorry_context: str) -> str:
    """Ask Gemini for mathematical insight when deeply stuck."""
    try:
        from google import genai
    except ImportError:
        return "(google-genai not installed, skipping Gemini consultation)"

    api_key = os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    if not api_key:
        return "(no Gemini API key found, skipping consultation)"

    client = genai.Client(api_key=api_key)

    prompt = f"""\
I'm formalizing a mathematical proof in Lean 4 with Mathlib and I'm stuck.
The theorem is Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7):
for a Noetherian topological space X of dimension n, H^i(X, F) = 0 for all i > n.

I'm stuck on: {stuck_on}

Here is the relevant Lean code context:
{sorry_context[:6000]}

Please suggest:
1. The mathematical argument that should work here (not Lean code, just the math).
2. What Mathlib lemmas or theories might be relevant.
3. An alternative proof strategy if the current approach seems wrong.
"""
    try:
        response = client.models.generate_content(
            model="gemini-2.5-flash",
            contents=prompt,
        )
        return response.text[:4000]
    except Exception as e:
        return f"(Gemini consultation failed: {e})"


# ---------------------------------------------------------------------------
# Telegram notification
# ---------------------------------------------------------------------------

def send_telegram(message: str):
    """Send a Telegram notification."""
    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "398863010")
    if not token:
        return
    try:
        subprocess.run(
            [
                "curl", "-s", "-X", "POST",
                f"https://api.telegram.org/bot{token}/sendMessage",
                "-d", f"chat_id={chat_id}",
                "-d", "parse_mode=Markdown",
                "--data-urlencode", f"text={message}",
            ],
            capture_output=True,
            check=False,
            timeout=10,
        )
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Main cycle
# ---------------------------------------------------------------------------

def run_cycle(dry_run: bool = False, budget_usd: float = 5.0) -> dict:
    """Run one full cycle: worker → evaluator → strategy update."""
    load_env()
    cycle = get_cycle_number()
    ts = datetime.now(timezone.utc).isoformat()
    print(f"\n{'='*60}")
    print(f"Cycle {cycle} starting at {ts}")
    print(f"{'='*60}")

    # 1. Git pull
    print("  Pulling latest...")
    git("checkout", WORKING_BRANCH, check=False)
    git("pull", "--rebase", "origin", WORKING_BRANCH, check=False)

    # 2. Snapshot before
    sorry_before = find_sorry_locations()
    log_before = read_file_safe(REPO_DIR / "Aristotle" / "GrothendieckVanishing" / "LOG.md")
    print(f"  Sorry count before: {len(sorry_before)}")

    # 3. Load history and determine strategy
    history = load_history()
    stuck_count = consecutive_stuck_cycles(history)
    strategy = read_file_safe(STRATEGY_FILE) or "Normal operation. Run the full /babysit protocol."

    # Gemini escalation if deeply stuck
    if stuck_count >= GEMINI_ESCALATION_THRESHOLD and sorry_before:
        print(f"  ESCALATION: stuck for {stuck_count} cycles, consulting Gemini...")
        # Get context around the first sorry
        first_sorry = sorry_before[0] if sorry_before else ""
        stuck_desc = history[-1].get("evaluation", {}).get("stuck_on", "") if history else ""
        gemini_advice = consult_gemini(stuck_desc or first_sorry, first_sorry)
        strategy = f"""\
ESCALATION: You have been stuck for {stuck_count} consecutive cycles.

A mathematical consultant (Gemini) was asked for help. Their advice:

{gemini_advice}

MANDATORY: Incorporate this advice. Try a fundamentally different approach.
Do NOT continue with the same strategy that has failed for {stuck_count} cycles.
"""
        print(f"  Gemini advice received ({len(gemini_advice)} chars)")

    print(f"  Strategy: {strategy[:200]}...")

    if dry_run:
        print("  [DRY RUN] Would run worker with above strategy.")
        return {"cycle": cycle, "dry_run": True}

    # 4. Run worker
    worker_prompt = build_worker_prompt(cycle, strategy, sorry_before)
    exit_code, worker_output = run_worker(worker_prompt, budget_usd=budget_usd)
    print(f"  Worker finished (exit={exit_code})")

    # 5. Snapshot after
    sorry_after = find_sorry_locations()
    git_diff = git("diff", "--stat", "HEAD~1", check=False)
    log_after = read_file_safe(REPO_DIR / "Aristotle" / "GrothendieckVanishing" / "LOG.md")
    # Extract just the new log entry
    log_entry = log_after[len(log_before):] if log_after.startswith(log_before) else log_after[-2000:]
    print(f"  Sorry count after: {len(sorry_after)}")

    # 6. Run evaluator
    eval_prompt = build_evaluator_prompt(
        cycle, git_diff, log_entry,
        sorry_before, sorry_after,
        history, worker_output,
    )
    evaluation = run_evaluator(eval_prompt)
    print(f"  Evaluation: score={evaluation.get('progress_score')}, {evaluation.get('summary', '')}")

    # 7. Write strategy for next cycle
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    STRATEGY_FILE.write_text(evaluation.get("strategy_for_next_cycle", "Normal operation."))

    # 8. Record history
    record = {
        "cycle": cycle,
        "timestamp": ts,
        "sorry_before": len(sorry_before),
        "sorry_after": len(sorry_after),
        "worker_exit_code": exit_code,
        "evaluation": evaluation,
    }
    append_history(record)

    # 9. Telegram summary
    score = evaluation.get("progress_score", 0)
    score_emoji = {-2: "🔴", -1: "🟠", 0: "⚪", 1: "🟢", 2: "🟢🟢"}
    msg = (
        f"{score_emoji.get(score, '?')} *Cycle {cycle}* "
        f"(sorry: {len(sorry_before)}→{len(sorry_after)})\n"
        f"{evaluation.get('summary', 'no summary')}"
    )
    if stuck_count >= 3:
        msg += f"\n⚠️ Stuck for {stuck_count + (1 if score <= 0 else 0)} cycles"
    send_telegram(msg)

    print(f"  Cycle {cycle} complete.")
    return record


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Autonomous formalization loop")
    parser.add_argument("--loop", action="store_true", help="Run continuously")
    parser.add_argument("--interval", type=int, default=600, help="Seconds between cycles (default: 600)")
    parser.add_argument("--dry-run", action="store_true", help="Show what would happen without running worker")
    parser.add_argument("--budget", type=float, default=5.0, help="Max USD per worker cycle (default: 5.0)")
    args = parser.parse_args()

    lock = FileLock(LOCK_FILE)
    if not lock.acquire():
        print("Another cycle is already running. Exiting.")
        sys.exit(0)

    try:
        if args.loop:
            print(f"Starting continuous loop (interval={args.interval}s)")
            while True:
                try:
                    run_cycle(dry_run=args.dry_run, budget_usd=args.budget)
                except Exception as e:
                    print(f"Cycle failed: {e}", file=sys.stderr)
                    send_telegram(f"❌ Cycle failed: {e}")
                print(f"  Sleeping {args.interval}s until next cycle...")
                time.sleep(args.interval)
        else:
            run_cycle(dry_run=args.dry_run, budget_usd=args.budget)
    finally:
        lock.release()


if __name__ == "__main__":
    main()
