#!/usr/bin/env python3.9
"""
Codex-native autonomous refactor loop for Grothendieck Vanishing.

This replaces the old Claude loop with:
  - repo-local Codex home/config under .refactor-state/codex-home
  - Lean LSP MCP wired to this repository
  - planner / worker / evaluator prompts specialized for remaining unchecked items
  - explicit status + history files for monitoring
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


REPO_DIR = Path(__file__).resolve().parent.parent
STATE_DIR = REPO_DIR / ".refactor-state"
PROMPTS_DIR = REPO_DIR / "scripts" / "prompts"
SETUP_HOME_SCRIPT = REPO_DIR / "scripts" / "setup_codex_refactor_home.sh"

LOCK_FILE = STATE_DIR / "codex_run.lock"
STATUS_FILE = STATE_DIR / "codex_status.json"
HISTORY_FILE = STATE_DIR / "codex_history.jsonl"
STRATEGY_FILE = STATE_DIR / "codex_strategy.md"
CYCLE_FILE = STATE_DIR / "codex_cycle"
TASK_RESULTS_DIR = STATE_DIR / "codex_task_results"
ATTEMPTS_FILE = STATE_DIR / "attempts.md"
REVIEW_TASKS_FILE = STATE_DIR / "review_tasks.md"
PRINCIPLES_FILE = STATE_DIR / "principles.md"

WORKING_BRANCH = "wip/grothendieck-vanishing"
COOLDOWN = 300
PLANNER_TIMEOUT = 1800
WORKER_TIMEOUT = 10800
EVALUATOR_TIMEOUT = 1800
HISTORY_WINDOW = 8

CODEX_BIN = Path(os.environ.get("CODEX_BIN", "/gscratch/amath/vilin/conda/envs/codex/bin/codex"))
CODEX_HOME_ROOT = Path(
    os.environ.get("CODEX_REFACTOR_HOME_ROOT", str(STATE_DIR / "codex-home"))
)

EVALUATOR_SCHEMA = {
    "type": "object",
    "properties": {
        "progress_score": {"type": "integer", "minimum": -2, "maximum": 2},
        "summary": {"type": "string"},
        "principle_violations": {"type": "array", "items": {"type": "string"}},
        "task_addressed": {"type": "boolean"},
        "task_complete": {"type": "boolean"},
        "stuck_on": {"type": "string"},
        "strategy_recommendation": {"type": "string"},
        "attempts_entry": {"type": "string"},
        "completed_task_lines": {"type": "array", "items": {"type": "string"}},
    },
    "required": [
        "progress_score",
        "summary",
        "principle_violations",
        "task_addressed",
        "task_complete",
        "stuck_on",
        "strategy_recommendation",
        "attempts_entry",
        "completed_task_lines",
    ],
}


def ensure_setup() -> None:
    result = subprocess.run(
        [str(SETUP_HOME_SCRIPT)],
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
        timeout=120,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "Codex home setup failed")
    if not CODEX_BIN.exists():
        raise RuntimeError(f"Codex binary not found at {CODEX_BIN}")


def write_status(**payload: object) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    status = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "pid": os.getpid(),
        **payload,
    }
    STATUS_FILE.write_text(json.dumps(status, indent=2, sort_keys=True))


def git(*args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
    )
    if check and result.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {result.stderr[:300]}")
    return result.stdout.strip()


def count_sorrys() -> int:
    import re

    sorry_re = re.compile(r"(?<!\w)sorry(?!\w)")
    count = 0
    for path in (REPO_DIR / "Aristotle" / "GrothendieckVanishing" / "main").glob("*.lean"):
        in_doc = False
        for line in path.read_text().splitlines():
            stripped = line.strip()
            if stripped.startswith("--"):
                continue
            if "/-" in stripped:
                in_doc = True
            if in_doc:
                if "-/" in stripped:
                    in_doc = False
                continue
            if sorry_re.search(stripped):
                count += 1
    return count


def get_cycle_number() -> int:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    n = 0
    if CYCLE_FILE.exists():
        try:
            n = int(CYCLE_FILE.read_text().strip())
        except ValueError:
            n = 0
    n += 1
    CYCLE_FILE.write_text(str(n))
    return n


def append_history(record: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with HISTORY_FILE.open("a") as f:
        f.write(json.dumps(record) + "\n")


def load_history(n: int = HISTORY_WINDOW) -> list[dict]:
    records: list[dict] = []
    for path in [STATE_DIR / "history.jsonl", HISTORY_FILE]:
        if not path.exists():
            continue
        for line in path.read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return records[-n:]


def format_history(history: list[dict]) -> str:
    if not history:
        return "(no previous cycles)"
    out = []
    for item in history:
        ev = item.get("evaluation", {})
        out.append(
            f"- Cycle {item.get('cycle', '?')}: score={ev.get('progress_score', '?')} "
            f"summary={ev.get('summary', 'no summary')}"
        )
    return "\n".join(out)


def read_file_safe(path: Path, max_chars: int = 12000) -> str:
    if not path.exists():
        return ""
    text = path.read_text()
    if len(text) > max_chars:
        return text[:max_chars] + f"\n... [truncated, {len(text)} chars total]"
    return text


def codex_env() -> dict[str, str]:
    env = os.environ.copy()
    env["HOME"] = str(CODEX_HOME_ROOT)
    env["PATH"] = f"/tmp/lake-bin:/tmp/lean4-toolchain/bin:{env.get('PATH', '')}"
    env.setdefault("CODEX_CI", "1")
    return env


def run_codex(
    prompt: str,
    timeout: int,
    output_schema: dict | None = None,
    output_path: Path | None = None,
    model: str | None = None,
) -> tuple[int, str]:
    cmd = [
        str(CODEX_BIN),
        "exec",
        "-C",
        str(REPO_DIR),
        "--color",
        "never",
        "--ephemeral",
        "--dangerously-bypass-approvals-and-sandbox",
    ]
    if model:
        cmd.extend(["-m", model])
    schema_path = None
    if output_schema is not None:
        schema_path = STATE_DIR / "codex_evaluator_schema.json"
        schema_path.write_text(json.dumps(output_schema))
        cmd.extend(["--output-schema", str(schema_path)])
    if output_path is not None:
        cmd.extend(["-o", str(output_path)])
    cmd.append(prompt)
    result = subprocess.run(
        cmd,
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        env=codex_env(),
    )
    last = ""
    if output_path is not None and output_path.exists():
        last = output_path.read_text()
    elif result.stdout:
        last = result.stdout[-12000:]
    return result.returncode, last


def run_planner(cycle: int, history: list[dict]) -> str:
    template = Template((PROMPTS_DIR / "codex_planner.md").read_text())
    prompt = template.safe_substitute(cycle=cycle, history=format_history(history))
    write_status(mode="planner", cycle=cycle)
    exit_code, _ = run_codex(prompt, timeout=PLANNER_TIMEOUT, model="gpt-5.4")
    if exit_code != 0:
        raise RuntimeError(f"Planner failed with exit code {exit_code}")
    strategy = read_file_safe(STRATEGY_FILE)
    if not strategy:
        raise RuntimeError("Planner did not write codex_strategy.md")
    return strategy


def run_worker(cycle: int, strategy: str) -> tuple[int, str]:
    template = Template((PROMPTS_DIR / "codex_worker.md").read_text())
    prompt = template.safe_substitute(
        cycle=cycle,
        strategy=strategy,
        principles=read_file_safe(PRINCIPLES_FILE),
    )
    output_path = STATE_DIR / "codex_worker_last_message.txt"
    write_status(mode="worker", cycle=cycle)
    return run_codex(
        prompt,
        timeout=WORKER_TIMEOUT,
        output_path=output_path,
        model="gpt-5.4",
    )


def default_eval(msg: str) -> dict:
    return {
        "progress_score": 0,
        "summary": msg,
        "principle_violations": [],
        "task_addressed": False,
        "task_complete": False,
        "stuck_on": "",
        "strategy_recommendation": "Pick the next still-unchecked checklist item and keep scope tighter.",
        "attempts_entry": msg,
        "completed_task_lines": [],
    }


def run_evaluator(cycle: int, strategy: str, diff: str, report: str, history: list[dict]) -> dict:
    template = Template((PROMPTS_DIR / "codex_evaluator.md").read_text())
    prompt = template.safe_substitute(
        cycle=cycle,
        principles=read_file_safe(PRINCIPLES_FILE),
        strategy=strategy[:5000],
        diff=diff[:10000] if diff else "(no changes)",
        report=report[:6000] if report else "(no report)",
        history=format_history(history),
    )
    output_path = STATE_DIR / "codex_evaluator_last_message.json"
    write_status(mode="evaluator", cycle=cycle)
    exit_code, output = run_codex(
        prompt,
        timeout=EVALUATOR_TIMEOUT,
        output_schema=EVALUATOR_SCHEMA,
        output_path=output_path,
        model="gpt-5.4-mini",
    )
    if exit_code != 0:
        return default_eval(f"Evaluator failed with exit code {exit_code}")
    try:
        return json.loads(output)
    except json.JSONDecodeError:
        return default_eval("Evaluator returned unparseable JSON")


def apply_gates(sorry_before: int, sorry_after: int) -> None:
    if sorry_after > sorry_before:
        git("checkout", "--", ".", check=False)
        raise RuntimeError(f"Gate failed: sorry count increased ({sorry_before} -> {sorry_after})")

    modified = [line for line in git("diff", "--name-only", "HEAD", check=False).splitlines() if line.endswith(".lean")]
    for path in modified:
        result = subprocess.run(
            ["lake", "env", "lean", path],
            cwd=REPO_DIR,
            capture_output=True,
            text=True,
            check=False,
            timeout=600,
        )
        if result.returncode != 0:
            git("checkout", "--", ".", check=False)
            raise RuntimeError(f"Gate failed: {path} does not compile: {result.stderr[:400]}")


def mark_completed_tasks(lines: list[str]) -> list[str]:
    if not lines:
        return []
    text = REVIEW_TASKS_FILE.read_text()
    changed: list[str] = []
    for line in lines:
        needle = line
        if needle.startswith("- [x]"):
            needle = needle.replace("- [x]", "- [ ]", 1)
        replacement = needle.replace("- [ ]", "- [x]", 1)
        if needle in text:
            text = text.replace(needle, replacement, 1)
            changed.append(needle)
    REVIEW_TASKS_FILE.write_text(text)
    return changed


class FileLock:
    def __init__(self, path: Path):
        self.path = path
        self.fd = None

    def acquire(self) -> bool:
        import fcntl

        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.fd = self.path.open("w")
        try:
            fcntl.flock(self.fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.fd.write(str(os.getpid()))
            self.fd.flush()
            return True
        except OSError:
            self.fd.close()
            self.fd = None
            return False

    def release(self) -> None:
        if self.fd is None:
            return
        import fcntl

        fcntl.flock(self.fd, fcntl.LOCK_UN)
        self.fd.close()
        self.fd = None


def run_cycle(dry_run: bool = False, worker_only: bool = False) -> dict:
    ensure_setup()
    cycle = get_cycle_number()
    history = load_history()
    ts = datetime.now(timezone.utc).isoformat()

    write_status(mode="cycle_start", cycle=cycle, branch=WORKING_BRANCH)
    print(f"Starting Codex refactor cycle {cycle}")

    git("checkout", WORKING_BRANCH, check=False)
    git("pull", "--rebase", "origin", WORKING_BRANCH, check=False)

    sorry_before = count_sorrys()
    strategy = read_file_safe(STRATEGY_FILE) if worker_only else run_planner(cycle, history)

    if dry_run:
        return {"cycle": cycle, "dry_run": True, "strategy": strategy}

    worker_exit, _worker_message = run_worker(cycle, strategy)
    sorry_after = count_sorrys()
    apply_gates(sorry_before, sorry_after)

    diff = git("diff", check=False)
    report = read_file_safe(TASK_RESULTS_DIR / f"cycle_{cycle}.md")
    evaluation = run_evaluator(cycle, strategy, diff, report, history)
    completed = mark_completed_tasks(evaluation.get("completed_task_lines", []))

    entry = evaluation.get("attempts_entry", "").strip()
    if entry:
        with ATTEMPTS_FILE.open("a") as f:
            f.write(f"\nCycle {cycle}: {entry}")

    record = {
        "cycle": cycle,
        "timestamp": ts,
        "worker_exit_code": worker_exit,
        "sorry_before": sorry_before,
        "sorry_after": sorry_after,
        "completed_task_lines": completed,
        "evaluation": evaluation,
    }
    append_history(record)

    if evaluation.get("strategy_recommendation"):
        STRATEGY_FILE.write_text(evaluation["strategy_recommendation"] + "\n")

    if git("diff", "--name-only", check=False):
        git("add", "-A")
        summary = evaluation.get("summary", "codex refactor cycle")
        git("commit", "-m", f"refactor: codex cycle {cycle} — {summary}", check=False)
        git("push", "origin", WORKING_BRANCH, check=False)

    write_status(
        mode="idle",
        cycle=cycle,
        last_summary=evaluation.get("summary", ""),
        completed_task_lines=completed,
    )
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description="Codex refactor loop")
    parser.add_argument("--loop", action="store_true", help="Run continuously")
    parser.add_argument("--interval", type=int, default=COOLDOWN, help="Seconds between cycles")
    parser.add_argument("--dry-run", action="store_true", help="Plan only; do not run the worker")
    parser.add_argument("--worker-only", action="store_true", help="Skip planner and reuse codex_strategy.md")
    args = parser.parse_args()

    lock = FileLock(LOCK_FILE)
    if not lock.acquire():
        raise SystemExit("Codex refactor loop is already running")

    try:
        if args.loop:
            while True:
                try:
                    run_cycle(dry_run=args.dry_run, worker_only=args.worker_only)
                except Exception as exc:
                    write_status(mode="error", error=str(exc))
                    print(f"Cycle failed: {exc}", file=sys.stderr)
                time.sleep(args.interval)
        else:
            run_cycle(dry_run=args.dry_run, worker_only=args.worker_only)
    finally:
        lock.release()


if __name__ == "__main__":
    TASK_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    main()
