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
from dataclasses import dataclass
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
GATE_REPAIR_TIMEOUT = 3600
HISTORY_WINDOW = 8
DEFAULT_MODEL = os.environ.get("CODEX_REFACTOR_MODEL", "gpt-5.4")
DEFAULT_REASONING_EFFORT = os.environ.get("CODEX_REFACTOR_REASONING_EFFORT", "xhigh")

CODEX_BIN = Path(os.environ.get("CODEX_BIN", "/gscratch/amath/vilin/conda/envs/codex/bin/codex"))
CODEX_HOME_ROOT = Path(
    os.environ.get("CODEX_REFACTOR_HOME_ROOT", str(STATE_DIR / "codex-home"))
)

EVALUATOR_SCHEMA = {
    "type": "object",
    "additionalProperties": False,
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


@dataclass
class GatePlan:
    compile_targets: list[str]
    requires_build: bool
    checked_paths: list[str]
    skipped_paths: list[str]


@dataclass
class GateFailure:
    kind: str
    message: str
    details: str
    command: str
    plan: GatePlan


def load_repo_env() -> None:
    env_path = REPO_DIR / ".env"
    if not env_path.exists():
        return
    for line in env_path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        if key and key not in os.environ:
            os.environ[key] = value.strip()


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
    reasoning_effort: str | None = DEFAULT_REASONING_EFFORT,
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
    if reasoning_effort:
        cmd.extend(["-c", f'model_reasoning_effort="{reasoning_effort}"'])
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
    exit_code, _ = run_codex(prompt, timeout=PLANNER_TIMEOUT, model=DEFAULT_MODEL)
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
        model=DEFAULT_MODEL,
    )


def run_gate_repair(cycle: int, strategy: str, failure: GateFailure, history: list[dict]) -> tuple[int, str]:
    template = Template((PROMPTS_DIR / "codex_gate_repair.md").read_text())
    prompt = template.safe_substitute(
        cycle=cycle,
        strategy=strategy[:6000],
        principles=read_file_safe(PRINCIPLES_FILE),
        history=format_history(history),
        gate_failure=format_gate_failure(failure),
        gate_checks=format_gate_plan(failure.plan),
        diff=(git("diff", check=False) or "(no changes)")[:10000],
    )
    output_path = STATE_DIR / "codex_gate_repair_last_message.txt"
    write_status(mode="gate_repair", cycle=cycle, gate_failure=failure.message)
    return run_codex(
        prompt,
        timeout=GATE_REPAIR_TIMEOUT,
        output_path=output_path,
        model=DEFAULT_MODEL,
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
        model=DEFAULT_MODEL,
    )
    if exit_code != 0:
        return default_eval(f"Evaluator failed with exit code {exit_code}")
    try:
        return json.loads(output)
    except json.JSONDecodeError:
        return default_eval("Evaluator returned unparseable JSON")


def send_telegram(message: str) -> None:
    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "398863010")
    if not token:
        return
    try:
        result = subprocess.run(
            [
                "curl",
                "-s",
                "-X",
                "POST",
                f"https://api.telegram.org/bot{token}/sendMessage",
                "-d",
                f"chat_id={chat_id}",
                "--data-urlencode",
                f"text={message}",
            ],
            capture_output=True,
            text=True,
            check=False,
            timeout=10,
        )
        if '"ok":false' in (result.stdout or ""):
            print(f"Telegram error: {result.stdout[:200]}", file=sys.stderr)
    except Exception as exc:
        print(f"Telegram send failed: {exc}", file=sys.stderr)


def is_gate_checked_lean_path(path: str) -> bool:
    return path == "Aristotle.lean" or path.startswith("Aristotle/")


def summarize_subprocess_output(result: subprocess.CompletedProcess[str], limit: int = 600) -> str:
    text = (result.stderr or result.stdout or "").strip()
    if not text:
        return "(no stderr or stdout)"
    return text[:limit]


def parse_diff_name_status() -> list[tuple[str, list[str]]]:
    result = subprocess.run(
        ["git", "diff", "--name-status", "-z", "HEAD"],
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(f"git diff --name-status failed: {result.stderr[:300]}")
    tokens = result.stdout.split("\0")
    if tokens and tokens[-1] == "":
        tokens.pop()
    entries: list[tuple[str, list[str]]] = []
    i = 0
    while i < len(tokens):
        status = tokens[i]
        i += 1
        code = status[:1]
        if code in {"R", "C"}:
            if i + 1 >= len(tokens):
                break
            entries.append((code, [tokens[i], tokens[i + 1]]))
            i += 2
        else:
            if i >= len(tokens):
                break
            entries.append((code, [tokens[i]]))
            i += 1
    return entries


def plan_gate_checks() -> GatePlan:
    compile_targets: list[str] = []
    checked_paths: list[str] = []
    skipped_paths: list[str] = []
    requires_build = False

    for code, paths in parse_diff_name_status():
        lean_paths = [path for path in paths if path.endswith(".lean")]
        if not lean_paths:
            continue
        gated_paths = [path for path in lean_paths if is_gate_checked_lean_path(path)]
        skipped_paths.extend(path for path in lean_paths if path not in gated_paths)
        if not gated_paths:
            continue

        checked_paths.extend(gated_paths)
        if code in {"A", "D", "R", "C", "T", "U"}:
            requires_build = True

        if code in {"R", "C"}:
            target = paths[-1]
            if target.endswith(".lean") and is_gate_checked_lean_path(target) and (REPO_DIR / target).exists():
                compile_targets.append(target)
            continue

        target = gated_paths[0]
        if code == "D":
            continue
        if (REPO_DIR / target).exists():
            compile_targets.append(target)

    return GatePlan(
        compile_targets=list(dict.fromkeys(compile_targets)),
        requires_build=requires_build,
        checked_paths=list(dict.fromkeys(checked_paths)),
        skipped_paths=list(dict.fromkeys(skipped_paths)),
    )


def format_gate_plan(plan: GatePlan) -> str:
    lines: list[str] = []
    if plan.compile_targets:
        lines.append("Gate compile commands:")
        lines.extend(f"- lake env lean {path}" for path in plan.compile_targets)
    if plan.requires_build:
        lines.append("- lake build")
    if plan.skipped_paths:
        lines.append("Skipped non-library Lean paths:")
        lines.extend(f"- {path}" for path in plan.skipped_paths[:8])
    if not lines:
        lines.append("- No project Lean files changed.")
    return "\n".join(lines)


def format_gate_failure(failure: GateFailure) -> str:
    lines = [
        f"Kind: {failure.kind}",
        f"Summary: {failure.message}",
        f"Command: {failure.command}",
        "Details:",
        failure.details,
        "",
        format_gate_plan(failure.plan),
    ]
    return "\n".join(lines)


def gate_failure_text(failure: GateFailure) -> str:
    details = failure.details.strip()
    if details and details != "(no stderr or stdout)":
        return f"{failure.message}: {details}"
    return failure.message


def check_gates(sorry_before: int, sorry_after: int) -> GateFailure | None:
    plan = plan_gate_checks()
    if sorry_after > sorry_before:
        return GateFailure(
            kind="sorry_count",
            message=f"sorry count increased ({sorry_before} -> {sorry_after})",
            details="The project must stay at 0 sorrys after every cycle.",
            command="count_sorrys",
            plan=plan,
        )

    for path in plan.compile_targets:
        result = subprocess.run(
            ["lake", "env", "lean", path],
            cwd=REPO_DIR,
            capture_output=True,
            text=True,
            check=False,
            timeout=600,
        )
        if result.returncode != 0:
            return GateFailure(
                kind="compile",
                message=f"{path} does not compile",
                details=summarize_subprocess_output(result),
                command=f"lake env lean {path}",
                plan=plan,
            )

    if plan.requires_build:
        result = subprocess.run(
            ["lake", "build"],
            cwd=REPO_DIR,
            capture_output=True,
            text=True,
            check=False,
            timeout=1800,
        )
        if result.returncode != 0:
            return GateFailure(
                kind="build",
                message="lake build failed after project Lean file add/delete/rename",
                details=summarize_subprocess_output(result, limit=800),
                command="lake build",
                plan=plan,
            )
    return None


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


def record_gate_failure(
    cycle: int,
    ts: str,
    worker_exit: int,
    sorry_before: int,
    sorry_after: int,
    failure: GateFailure,
    repair_attempted: bool,
    repair_exit_code: int | None,
) -> dict:
    summary_prefix = "Gate failed after auto-repair" if repair_attempted else "Gate failed"
    summary = f"{summary_prefix}: {gate_failure_text(failure)}"
    recommendation = (
        "Repair the previous cycle's mechanical gate failure before attempting new checklist work.\n"
        f"{format_gate_plan(failure.plan)}"
    )
    evaluation = default_eval(summary)
    evaluation["progress_score"] = -2
    evaluation["summary"] = summary
    evaluation["principle_violations"] = ["mechanical gate failed"]
    evaluation["task_addressed"] = True
    evaluation["stuck_on"] = failure.message
    evaluation["strategy_recommendation"] = recommendation
    evaluation["attempts_entry"] = (
        f"{summary_prefix.lower()}: {failure.message} ({failure.command})"
    )
    with ATTEMPTS_FILE.open("a") as f:
        f.write(f"\nCycle {cycle}: {evaluation['attempts_entry']}")
    STRATEGY_FILE.write_text(recommendation + "\n")
    record = {
        "cycle": cycle,
        "timestamp": ts,
        "worker_exit_code": worker_exit,
        "sorry_before": sorry_before,
        "sorry_after": sorry_after,
        "completed_task_lines": [],
        "gate_failure": {
            "kind": failure.kind,
            "message": failure.message,
            "details": failure.details,
            "command": failure.command,
            "compile_targets": failure.plan.compile_targets,
            "requires_build": failure.plan.requires_build,
            "skipped_paths": failure.plan.skipped_paths,
        },
        "gate_repair_attempted": repair_attempted,
        "gate_repair_exit_code": repair_exit_code,
        "evaluation": evaluation,
    }
    append_history(record)
    return record


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
    gate_repair_attempted = False
    gate_repair_exit_code = None
    gate_failure = check_gates(sorry_before, sorry_after)
    if gate_failure is not None:
        gate_repair_attempted = True
        gate_repair_exit_code, _gate_repair_message = run_gate_repair(cycle, strategy, gate_failure, history)
        sorry_after = count_sorrys()
        gate_failure = check_gates(sorry_before, sorry_after)
        if gate_failure is not None:
            git("checkout", "--", ".", check=False)
            record_gate_failure(
                cycle=cycle,
                ts=ts,
                worker_exit=worker_exit,
                sorry_before=sorry_before,
                sorry_after=sorry_after,
                failure=gate_failure,
                repair_attempted=gate_repair_attempted,
                repair_exit_code=gate_repair_exit_code,
            )
            raise RuntimeError(f"Gate failed after auto-repair: {gate_failure_text(gate_failure)}")

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
        "gate_repair_attempted": gate_repair_attempted,
        "gate_repair_exit_code": gate_repair_exit_code,
        "evaluation": evaluation,
    }
    append_history(record)

    if evaluation.get("strategy_recommendation"):
        STRATEGY_FILE.write_text(evaluation["strategy_recommendation"] + "\n")

    evaluator_ok = not str(evaluation.get("summary", "")).startswith("Evaluator failed")
    if evaluator_ok and git("diff", "--name-only", check=False):
        git("add", "-A")
        summary = evaluation.get("summary", "codex refactor cycle")
        git("commit", "-m", f"refactor: codex cycle {cycle} — {summary}", check=False)
        git("push", "origin", WORKING_BRANCH, check=False)

    score = evaluation.get("progress_score", 0)
    emoji = {-2: "🔴", -1: "🟠", 0: "⚪", 1: "🟢", 2: "🟢🟢"}.get(score, "⚪")
    msg = f"{emoji} *Codex Refactor Cycle {cycle}*\n{evaluation.get('summary', 'no summary')}"
    violations = evaluation.get("principle_violations", [])
    if violations:
        msg += f"\n⚠️ Violations: {', '.join(violations[:3])}"
    if completed:
        msg += f"\n✅ Completed: {', '.join(completed[:3])}"
    send_telegram(msg)

    write_status(
        mode="idle",
        cycle=cycle,
        last_summary=evaluation.get("summary", ""),
        completed_task_lines=completed,
    )
    return record


def main() -> None:
    load_repo_env()
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
                except subprocess.TimeoutExpired:
                    write_status(mode="error", error="Cycle timed out")
                    print("Cycle timed out", file=sys.stderr)
                    send_telegram("⏰ Codex refactor cycle timed out")
                except Exception as exc:
                    write_status(mode="error", error=str(exc))
                    print(f"Cycle failed: {exc}", file=sys.stderr)
                    send_telegram(f"❌ Codex refactor cycle failed: {exc}")
                time.sleep(args.interval)
        else:
            run_cycle(dry_run=args.dry_run, worker_only=args.worker_only)
    finally:
        lock.release()


if __name__ == "__main__":
    TASK_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    main()
