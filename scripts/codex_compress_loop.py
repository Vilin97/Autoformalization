#!/usr/bin/env python3.9
"""
Codex-native autonomous compress loop for Grothendieck Vanishing.

Modeled on `codex_refactor_loop.py` but tuned for a different objective:
COMPRESS the existing 8127-line tree below 5000 raw LOC, by deleting unused
declarations, factoring repeated patterns into single helpers, golfing long
proofs, and reverting the over-applied `(F : Presheaf) (hF : F.IsSheaf)`
idiom back to `(F : Sheaf X _)`.

Per-cycle gates:
  - 0 sorry / axiom / admit
  - `lake env lean <path>` for every modified Lean file
  - `lake build` for any add/delete/rename of project Lean files
  - **NORMALIZED LOC strictly decreased** (the compress-loop-specific gate)

Stop condition: raw `wc -l` of `Aristotle/GrothendieckVanishing/main/*.lean`
drops below 5000.
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

import normalized_loc  # local module: scripts/normalized_loc.py


REPO_DIR = Path(__file__).resolve().parent.parent
STATE_DIR = REPO_DIR / ".compress-state"
PROMPTS_DIR = REPO_DIR / "scripts" / "prompts"
SCRIPTS_DIR = REPO_DIR / "scripts"
SETUP_HOME_SCRIPT = REPO_DIR / "scripts" / "setup_codex_compress_home.sh"

LOCK_FILE = STATE_DIR / "codex_run.lock"
STATUS_FILE = STATE_DIR / "codex_status.json"
HISTORY_FILE = STATE_DIR / "codex_history.jsonl"
STRATEGY_FILE = STATE_DIR / "compress_strategy.md"
CYCLE_FILE = STATE_DIR / "codex_cycle"
TASK_RESULTS_DIR = STATE_DIR / "codex_task_results"
ATTEMPTS_FILE = STATE_DIR / "attempts.md"
TASKS_FILE = STATE_DIR / "compress_tasks.md"
PRINCIPLES_FILE = STATE_DIR / "principles.md"

WORKING_BRANCH = "wip/grothendieck-vanishing"
COOLDOWN = 300
IDLE_COOLDOWN = 3600
IDLE_SKIP_THRESHOLD = 3
PLANNER_TIMEOUT = 1800
WORKER_TIMEOUT = 10800
EVALUATOR_TIMEOUT = 1800
AUDITOR_TIMEOUT = 1800
GATE_REPAIR_TIMEOUT = 3600
HISTORY_WINDOW = 8
RAW_LOC_STOP_TARGET = 5000
DEFAULT_MODEL = os.environ.get("CODEX_COMPRESS_MODEL", "gpt-5.5")
DEFAULT_REASONING_EFFORT = os.environ.get("CODEX_COMPRESS_REASONING_EFFORT", "xhigh")
EVALUATOR_MODEL = os.environ.get("CODEX_COMPRESS_EVALUATOR_MODEL", "claude-opus-4-7")
AUDITOR_MODEL = os.environ.get("CODEX_COMPRESS_AUDITOR_MODEL", EVALUATOR_MODEL)

CODEX_BIN = Path(os.environ.get("CODEX_BIN", "/gscratch/amath/vilin/conda/envs/codex/bin/codex"))
CODEX_HOME_ROOT = Path(
    os.environ.get("CODEX_COMPRESS_HOME_ROOT", str(STATE_DIR / "codex-home"))
)
CLAUDE_BIN = Path(os.environ.get("CLAUDE_BIN", "/mmfs1/home/vilin/.local/bin/claude"))

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

AUDITOR_SCHEMA = {
    "type": "object",
    "additionalProperties": False,
    "properties": {
        "loop_done": {"type": "boolean"},
        "added_lines": {"type": "array", "items": {"type": "string"}},
        "audit_summary": {"type": "string"},
        "principle_violations": {"type": "array", "items": {"type": "string"}},
    },
    "required": ["loop_done", "added_lines", "audit_summary", "principle_violations"],
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
    if not SETUP_HOME_SCRIPT.exists():
        raise RuntimeError(f"Setup script not found at {SETUP_HOME_SCRIPT}")
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
    if HISTORY_FILE.exists():
        for line in HISTORY_FILE.read_text().splitlines():
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
        delta = item.get("loc_delta")
        delta_str = f" loc_delta={delta:+d}" if isinstance(delta, int) else ""
        out.append(
            f"- Cycle {item.get('cycle', '?')}: score={ev.get('progress_score', '?')}"
            f"{delta_str} summary={ev.get('summary', 'no summary')}"
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
    env["PATH"] = (
        f"/gscratch/amath/vilin/conda/envs/codex/bin:/tmp/lake-bin:"
        f"/tmp/lean4-toolchain/bin:{env.get('PATH', '')}"
    )
    env.setdefault("CODEX_CI", "1")
    return env


def run_claude(
    prompt: str,
    timeout: int,
    schema: dict | None = None,
    model: str = EVALUATOR_MODEL,
    append_system_prompt: str | None = None,
) -> tuple[int, dict | str]:
    """Invoke Claude Code in headless print mode."""
    if not CLAUDE_BIN.exists():
        raise RuntimeError(f"Claude binary not found at {CLAUDE_BIN}")
    cmd = [
        str(CLAUDE_BIN),
        "-p",
        prompt,
        "--output-format",
        "json",
        "--model",
        model,
        "--permission-mode",
        "bypassPermissions",
        "--add-dir",
        str(REPO_DIR),
    ]
    if schema is not None:
        cmd.extend(["--json-schema", json.dumps(schema)])
    if append_system_prompt:
        cmd.extend(["--append-system-prompt", append_system_prompt])
    env = os.environ.copy()
    env["PATH"] = f"/tmp/lake-bin:/tmp/lean4-toolchain/bin:{env.get('PATH', '')}"
    result = subprocess.run(
        cmd,
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        env=env,
    )
    if result.returncode != 0:
        return result.returncode, (result.stderr or result.stdout or "")[-4000:]
    try:
        payload = json.loads(result.stdout)
    except json.JSONDecodeError:
        return 1, result.stdout[-4000:]
    if payload.get("is_error"):
        return 1, payload.get("result", "") or payload.get("error", "")
    if schema is not None:
        structured = payload.get("structured_output")
        if structured is None:
            return 1, payload.get("result", "") or "no structured_output"
        return 0, structured
    return 0, payload.get("result", "")


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


def run_audit(cycle: int) -> None:
    """Refresh `.compress-state/audit.md` with fresh data the planner reads.
    Non-fatal: the planner still runs even if the audit fails."""
    write_status(mode="audit", cycle=cycle)
    try:
        subprocess.run(
            ["python3.9", str(SCRIPTS_DIR / "compress_audit.py"), str(cycle)],
            cwd=REPO_DIR,
            timeout=900,
            check=False,
        )
    except subprocess.TimeoutExpired:
        print("Audit timed out; planner will use stale audit.md", file=sys.stderr)


def run_planner(cycle: int, history: list[dict]) -> str:
    template = Template((PROMPTS_DIR / "compress_planner.md").read_text())
    audit = read_file_safe(STATE_DIR / "audit.md") or "(audit unavailable)"
    prompt = template.safe_substitute(
        cycle=cycle, history=format_history(history), audit=audit[:18000]
    )
    write_status(mode="planner", cycle=cycle)
    exit_code, _ = run_codex(prompt, timeout=PLANNER_TIMEOUT, model=DEFAULT_MODEL)
    if exit_code != 0:
        raise RuntimeError(f"Planner failed with exit code {exit_code}")
    strategy = read_file_safe(STRATEGY_FILE)
    if not strategy:
        raise RuntimeError("Planner did not write compress_strategy.md")
    return strategy


def run_worker(cycle: int, strategy: str) -> tuple[int, str]:
    template = Template((PROMPTS_DIR / "compress_worker.md").read_text())
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
    template = Template((PROMPTS_DIR / "compress_gate_repair.md").read_text())
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
    template = Template((PROMPTS_DIR / "compress_evaluator.md").read_text())
    prompt = template.safe_substitute(
        cycle=cycle,
        principles=read_file_safe(PRINCIPLES_FILE),
        strategy=strategy[:8000],
        diff=diff[:20000] if diff else "(no changes)",
        report=report[:8000] if report else "(no report)",
        history=format_history(history),
    )
    output_path = STATE_DIR / "codex_evaluator_last_message.json"
    write_status(mode="evaluator", cycle=cycle, evaluator_model=EVALUATOR_MODEL)
    exit_code, payload = run_claude(
        prompt,
        timeout=EVALUATOR_TIMEOUT,
        schema=EVALUATOR_SCHEMA,
        model=EVALUATOR_MODEL,
    )
    if exit_code != 0 or not isinstance(payload, dict):
        detail = payload if isinstance(payload, str) else "unknown"
        return default_eval(f"Evaluator failed (exit {exit_code}): {detail[:300]}")
    output_path.write_text(json.dumps(payload, indent=2))
    return payload


def run_auditor(cycle: int, history: list[dict]) -> dict:
    template = Template((PROMPTS_DIR / "compress_auditor.md").read_text())
    prompt = template.safe_substitute(
        cycle=cycle,
        history=format_history(history),
    )
    write_status(mode="auditor", cycle=cycle, auditor_model=AUDITOR_MODEL)
    exit_code, payload = run_claude(
        prompt,
        timeout=AUDITOR_TIMEOUT,
        schema=AUDITOR_SCHEMA,
        model=AUDITOR_MODEL,
    )
    if exit_code != 0 or not isinstance(payload, dict):
        detail = payload if isinstance(payload, str) else "unknown"
        return {
            "loop_done": False,
            "added_lines": [],
            "audit_summary": f"Auditor failed (exit {exit_code}): {str(detail)[:300]}",
            "principle_violations": [],
        }
    (STATE_DIR / "codex_auditor_last_message.json").write_text(json.dumps(payload, indent=2))
    return payload


def has_unchecked_or_wip_items() -> bool:
    if not TASKS_FILE.exists():
        return False
    for line in TASKS_FILE.read_text().splitlines():
        stripped = line.lstrip()
        if stripped.startswith("- [ ]") or stripped.startswith("- [>]"):
            return True
    return False


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
    lines.append("- python3.9 scripts/normalized_loc.py  (must be < cycle-start baseline)")
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


def check_gates(sorry_before: int, sorry_after: int, loc_before: int) -> GateFailure | None:
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

    # Compress-loop-specific gate: normalized LOC must strictly decrease.
    loc_after = normalized_loc.total_normalized_count()
    if loc_after >= loc_before:
        return GateFailure(
            kind="loc_not_decreased",
            message=f"normalized LOC did not decrease ({loc_before} -> {loc_after})",
            details=("The compress loop's commit-level gate requires the diff to "
                     "strictly reduce normalized LOC. Comment / blank-line removal "
                     "and tactic stacking do not count (the metric ignores them)."),
            command="python3.9 scripts/normalized_loc.py",
            plan=plan,
        )
    return None


def _complete_if_for(task_line: str, text: str) -> str | None:
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.rstrip() != task_line.rstrip():
            continue
        j = i + 1
        while j < len(lines) and lines[j].strip() == "":
            j += 1
        if j < len(lines):
            stripped = lines[j].lstrip()
            if stripped.startswith("COMPLETE_IF:"):
                return stripped[len("COMPLETE_IF:"):].strip()
        return None
    return None


def _complete_if_passes(shell_expr: str) -> bool:
    result = subprocess.run(
        ["bash", "-c", shell_expr],
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
        timeout=120,
    )
    return result.returncode == 0


def mark_completed_tasks(lines: list[str]) -> tuple[list[str], list[tuple[str, str]]]:
    if not lines:
        return [], []
    text = TASKS_FILE.read_text()
    flipped: list[str] = []
    rejected: list[tuple[str, str]] = []
    for line in lines:
        needle_candidates = [line]
        for prefix in ("- [x]", "- [ ]", "- [>]"):
            if line.lstrip().startswith(prefix):
                suffix = line.lstrip()[len(prefix):]
                indent = line[: len(line) - len(line.lstrip())]
                for alt in ("- [ ]", "- [>]"):
                    cand = f"{indent}{alt}{suffix}"
                    if cand not in needle_candidates:
                        needle_candidates.append(cand)
                break
        matched = None
        for cand in needle_candidates:
            if cand in text:
                matched = cand
                break
        if matched is None:
            rejected.append((line, "task line not found in compress_tasks.md"))
            continue
        criterion = _complete_if_for(matched, text)
        if criterion is not None and not _complete_if_passes(criterion):
            rejected.append((matched, f"COMPLETE_IF failed: {criterion}"))
            continue
        replacement = matched
        for prefix in ("- [ ]", "- [>]"):
            if prefix in replacement:
                replacement = replacement.replace(prefix, "- [x]", 1)
                break
        text = text.replace(matched, replacement, 1)
        flipped.append(matched)
    TASKS_FILE.write_text(text)
    return flipped, rejected


def promote_to_wip(task_line: str) -> bool:
    if not task_line:
        return False
    text = TASKS_FILE.read_text()
    if task_line not in text:
        return False
    if "- [>]" in task_line:
        return False
    upgraded = task_line.replace("- [ ]", "- [>]", 1)
    if upgraded == task_line:
        return False
    TASKS_FILE.write_text(text.replace(task_line, upgraded, 1))
    return True


def recent_cycles_are_idle(history: list[dict], n: int = IDLE_SKIP_THRESHOLD) -> bool:
    if len(history) < n:
        return False
    recent = history[-n:]
    for record in recent:
        if record.get("completed_task_lines"):
            return False
        ev = record.get("evaluation", {})
        if ev.get("task_addressed") and ev.get("progress_score", 0) > 0:
            return False
    return True


def raw_loc_total() -> int:
    return normalized_loc.total_raw_loc()


def stop_condition_met() -> bool:
    return raw_loc_total() < RAW_LOC_STOP_TARGET


def record_gate_failure(
    cycle: int,
    ts: str,
    worker_exit: int,
    sorry_before: int,
    sorry_after: int,
    failure: GateFailure,
    repair_attempted: bool,
    repair_exit_code: int | None,
    loc_before: int,
    loc_after: int,
) -> dict:
    summary_prefix = "Gate failed after auto-repair" if repair_attempted else "Gate failed"
    summary = f"{summary_prefix}: {gate_failure_text(failure)}"
    recommendation = (
        "Repair the previous cycle's mechanical gate failure before attempting new compression work.\n"
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
        "loc_before": loc_before,
        "loc_after": loc_after,
        "loc_delta": loc_after - loc_before,
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
    print(f"Starting Codex compress cycle {cycle}")

    git("checkout", WORKING_BRANCH, check=False)
    git("pull", "--rebase", "origin", WORKING_BRANCH, check=False)

    # Stop condition: raw LOC < 5000.
    raw_loc = raw_loc_total()
    if raw_loc < RAW_LOC_STOP_TARGET:
        msg = f"Stop condition met: raw LOC = {raw_loc} < {RAW_LOC_STOP_TARGET}."
        print(msg)
        write_status(mode="loop_done", cycle=cycle, last_summary=msg, raw_loc=raw_loc)
        record = {
            "cycle": cycle,
            "timestamp": ts,
            "raw_loc": raw_loc,
            "loop_done": True,
            "evaluation": default_eval(msg),
            "completed_task_lines": [],
        }
        append_history(record)
        send_telegram(f"🟢 Compress loop done: raw LOC = {raw_loc} < {RAW_LOC_STOP_TARGET}")
        return record

    # If checklist is empty, run the auditor (which re-runs the comprehensive scan).
    if not has_unchecked_or_wip_items():
        audit = run_auditor(cycle, history)
        if audit.get("loop_done"):
            write_status(
                mode="idle_done",
                cycle=cycle,
                last_summary=audit.get("audit_summary", ""),
                auditor_result=audit,
            )
            record = {
                "cycle": cycle,
                "timestamp": ts,
                "auditor": audit,
                "evaluation": default_eval(audit.get("audit_summary") or "auditor says done"),
                "completed_task_lines": [],
            }
            append_history(record)
            return record
        added = audit.get("added_lines") or []
        print(f"Auditor refreshed checklist; {len(added)} new lines.")

    sorry_before = count_sorrys()
    loc_before = normalized_loc.total_normalized_count()
    print(f"  cycle-start: raw {raw_loc} LOC, normalized {loc_before}")

    if not worker_only:
        run_audit(cycle)

    strategy = read_file_safe(STRATEGY_FILE) if worker_only else run_planner(cycle, history)

    promoted: list[str] = []
    for line in strategy.splitlines():
        stripped = line.strip()
        if stripped.startswith("- [ ]") and promote_to_wip(stripped):
            promoted.append(stripped)
    if promoted:
        print(f"Promoted {len(promoted)} checklist items to - [>] WIP.")

    if dry_run:
        return {"cycle": cycle, "dry_run": True, "strategy": strategy}

    worker_exit, _worker_message = run_worker(cycle, strategy)
    sorry_after = count_sorrys()
    loc_after = normalized_loc.total_normalized_count()
    gate_repair_attempted = False
    gate_repair_exit_code = None
    gate_failure = check_gates(sorry_before, sorry_after, loc_before)
    if gate_failure is not None:
        gate_repair_attempted = True
        gate_repair_exit_code, _gate_repair_message = run_gate_repair(cycle, strategy, gate_failure, history)
        sorry_after = count_sorrys()
        loc_after = normalized_loc.total_normalized_count()
        gate_failure = check_gates(sorry_before, sorry_after, loc_before)
        if gate_failure is not None:
            git("checkout", "--", ".", check=False)
            loc_after = normalized_loc.total_normalized_count()
            record_gate_failure(
                cycle=cycle,
                ts=ts,
                worker_exit=worker_exit,
                sorry_before=sorry_before,
                sorry_after=sorry_after,
                failure=gate_failure,
                repair_attempted=gate_repair_attempted,
                repair_exit_code=gate_repair_exit_code,
                loc_before=loc_before,
                loc_after=loc_after,
            )
            raise RuntimeError(f"Gate failed after auto-repair: {gate_failure_text(gate_failure)}")

    diff = git("diff", check=False)
    report = read_file_safe(TASK_RESULTS_DIR / f"cycle_{cycle}.md")
    evaluation = run_evaluator(cycle, strategy, diff, report, history)
    completed, rejected = mark_completed_tasks(evaluation.get("completed_task_lines", []))
    if rejected:
        with ATTEMPTS_FILE.open("a") as f:
            for line, reason in rejected:
                f.write(f"\nCycle {cycle}: rejected complete ({reason}): {line.strip()}")

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
        "loc_before": loc_before,
        "loc_after": loc_after,
        "loc_delta": loc_after - loc_before,
        "raw_loc_after": raw_loc_total(),
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
        summary = evaluation.get("summary", "codex compress cycle")
        delta = loc_after - loc_before
        git("commit", "-m", f"compress: codex cycle {cycle} ({delta:+d} norm LOC) — {summary}", check=False)
        git("push", "origin", WORKING_BRANCH, check=False)

    score = evaluation.get("progress_score", 0)
    emoji = {-2: "🔴", -1: "🟠", 0: "⚪", 1: "🟢", 2: "🟢🟢"}.get(score, "⚪")
    delta = loc_after - loc_before
    raw_after = record["raw_loc_after"]
    msg = (
        f"{emoji} *Codex Compress Cycle {cycle}*\n"
        f"{evaluation.get('summary', 'no summary')}\n"
        f"normLOC: {loc_before} → {loc_after} ({delta:+d}); "
        f"rawLOC: {raw_after} (target <{RAW_LOC_STOP_TARGET})"
    )
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
        loc_before=loc_before,
        loc_after=loc_after,
        loc_delta=delta,
        raw_loc=raw_after,
        completed_task_lines=completed,
    )
    return record


def main() -> None:
    load_repo_env()
    parser = argparse.ArgumentParser(description="Codex compress loop")
    parser.add_argument("--loop", action="store_true", help="Run continuously")
    parser.add_argument("--interval", type=int, default=COOLDOWN, help="Seconds between cycles")
    parser.add_argument("--dry-run", action="store_true", help="Plan only; do not run the worker")
    parser.add_argument("--worker-only", action="store_true", help="Skip planner and reuse compress_strategy.md")
    args = parser.parse_args()

    lock = FileLock(LOCK_FILE)
    if not lock.acquire():
        raise SystemExit("Codex compress loop is already running")

    try:
        if args.loop:
            raw_now = raw_loc_total()
            norm_now = normalized_loc.total_normalized_count()
            send_telegram(
                f"🚀 Compress loop started\n"
                f"rawLOC: {raw_now} (target <{RAW_LOC_STOP_TARGET})\n"
                f"normLOC: {norm_now}"
            )
            while True:
                if stop_condition_met():
                    msg = f"Stop condition met: raw LOC < {RAW_LOC_STOP_TARGET}. Exiting --loop."
                    print(msg)
                    write_status(mode="loop_done", last_summary=msg)
                    send_telegram(f"🟢 Compress loop exiting: {msg}")
                    break
                try:
                    record = run_cycle(dry_run=args.dry_run, worker_only=args.worker_only)
                    if record.get("loop_done"):
                        break
                except subprocess.TimeoutExpired:
                    write_status(mode="error", error="Cycle timed out")
                    print("Cycle timed out", file=sys.stderr)
                    send_telegram("⏰ Codex compress cycle timed out")
                    record = None
                except Exception as exc:
                    write_status(mode="error", error=str(exc))
                    print(f"Cycle failed: {exc}", file=sys.stderr)
                    send_telegram(f"❌ Codex compress cycle failed: {exc}")
                    record = None
                history = load_history()
                sleep_seconds = args.interval
                if recent_cycles_are_idle(history):
                    sleep_seconds = max(args.interval, IDLE_COOLDOWN)
                    print(
                        f"Idle backoff: last {IDLE_SKIP_THRESHOLD} cycles produced no "
                        f"progress; sleeping {sleep_seconds}s.",
                        file=sys.stderr,
                    )
                time.sleep(sleep_seconds)
        else:
            run_cycle(dry_run=args.dry_run, worker_only=args.worker_only)
    finally:
        lock.release()


if __name__ == "__main__":
    TASK_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    main()
