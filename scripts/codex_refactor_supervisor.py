#!/usr/bin/env python3.9
"""
Periodic supervisor for the Codex refactor loop.

Purpose:
  - audit actual progress against the checklist
  - correct mistaken checkmarks
  - refresh prompts to keep focus on hard remaining items
  - optionally stop and restart the worker loop after the audit
"""

from __future__ import annotations

import argparse
import json
import os
import signal
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
WORKER_LOOP_SCRIPT = REPO_DIR / "scripts" / "run_codex_refactor_loop.sh"

SUPERVISOR_LOCK = STATE_DIR / "codex_supervisor.lock"
SUPERVISOR_STATUS = STATE_DIR / "codex_supervisor_status.json"
SUPERVISOR_HISTORY = STATE_DIR / "codex_supervisor_history.jsonl"
SUPERVISOR_REPORTS = STATE_DIR / "codex_supervisor_reports"

WORKER_LOCK = STATE_DIR / "codex_run.lock"
WORKER_STATUS = STATE_DIR / "codex_status.json"

CODEX_HOME_ROOT = Path(
    os.environ.get("CODEX_REFACTOR_HOME_ROOT", str(STATE_DIR / "codex-home"))
)
CODEX_BIN = Path(os.environ.get("CODEX_BIN", "/gscratch/amath/vilin/conda/envs/codex/bin/codex"))
COOLDOWN = 12 * 60 * 60
SUPERVISOR_TIMEOUT = 3 * 60 * 60
DEFAULT_MODEL = os.environ.get("CODEX_REFACTOR_MODEL", "gpt-5.4")
DEFAULT_REASONING_EFFORT = os.environ.get("CODEX_REFACTOR_REASONING_EFFORT", "xhigh")


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


def codex_env() -> dict[str, str]:
    env = os.environ.copy()
    env["HOME"] = str(CODEX_HOME_ROOT)
    env["PATH"] = f"/tmp/lake-bin:/tmp/lean4-toolchain/bin:{env.get('PATH', '')}"
    env.setdefault("CODEX_CI", "1")
    return env


def write_status(**payload: object) -> None:
    status = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "pid": os.getpid(),
        **payload,
    }
    SUPERVISOR_STATUS.write_text(json.dumps(status, indent=2, sort_keys=True))


def append_history(record: dict) -> None:
    with SUPERVISOR_HISTORY.open("a") as f:
        f.write(json.dumps(record) + "\n")


def read_text(path: Path, max_chars: int = 12000) -> str:
    if not path.exists():
        return ""
    text = path.read_text()
    if len(text) > max_chars:
        return text[:max_chars] + f"\n... [truncated, {len(text)} chars total]"
    return text


def load_history(n: int = 12) -> str:
    lines: list[str] = []
    for path in [STATE_DIR / "history.jsonl", STATE_DIR / "codex_history.jsonl", SUPERVISOR_HISTORY]:
        if not path.exists():
            continue
        for line in path.read_text().splitlines():
            line = line.strip()
            if line:
                lines.append(line)
    if not lines:
        return "(no history)"
    return "\n".join(lines[-n:])


def worker_pid() -> int | None:
    if not WORKER_LOCK.exists():
        return None
    try:
        return int(WORKER_LOCK.read_text().strip())
    except ValueError:
        return None


def pid_alive(pid: int | None) -> bool:
    if pid is None:
        return False
    try:
        os.kill(pid, 0)
        return True
    except OSError:
        return False


def stop_worker_loop() -> bool:
    pid = worker_pid()
    if not pid_alive(pid):
        return False
    os.kill(pid, signal.SIGTERM)
    for _ in range(20):
        if not pid_alive(pid):
            return True
        time.sleep(1)
    os.kill(pid, signal.SIGKILL)
    return True


def start_worker_loop() -> int:
    log_path = STATE_DIR / "codex_worker_loop.log"
    log_file = log_path.open("a")
    proc = subprocess.Popen(
        [str(WORKER_LOOP_SCRIPT), "--loop"],
        cwd=REPO_DIR,
        stdout=log_file,
        stderr=subprocess.STDOUT,
        env=os.environ.copy(),
        start_new_session=True,
    )
    return proc.pid


def run_codex(prompt: str, output_path: Path) -> tuple[int, str]:
    cmd = [
        str(CODEX_BIN),
        "exec",
        "-C",
        str(REPO_DIR),
        "--color",
        "never",
        "--ephemeral",
        "--dangerously-bypass-approvals-and-sandbox",
        "-m",
        DEFAULT_MODEL,
        "-c",
        f'model_reasoning_effort="{DEFAULT_REASONING_EFFORT}"',
        "-o",
        str(output_path),
        prompt,
    ]
    result = subprocess.run(
        cmd,
        cwd=REPO_DIR,
        capture_output=True,
        text=True,
        check=False,
        timeout=SUPERVISOR_TIMEOUT,
        env=codex_env(),
    )
    text = output_path.read_text() if output_path.exists() else result.stdout[-12000:]
    return result.returncode, text


def run_supervisor_audit() -> dict:
    ensure_setup()
    SUPERVISOR_REPORTS.mkdir(parents=True, exist_ok=True)
    now = datetime.now(timezone.utc)
    report_name = f"{now.strftime('%Y%m%dT%H%M%SZ')}"
    report_path = SUPERVISOR_REPORTS / f"{report_name}.md"
    template = Template((PROMPTS_DIR / "codex_supervisor.md").read_text())
    prompt = template.safe_substitute(
        history=load_history(),
        status=read_text(WORKER_STATUS),
        report_name=report_name,
    )
    output_path = STATE_DIR / "codex_supervisor_last_message.txt"
    exit_code, _ = run_codex(prompt, output_path)
    return {
        "timestamp": now.isoformat(),
        "exit_code": exit_code,
        "report_path": str(report_path),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Codex refactor supervisor")
    parser.add_argument("--loop", action="store_true", help="Run continuously")
    parser.add_argument("--interval", type=int, default=COOLDOWN, help="Seconds between audits")
    parser.add_argument("--restart-loop", action="store_true", help="Stop the worker loop before audit and restart it after")
    parser.add_argument("--stop-worker-only", action="store_true", help="Stop the worker loop before audit, but do not restart it")
    args = parser.parse_args()

    lock = FileLock(SUPERVISOR_LOCK)
    if not lock.acquire():
        raise SystemExit("Codex supervisor is already running")

    try:
        while True:
            write_status(mode="starting", worker_running=pid_alive(worker_pid()))
            stopped = False
            restarted_pid = None
            try:
                if args.restart_loop or args.stop_worker_only:
                    stopped = stop_worker_loop()
                    write_status(mode="auditing", worker_stopped=stopped)
                record = run_supervisor_audit()
                if args.restart_loop:
                    restarted_pid = start_worker_loop()
                record["worker_stopped"] = stopped
                record["worker_restarted_pid"] = restarted_pid
                append_history(record)
                write_status(mode="idle", **record)
            except Exception as exc:
                write_status(mode="error", error=str(exc))
                print(f"Supervisor audit failed: {exc}", file=sys.stderr)
            if not args.loop:
                break
            time.sleep(args.interval)
    finally:
        lock.release()


if __name__ == "__main__":
    main()
