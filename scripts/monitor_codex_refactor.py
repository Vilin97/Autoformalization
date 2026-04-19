#!/usr/bin/env python3.9
from __future__ import annotations

import json
from pathlib import Path


REPO_DIR = Path(__file__).resolve().parent.parent
STATE_DIR = REPO_DIR / ".refactor-state"
STATUS_FILE = STATE_DIR / "codex_status.json"
HISTORY_FILE = STATE_DIR / "codex_history.jsonl"


def tail_history() -> dict | None:
    if not HISTORY_FILE.exists():
        return None
    lines = [line.strip() for line in HISTORY_FILE.read_text().splitlines() if line.strip()]
    if not lines:
        return None
    return json.loads(lines[-1])


def main() -> None:
    if STATUS_FILE.exists():
        status = json.loads(STATUS_FILE.read_text())
        print(json.dumps(status, indent=2, sort_keys=True))
    else:
        print("No codex status file yet.")

    record = tail_history()
    if record is None:
        print("No codex cycle history yet.")
        return

    print("\nLast completed cycle:")
    print(json.dumps(record, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
