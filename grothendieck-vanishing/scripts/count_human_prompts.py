#!/usr/bin/env python3.9
"""Count human prompts in Claude Code session JSONL transcripts.

A "human prompt" is a `type: "user"` record whose `message.content` is a plain
string (not a tool_result block list). The Claude Code transcript stores tool
results as `type: "user"` too — those are filtered out.

Usage:
    python3.9 scripts/count_human_prompts.py [<dir-or-file> ...]

Defaults to the local Claude Code project dir for this repo if no args given.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

DEFAULT_DIR = Path.home() / ".claude" / "projects" / "-Users-vasil-Github-Clawristotle"


def is_human_prompt(record: dict) -> bool:
    if record.get("type") != "user":
        return False
    msg = record.get("message", {})
    if msg.get("role") != "user":
        return False
    content = msg.get("content")
    return isinstance(content, str) and bool(content.strip())


def count_session(path: Path) -> tuple[int, int, str | None, str | None]:
    """Return (human_prompts, total_user_records, first_ts, last_ts)."""
    human = total = 0
    first_ts = last_ts = None
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if r.get("type") == "user":
                total += 1
                ts = r.get("timestamp")
                if ts:
                    if first_ts is None or ts < first_ts:
                        first_ts = ts
                    if last_ts is None or ts > last_ts:
                        last_ts = ts
                if is_human_prompt(r):
                    human += 1
    return human, total, first_ts, last_ts


def main(argv: list[str]) -> int:
    targets: list[Path] = []
    for a in argv[1:] or [str(DEFAULT_DIR)]:
        p = Path(a)
        if p.is_dir():
            targets.extend(sorted(p.glob("*.jsonl")))
        elif p.is_file():
            targets.append(p)
        else:
            print(f"warn: {p} not found", file=sys.stderr)
    if not targets:
        print("no jsonl files found", file=sys.stderr)
        return 1
    grand_human = grand_total = 0
    print(f"{'session':<40} {'human':>6} {'tool_resp':>10} {'first':<26} {'last':<26}")
    for p in targets:
        h, t, fts, lts = count_session(p)
        grand_human += h
        grand_total += t
        print(f"{p.stem[:40]:<40} {h:>6} {t-h:>10} {(fts or '-')[:26]:<26} {(lts or '-')[:26]:<26}")
    print("-" * 100)
    print(f"{'TOTAL':<40} {grand_human:>6} {grand_total-grand_human:>10}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
