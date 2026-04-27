#!/usr/bin/env python3.9
"""
Normalized LOC metric for the compress loop.

Strips block + line comments, drops blank lines, and splits stacked tactics
on `;` and `<;>` so the per-cycle gate cannot be gamed by:

  - deleting comments or blank lines
  - stacking `tac1; tac2; tac3` onto one line
  - chaining via `tac1 <;> tac2`

Used both as a Python module (the loop imports `total_normalized_count`) and
as a CLI:

    python3.9 scripts/normalized_loc.py                # prints total
    python3.9 scripts/normalized_loc.py --per-file     # prints each file + total
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


REPO_DIR = Path(__file__).resolve().parent.parent
MAIN_DIR = REPO_DIR / "Aristotle" / "GrothendieckVanishing" / "main"


def strip_block_comments(text: str) -> str:
    """Strip Lean block comments, handling nesting.

    Treats `/- ... -/`, `/-- ... -/`, and `/-! ... -/` uniformly as comments.
    String-literal awareness is intentionally omitted; project source has no
    strings containing `/-` or `-/`.
    """
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if i + 1 < n and text[i] == "/" and text[i + 1] == "-":
            depth += 1
            i += 2
            continue
        if depth > 0 and i + 1 < n and text[i] == "-" and text[i + 1] == "/":
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def strip_line_comments(text: str) -> str:
    """Drop `-- ...` line comments. No string awareness — project source has
    no string literals containing `--`."""
    out_lines: list[str] = []
    for line in text.splitlines():
        idx = line.find("--")
        if idx >= 0:
            line = line[:idx]
        out_lines.append(line)
    return "\n".join(out_lines)


def count_tactic_units(text: str) -> int:
    """Count non-blank logical units after splitting each line on `;` and `<;>`."""
    count = 0
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        normalized = line.replace("<;>", ";")
        for part in normalized.split(";"):
            if part.strip():
                count += 1
    return count


def normalize_count_text(text: str) -> int:
    return count_tactic_units(strip_line_comments(strip_block_comments(text)))


def normalize_count_file(path: Path) -> int:
    return normalize_count_text(path.read_text())


def list_main_files() -> list[Path]:
    return sorted(MAIN_DIR.glob("*.lean"))


def per_file_counts() -> list[tuple[Path, int]]:
    return [(path, normalize_count_file(path)) for path in list_main_files()]


def total_normalized_count() -> int:
    return sum(n for _, n in per_file_counts())


def total_raw_loc() -> int:
    total = 0
    for path in list_main_files():
        total += sum(1 for _ in path.read_text().splitlines())
    return total


def main() -> None:
    parser = argparse.ArgumentParser(description="Normalized LOC metric")
    parser.add_argument("--per-file", action="store_true", help="Print per-file breakdown")
    parser.add_argument("--raw", action="store_true", help="Also print raw wc -l for comparison")
    args = parser.parse_args()

    counts = per_file_counts()
    total = sum(n for _, n in counts)

    if args.per_file:
        for path, n in counts:
            rel = path.relative_to(REPO_DIR)
            print(f"{n:6d}  {rel}")
        print(f"{total:6d}  TOTAL (normalized)")
    else:
        print(total)

    if args.raw:
        raw = total_raw_loc()
        print(f"{raw:6d}  TOTAL (raw wc -l)", file=sys.stderr)


if __name__ == "__main__":
    main()
