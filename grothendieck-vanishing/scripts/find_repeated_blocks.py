#!/usr/bin/env python3
"""Find repeated proof blocks across Lean files.

Scans .lean files for repeated sequences of tactic lines (ignoring leading
whitespace). Reports blocks of N+ consecutive matching lines that appear
in 2+ locations. These are candidates for helper extraction.

Usage:
    python scripts/find_repeated_blocks.py [dir] [--min-lines N] [--min-occurrences N]

Example:
    python scripts/find_repeated_blocks.py Aristotle/GrothendieckVanishing/main/ --min-lines 3
"""

import argparse
import os
import re
from collections import defaultdict
from pathlib import Path


def normalize_line(line: str) -> str:
    """Strip leading whitespace and trailing whitespace for comparison."""
    return line.strip()


def is_tactic_line(line: str) -> bool:
    """Check if a line looks like a tactic/proof line (not a declaration or comment)."""
    stripped = line.strip()
    if not stripped:
        return False
    # Skip pure comments, section headers, docstrings
    if stripped.startswith("--") or stripped.startswith("/-") or stripped.startswith("-/"):
        return False
    # Skip declarations (theorem, def, lemma, etc.)
    if re.match(r'^(theorem|def|lemma|abbrev|noncomputable|private|instance|section|namespace|end|open|universe|import|variable)', stripped):
        return False
    return True


def extract_blocks(filepath: str, min_lines: int) -> list[tuple[str, str, int, list[str]]]:
    """Extract all consecutive tactic blocks of length >= min_lines.

    Returns list of (filepath, block_key, start_line, lines).
    block_key is the normalized joined string for comparison.
    """
    with open(filepath) as f:
        lines = f.readlines()

    blocks = []
    current_block_start = None
    current_block_lines = []

    for i, line in enumerate(lines):
        if is_tactic_line(line):
            if current_block_start is None:
                current_block_start = i + 1  # 1-indexed
            current_block_lines.append(line)
        else:
            if len(current_block_lines) >= min_lines:
                # Generate all sub-blocks of length >= min_lines
                for start in range(len(current_block_lines)):
                    for end in range(start + min_lines, len(current_block_lines) + 1):
                        sub = current_block_lines[start:end]
                        key = "\n".join(normalize_line(l) for l in sub)
                        blocks.append((
                            filepath,
                            key,
                            current_block_start + start,
                            [l.rstrip() for l in sub]
                        ))
            current_block_start = None
            current_block_lines = []

    # Handle last block
    if len(current_block_lines) >= min_lines:
        for start in range(len(current_block_lines)):
            for end in range(start + min_lines, len(current_block_lines) + 1):
                sub = current_block_lines[start:end]
                key = "\n".join(normalize_line(l) for l in sub)
                blocks.append((
                    filepath,
                    key,
                    current_block_start + start,
                    [l.rstrip() for l in sub]
                ))

    return blocks


def find_repeated_blocks(directory: str, min_lines: int, min_occurrences: int):
    """Find repeated blocks across all .lean files in directory."""

    # Collect all blocks
    all_blocks = []
    for root, dirs, files in os.walk(directory):
        for fname in sorted(files):
            if fname.endswith(".lean"):
                filepath = os.path.join(root, fname)
                all_blocks.extend(extract_blocks(filepath, min_lines))

    # Group by normalized content
    by_key = defaultdict(list)
    for filepath, key, line, lines in all_blocks:
        by_key[key].append((filepath, line, lines))

    # Filter to blocks appearing in 2+ distinct locations
    # (same file different line counts as distinct)
    repeated = {}
    for key, locations in by_key.items():
        # Deduplicate: same file + overlapping lines = same location
        unique_locations = []
        seen = set()
        for filepath, line, lines in locations:
            loc_key = (filepath, line)
            if loc_key not in seen:
                seen.add(loc_key)
                unique_locations.append((filepath, line, lines))

        # Must appear in 2+ non-overlapping locations
        if len(unique_locations) >= min_occurrences:
            # Check they're not all overlapping within the same file
            by_file = defaultdict(list)
            for fp, ln, ls in unique_locations:
                by_file[fp].append(ln)

            non_overlapping = []
            for fp, starts in by_file.items():
                starts.sort()
                last_end = -1
                for s in starts:
                    if s > last_end:
                        non_overlapping.append((fp, s))
                        last_end = s + key.count("\n")

            if len(non_overlapping) >= min_occurrences:
                n_lines = key.count("\n") + 1
                repeated[key] = (n_lines, non_overlapping, unique_locations[0][2])

    # Sort by (number of lines * occurrences) descending = total savings potential
    ranked = sorted(
        repeated.items(),
        key=lambda x: x[1][0] * len(x[1][1]),
        reverse=True
    )

    # Remove sub-blocks: if a block is a subset of a longer block at the same
    # locations, skip the shorter one
    seen_locations = set()
    filtered = []
    for key, (n_lines, locations, sample) in ranked:
        loc_set = frozenset((fp, ln) for fp, ln in locations)
        # Check if this is a sub-block of something already reported
        is_sub = False
        for prev_locs in seen_locations:
            if all(any(fp == pfp and pln <= ln <= pln + 50
                      for pfp, pln in prev_locs)
                   for fp, ln in loc_set):
                is_sub = True
                break
        if not is_sub:
            filtered.append((key, n_lines, locations, sample))
            seen_locations.add(loc_set)

    return filtered


def main():
    parser = argparse.ArgumentParser(description="Find repeated proof blocks in Lean files")
    parser.add_argument("directory", nargs="?", default="Aristotle/GrothendieckVanishing/main/",
                       help="Directory to scan")
    parser.add_argument("--min-lines", type=int, default=3,
                       help="Minimum block length (default: 3)")
    parser.add_argument("--min-occurrences", type=int, default=2,
                       help="Minimum number of occurrences (default: 2)")
    parser.add_argument("--top", type=int, default=20,
                       help="Show top N results (default: 20)")
    args = parser.parse_args()

    results = find_repeated_blocks(args.directory, args.min_lines, args.min_occurrences)

    if not results:
        print("No repeated blocks found.")
        return

    print(f"Found {len(results)} repeated blocks (showing top {args.top}):\n")

    for i, (key, n_lines, locations, sample) in enumerate(results[:args.top]):
        savings = n_lines * (len(locations) - 1)  # keep one, save the rest
        print(f"{'='*70}")
        print(f"#{i+1}: {n_lines} lines × {len(locations)} occurrences "
              f"(potential savings: ~{savings} lines)")
        print(f"{'='*70}")
        for fp, ln in locations:
            short_fp = os.path.basename(fp)
            print(f"  {short_fp}:{ln}")
        print()
        for line in sample[:8]:  # Show first 8 lines
            print(f"    {line}")
        if n_lines > 8:
            print(f"    ... ({n_lines - 8} more lines)")
        print()


if __name__ == "__main__":
    main()
