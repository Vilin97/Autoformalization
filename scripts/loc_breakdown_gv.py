#!/usr/bin/env python3
"""Generate a LOC-by-file-group stacked area chart for the Grothendieck Vanishing project.

Walks commits on wip/grothendieck-vanishing that touch
Aristotle/GrothendieckVanishing/main/*.lean, counts lines per file at each
commit, groups files into logical categories, and renders a stacked area chart.
"""

import subprocess
import os
from datetime import datetime, timezone, timedelta

import matplotlib.pyplot as plt
import matplotlib.dates as mdates
import numpy as np

REPO = "/Users/vasil/Github/aristotle"
OUT_DIR = os.path.join(REPO, "artifacts")
OUT_PNG = os.path.join(OUT_DIR, "loc_breakdown_gv.png")
BRANCH = "wip/grothendieck-vanishing"
FILE_PATTERN = "Aristotle/GrothendieckVanishing/main/"
PDT = timezone(timedelta(hours=-7))

# Sample every Nth commit for speed (286 commits x ~20 files is slow)
SAMPLE_EVERY = 3

# File groups: (label, color, list of filenames)
# Order: cool (bottom) to warm (top) in the stack
GROUPS = [
    ("Filtered colimit",   "#2ca02c", ["PresheafFilteredColimit.lean"]),
    ("Stalk/generator",    "#17becf", ["SheafStalkAlgebra.lean", "StalkGeneratorAlgebra.lean"]),
    ("Extension-by-zero",  "#00bcd4", ["ZeroOutside.lean", "ZeroOutsideFinset.lean"]),
    ("Closed immersion",   "#5dade2", ["ClosedImmersion.lean"]),
    ("Setup/core",         "#1f77b4", ["SetupCore.lean", "Setup.lean", "CohomologyIso.lean", "Auxiliary.lean"]),
    ("Flasque vanishing",  "#0d47a1", ["FlasqueVanishing.lean", "FlasqueCohomology.lean"]),
    ("Dim 0",              "#f4a460", ["DimZeroVanishing.lean", "ConstantSheafFlasque.lean"]),
    ("Closed-open decomp", "#ff8c00", ["ClosedOpenDecomposition.lean", "ReducibleVanishing.lean"]),
    ("Irreducible step",   "#e74c3c", ["IrreducibleStep.lean", "FiniteGeneratorReduction.lean"]),
    ("Main theorem",       "#b71c1c", ["GrothendieckVanishing.lean", "main.lean"]),
]


def git(*args: str) -> subprocess.CompletedProcess:
    """Run a git command in the repo and return the CompletedProcess."""
    return subprocess.run(
        ["git"] + list(args),
        cwd=REPO,
        capture_output=True,
        text=True,
    )


def get_commits():
    """Return list of (commit_hash, datetime_pdt) for commits that touch the GV files."""
    result = git(
        "log",
        BRANCH,
        "--format=%H %aI",
        "--reverse",
        "--",
        FILE_PATTERN,
    )
    commits = []
    for line in result.stdout.strip().splitlines():
        if not line.strip():
            continue
        parts = line.split(None, 1)
        sha = parts[0]
        iso_date = parts[1]
        dt = datetime.fromisoformat(iso_date).astimezone(PDT)
        commits.append((sha, dt))
    return commits


def count_lines_per_file(sha: str) -> dict[str, int]:
    """Count lines per .lean file in the GV directory at the given commit.

    Uses `git show <sha>:<file> | wc -l` for speed instead of reading full content.
    """
    tree_result = git("ls-tree", "--name-only", "-r", sha, "--", FILE_PATTERN)
    if not tree_result.stdout.strip():
        return {}

    counts: dict[str, int] = {}
    for filepath in tree_result.stdout.strip().splitlines():
        if not filepath.endswith(".lean"):
            continue
        filename = os.path.basename(filepath)
        # Use wc -l via shell for speed
        wc_result = subprocess.run(
            f'git show {sha}:{filepath} | wc -l',
            cwd=REPO,
            capture_output=True,
            text=True,
            shell=True,
        )
        try:
            counts[filename] = int(wc_result.stdout.strip())
        except ValueError:
            counts[filename] = 0
    return counts


def group_counts(file_counts: dict[str, int]) -> list[int]:
    """Given per-file line counts, return a list of totals per group (same order as GROUPS)."""
    totals = []
    for _label, _color, filenames in GROUPS:
        total = sum(file_counts.get(fn, 0) for fn in filenames)
        totals.append(total)
    return totals


def main():
    os.makedirs(OUT_DIR, exist_ok=True)

    print("Collecting commits...")
    all_commits = get_commits()
    print(f"Found {len(all_commits)} commits touching GV files.")

    # Sample every Nth commit, always include the last one
    sampled = all_commits[::SAMPLE_EVERY]
    if all_commits and sampled[-1] != all_commits[-1]:
        sampled.append(all_commits[-1])
    print(f"Sampling {len(sampled)} commits (every {SAMPLE_EVERY}).")

    dates: list[datetime] = []
    # group_series[i] = list of LOC values for group i across commits
    group_series: list[list[int]] = [[] for _ in GROUPS]

    for i, (sha, dt) in enumerate(sampled):
        file_counts = count_lines_per_file(sha)
        totals = group_counts(file_counts)
        dates.append(dt)
        for j, val in enumerate(totals):
            group_series[j].append(val)
        if (i + 1) % 10 == 0 or i == len(sampled) - 1:
            total_loc = sum(totals)
            print(f"  [{i + 1}/{len(sampled)}] {dt:%Y-%m-%d %H:%M} -> {total_loc} lines")

    # --- Plot ---
    fig, ax = plt.subplots(figsize=(12, 6))

    labels = [g[0] for g in GROUPS]
    colors = [g[1] for g in GROUPS]

    # stackplot expects arrays; stack order matches GROUPS (cool bottom, warm top)
    y = np.array(group_series)
    ax.stackplot(dates, *y, labels=labels, colors=colors, alpha=0.85)

    # X-axis: Mar 27 - Apr 5, PDT
    ax.set_xlim(
        datetime(2026, 3, 27, 0, 0, tzinfo=PDT),
        datetime(2026, 4, 5, 0, 0, tzinfo=PDT),
    )
    ax.xaxis.set_major_locator(mdates.DayLocator(tz=PDT))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=PDT))
    ax.set_xlabel("Date (PDT)", fontsize=10)

    ax.set_ylabel("Lines of Code", fontsize=10)
    ax.set_title(
        "Grothendieck Vanishing \u2014 LOC by File Group",
        fontsize=13,
        fontweight="bold",
    )

    ax.grid(True, color="gray", linewidth=0.3, alpha=0.6)
    ax.set_axisbelow(True)

    # Legend: reversed so warm colors (top of stack) are at top of legend
    handles, leg_labels = ax.get_legend_handles_labels()
    ax.legend(
        handles[::-1],
        leg_labels[::-1],
        loc="center left",
        bbox_to_anchor=(1.01, 0.5),
        fontsize=8,
        frameon=True,
        framealpha=0.9,
    )

    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150, bbox_inches="tight")
    print(f"\nSaved chart to {OUT_PNG}")


if __name__ == "__main__":
    main()
