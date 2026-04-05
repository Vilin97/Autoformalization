#!/usr/bin/env python3
"""Generate a lines-of-code-over-time chart for the Grothendieck Vanishing project.

Walks every commit on wip/grothendieck-vanishing that touches
Aristotle/GrothendieckVanishing/main/*.lean, counts total lines in those
files at each commit, and renders a matplotlib chart.
"""

import subprocess
import os
from datetime import datetime, timezone, timedelta

import matplotlib.pyplot as plt
import matplotlib.dates as mdates

REPO = "/Users/vasil/Github/aristotle"
OUT_DIR = os.path.join(REPO, "artifacts")
OUT_PNG = os.path.join(OUT_DIR, "loc_history_gv.png")
BRANCH = "wip/grothendieck-vanishing"
FILE_PATTERN = "Aristotle/GrothendieckVanishing/main/"
PDT = timezone(timedelta(hours=-7))


def git(*args: str) -> str:
    """Run a git command in the repo and return stdout."""
    result = subprocess.run(
        ["git"] + list(args),
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def get_commits():
    """Return list of (commit_hash, datetime_pdt) for commits that touch the GV files."""
    # Get all commits on the branch that touch the GV directory, oldest first
    log = git(
        "log",
        BRANCH,
        "--format=%H %aI",
        "--reverse",
        "--",
        f"{FILE_PATTERN}",
    )
    commits = []
    for line in log.splitlines():
        if not line.strip():
            continue
        parts = line.split(None, 1)
        sha = parts[0]
        iso_date = parts[1]
        dt = datetime.fromisoformat(iso_date).astimezone(PDT)
        commits.append((sha, dt))
    return commits


def count_lines_at_commit(sha: str) -> int:
    """Count total lines across all .lean files in the GV directory at the given commit."""
    # List files in the tree at that commit
    tree_listing = git("ls-tree", "--name-only", "-r", sha, "--", FILE_PATTERN)
    if not tree_listing:
        return 0
    total = 0
    for filepath in tree_listing.splitlines():
        if not filepath.endswith(".lean"):
            continue
        content = git("show", f"{sha}:{filepath}")
        total += content.count("\n") + (1 if content and not content.endswith("\n") else 0)
    return total


def main():
    os.makedirs(OUT_DIR, exist_ok=True)

    print("Collecting commits...")
    commits = get_commits()
    print(f"Found {len(commits)} commits touching GV files.")

    dates = []
    locs = []
    for i, (sha, dt) in enumerate(commits):
        loc = count_lines_at_commit(sha)
        dates.append(dt)
        locs.append(loc)
        if (i + 1) % 20 == 0 or i == len(commits) - 1:
            print(f"  [{i + 1}/{len(commits)}] {dt:%Y-%m-%d %H:%M} -> {loc} lines")

    # --- Notable events (approximate PDT timestamps) ---
    events = [
        (datetime(2026, 3, 27, 11, 54, tzinfo=PDT), "Skeleton\n(2 sorry's)"),
        (datetime(2026, 3, 28,  8,  0, tzinfo=PDT), "constantSheaf_flasque\nPROVED"),
        (datetime(2026, 3, 28, 22, 20, tzinfo=PDT), "ReducibleVanishing\nPROVED"),
        (datetime(2026, 3, 29, 22, 30, tzinfo=PDT), "Decompose into\n3 sub-lemmas"),
        (datetime(2026, 3, 30, 12,  0, tzinfo=PDT), "imageIncl_cokernel_epi\n(3\u21922 sorry's)"),
        (datetime(2026, 4,  1, 13, 53, tzinfo=PDT), "Restore 14 regressed\nproofs (16\u21922)"),
        (datetime(2026, 4,  2, 21,  0, tzinfo=PDT), "1 sorry\nremains"),
        (datetime(2026, 4,  3, 19, 30, tzinfo=PDT), "Decompose into\nisSheaf + colimit"),
        (datetime(2026, 4,  4, 17, 18, tzinfo=PDT), "0 sorry's\n(COMPLETE)"),
    ]

    # --- Plot ---
    fig, ax = plt.subplots(figsize=(12, 5))

    ax.plot(dates, locs, color="royalblue", marker="o", markersize=3,
            linewidth=1.5, zorder=3)

    # Annotations: alternate above/below to reduce overlap
    y_min, y_max = min(locs), max(locs)
    y_range = y_max - y_min if y_max != y_min else 1
    for idx, (evt_dt, label) in enumerate(events):
        # Draw a thin vertical line at the event time
        ax.axvline(evt_dt, color="gray", linewidth=0.5, alpha=0.5, zorder=1)

        # Find the closest data point to get the y value
        closest_idx = min(range(len(dates)), key=lambda j: abs((dates[j] - evt_dt).total_seconds()))
        y_val = locs[closest_idx]

        # Alternate offset direction
        if idx % 2 == 0:
            y_offset = y_range * 0.18
            va = "bottom"
        else:
            y_offset = -y_range * 0.18
            va = "top"

        ax.annotate(
            label,
            xy=(evt_dt, y_val),
            xytext=(evt_dt, y_val + y_offset),
            fontsize=7,
            ha="center",
            va=va,
            arrowprops=dict(arrowstyle="-", color="gray", linewidth=0.7),
            bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="gray", alpha=0.85),
            zorder=5,
        )

    # X-axis: Mar 27 - Apr 4, PDT
    ax.set_xlim(
        datetime(2026, 3, 27, 0, 0, tzinfo=PDT),
        datetime(2026, 4, 5, 0, 0, tzinfo=PDT),
    )
    ax.xaxis.set_major_locator(mdates.DayLocator(tz=PDT))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=PDT))
    ax.set_xlabel("Date (PDT)", fontsize=10)

    ax.set_ylabel("Total Lines of Code", fontsize=10)
    ax.set_title("Grothendieck Vanishing \u2014 Lines of Code", fontsize=13, fontweight="bold")

    ax.grid(True, color="gray", linewidth=0.3, alpha=0.6)
    ax.set_axisbelow(True)

    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150)
    print(f"\nSaved chart to {OUT_PNG}")


if __name__ == "__main__":
    main()
