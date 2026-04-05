#!/usr/bin/env python3
"""Generate a git churn (lines added/deleted per day) chart for the Grothendieck Vanishing project."""

import subprocess
import re
from collections import defaultdict
from datetime import datetime, timedelta, timezone

import matplotlib.pyplot as plt
import matplotlib.dates as mdates
import numpy as np

REPO = "/Users/vasil/Github/aristotle"
OUT = "/Users/vasil/Github/aristotle/artifacts/git_churn_gv.png"

# PDT = UTC-7
PDT = timezone(timedelta(hours=-7))

# Date range
START = datetime(2026, 3, 27, tzinfo=PDT).date()
END = datetime(2026, 4, 4, tzinfo=PDT).date()


def get_churn_data():
    """Run git log --numstat and aggregate additions/deletions by day (PDT)."""
    result = subprocess.run(
        [
            "git", "log", "--numstat", "--format=%aI",
            "wip/grothendieck-vanishing",
            "--", "Aristotle/GrothendieckVanishing/main/*.lean",
        ],
        cwd=REPO,
        capture_output=True,
        text=True,
    )

    adds_by_day = defaultdict(int)
    dels_by_day = defaultdict(int)

    current_date = None
    for line in result.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        # Try to parse as ISO date (commit header line)
        if re.match(r"^\d{4}-\d{2}-\d{2}T", line):
            dt = datetime.fromisoformat(line).astimezone(PDT)
            current_date = dt.date()
            continue
        # Try to parse as numstat line: added<TAB>deleted<TAB>filename
        parts = line.split("\t")
        if len(parts) == 3 and current_date is not None:
            added, deleted, _filename = parts
            if added == "-" or deleted == "-":
                # binary file
                continue
            adds_by_day[current_date] += int(added)
            dels_by_day[current_date] += int(deleted)

    return adds_by_day, dels_by_day


def main():
    adds_by_day, dels_by_day = get_churn_data()

    # Build arrays for the date range
    days = []
    d = START
    while d <= END:
        days.append(d)
        d += timedelta(days=1)

    additions = np.array([adds_by_day.get(d, 0) for d in days], dtype=float)
    deletions = np.array([dels_by_day.get(d, 0) for d in days], dtype=float)
    net = additions - deletions

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 7), sharex=True)
    fig.suptitle("Grothendieck Vanishing — Git Churn", fontsize=16, fontweight="bold")

    bar_width = 0.8

    # Top subplot: stacked additions (green) and deletions (red, negative)
    ax1.bar(days, additions, width=bar_width, color="#2ecc71", label="Additions", zorder=3)
    ax1.bar(days, -deletions, width=bar_width, color="#e74c3c", label="Deletions", zorder=3)
    ax1.axhline(0, color="black", linewidth=0.5)
    ax1.set_ylabel("Lines")
    ax1.legend(loc="upper left")
    ax1.grid(True, color="gray", alpha=0.3, zorder=0)
    ax1.set_title("Additions & Deletions per Day", fontsize=12)

    # Bottom subplot: net change (blue)
    colors = ["#3498db" if n >= 0 else "#e67e22" for n in net]
    ax2.bar(days, net, width=bar_width, color=colors, zorder=3)
    ax2.axhline(0, color="black", linewidth=0.5)
    ax2.set_ylabel("Net Lines")
    ax2.grid(True, color="gray", alpha=0.3, zorder=0)
    ax2.set_title("Net Change per Day", fontsize=12)

    # Format x-axis
    ax2.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax2.xaxis.set_major_locator(mdates.DayLocator())
    plt.setp(ax2.xaxis.get_majorticklabels(), rotation=45, ha="right")

    plt.tight_layout()
    fig.savefig(OUT, dpi=150)
    print(f"Saved to {OUT}")
    print(f"  Date range: {START} to {END}")
    print(f"  Total additions: {int(additions.sum())}")
    print(f"  Total deletions: {int(deletions.sum())}")
    print(f"  Net change: {int(net.sum())}")


if __name__ == "__main__":
    main()
