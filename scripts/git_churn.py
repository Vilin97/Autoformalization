#!/usr/bin/env python3
"""Visualize git churn (lines added/deleted per day) for Aristotle/Landau/ .lean files."""

import subprocess
import re
from collections import defaultdict
from datetime import datetime, timezone, timedelta
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates

PT = timezone(timedelta(hours=-7))  # PDT

REPO = Path(__file__).resolve().parent.parent
TARGET_DIR = "Aristotle/Landau/"
EXCLUDE_DIRS = {"Aristotle/Landau/aristotle-in/", "Aristotle/Landau/aristotle-out/"}
OUT_PNG = REPO / "scripts" / "git_churn.png"


def parse_git_log():
    """Run git log --numstat and aggregate additions/deletions per day (PDT)."""
    result = subprocess.run(
        [
            "git", "log", "--numstat", "--format=%aI", "--",
            f"{TARGET_DIR}*.lean", f"{TARGET_DIR}**/*.lean",
        ],
        capture_output=True, text=True, cwd=REPO,
    )

    added_by_day = defaultdict(int)
    deleted_by_day = defaultdict(int)
    current_date = None

    for line in result.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        if re.match(r"^\d{4}-\d{2}-\d{2}T", line):
            dt = datetime.fromisoformat(line).astimezone(PT)
            current_date = dt.date()
            continue
        parts = line.split("\t")
        if len(parts) == 3 and current_date is not None:
            add_str, del_str, filepath = parts
            if add_str == "-" or del_str == "-":
                continue
            if not filepath.endswith(".lean"):
                continue
            if any(filepath.startswith(ex) for ex in EXCLUDE_DIRS):
                continue
            if not filepath.startswith(TARGET_DIR):
                continue
            added_by_day[current_date] += int(add_str)
            deleted_by_day[current_date] += int(del_str)

    return added_by_day, deleted_by_day


def main():
    added, deleted = parse_git_log()
    total_add = sum(added.values())
    total_del = sum(deleted.values())
    print(f"Total: +{total_add} -{total_del} net {total_add - total_del}"
          f" across {len(set(added) | set(deleted))} days")

    all_days = sorted(set(added.keys()) | set(deleted.keys()))
    if not all_days:
        print("No data found.")
        return

    adds = [added.get(d, 0) for d in all_days]
    dels = [deleted.get(d, 0) for d in all_days]

    fig, ax = plt.subplots(figsize=(12, 5))

    bar_width = 0.8
    ax.bar(all_days, adds, width=bar_width, color="#2ecc71", alpha=0.85,
           label=f"Lines added (+{total_add:,})")
    ax.bar(all_days, [-d for d in dels], width=bar_width, color="#e74c3c", alpha=0.85,
           label=f"Lines deleted (-{total_del:,})")
    ax.axhline(0, color="black", linewidth=0.5)

    ax.set_ylabel("Lines changed")
    ax.set_title("Git Churn: Lines Added and Deleted per Day", fontsize=13, fontweight="bold")
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=PT))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=1, tz=PT))
    ax.legend(loc="upper left", fontsize=9)
    ax.grid(True, axis="y", alpha=0.3)
    fig.autofmt_xdate()

    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150)
    print(f"Saved to {OUT_PNG}")


if __name__ == "__main__":
    main()
