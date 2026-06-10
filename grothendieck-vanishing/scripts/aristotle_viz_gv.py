#!/usr/bin/env python3
"""
Generate an Aristotle outcomes chart for the Grothendieck Vanishing project.

Fetches all Aristotle projects created on or after 2026-03-27, classifies them
by outcome status, and produces a two-panel figure:
  - Left:  pie chart of outcome breakdown
  - Right: stacked bar chart of submissions per day, colored by outcome
"""

import asyncio
import os
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

# Set API key before importing aristotlelib
os.environ["ARISTOTLE_API_KEY"] = "arstl_JpLO92RXUx_X6rpIn78M8_ksUhFgUAbdqZKQ4gNBLxs"

from aristotlelib import Project  # noqa: E402

import matplotlib.pyplot as plt  # noqa: E402
import matplotlib.dates as mdates  # noqa: E402
import matplotlib.ticker as mticker  # noqa: E402

REPO = Path("/Users/vasil/Github/aristotle")
OUT_DIR = REPO / "artifacts"
OUT_DIR.mkdir(parents=True, exist_ok=True)

GV_START = datetime(2026, 3, 27)  # naive datetime for comparison

# Colors and labels keyed by status value
STATUS_META = {
    "COMPLETE": {"color": "#4CAF50", "label": "Proved"},
    "COMPLETE_WITH_ERRORS": {"color": "#FA8072", "label": "Returned with sorry"},
    "CANCELED": {"color": "#BDBDBD", "label": "Canceled"},
    "FAILED": {"color": "#616161", "label": "Failed"},
}
# Canonical order for stacking / legend
STATUS_ORDER = ["COMPLETE", "COMPLETE_WITH_ERRORS", "CANCELED", "FAILED"]


async def fetch_all_projects():
    """Page through Project.list_projects and return all projects."""
    all_projects = []
    next_key = None
    while True:
        projects, next_key = await Project.list_projects(
            limit=100, pagination_key=next_key
        )
        all_projects.extend(projects)
        if next_key is None:
            break
    return all_projects


def strip_tz(dt):
    """Return a naive datetime (strip tzinfo if present)."""
    if dt is not None and dt.tzinfo is not None:
        return dt.replace(tzinfo=None)
    return dt


def main():
    # --- Fetch and filter ---
    all_projects = asyncio.run(fetch_all_projects())
    gv_projects = [
        p for p in all_projects if strip_tz(p.created_at) >= GV_START
    ]

    total = len(gv_projects)
    print(f"Total GV-era projects: {total}")

    # --- Tally by status ---
    status_counts = Counter()
    daily_status = defaultdict(Counter)  # date -> Counter(status)

    for p in gv_projects:
        status_val = p.status.value if hasattr(p.status, "value") else str(p.status)
        status_counts[status_val] += 1
        day = strip_tz(p.created_at).date()
        daily_status[day][status_val] += 1

    for s in STATUS_ORDER:
        print(f"  {s}: {status_counts.get(s, 0)}")

    # --- Build figure ---
    fig, (ax_pie, ax_bar) = plt.subplots(1, 2, figsize=(12, 5))
    fig.suptitle(f"Aristotle ATP \u2014 {total} Submissions", fontsize=15, fontweight="bold")

    # ---- Left panel: pie chart ----
    pie_sizes = []
    pie_labels = []
    pie_colors = []
    for s in STATUS_ORDER:
        c = status_counts.get(s, 0)
        if c > 0:
            pie_sizes.append(c)
            meta = STATUS_META[s]
            pie_labels.append(f"{meta['label']} ({c})")
            pie_colors.append(meta["color"])

    wedges, texts, autotexts = ax_pie.pie(
        pie_sizes,
        labels=pie_labels,
        colors=pie_colors,
        autopct="%1.0f%%",
        startangle=140,
        textprops={"fontsize": 10},
    )
    for at in autotexts:
        at.set_fontsize(9)
        at.set_fontweight("bold")
    ax_pie.set_title("Outcome Breakdown", fontsize=12)

    # ---- Right panel: stacked bar chart ----
    all_dates = sorted(daily_status.keys())
    # Ensure full date range Mar 27 – Apr 4
    from datetime import timedelta

    start_date = datetime(2026, 3, 27).date()
    end_date = datetime(2026, 4, 4).date()
    date_range = []
    d = start_date
    while d <= end_date:
        date_range.append(d)
        d += timedelta(days=1)

    x_labels = [d.strftime("%b %d") for d in date_range]
    x_pos = range(len(date_range))

    bottoms = [0] * len(date_range)
    for s in STATUS_ORDER:
        heights = [daily_status[d].get(s, 0) for d in date_range]
        meta = STATUS_META[s]
        bars = ax_bar.bar(
            x_pos,
            heights,
            bottom=bottoms,
            color=meta["color"],
            label=meta["label"],
            edgecolor="white",
            linewidth=0.5,
        )
        # Label segments with count > 2
        for i, (h, b) in enumerate(zip(heights, bottoms)):
            if h > 2:
                ax_bar.text(
                    i,
                    b + h / 2,
                    str(h),
                    ha="center",
                    va="center",
                    fontsize=8,
                    fontweight="bold",
                )
        bottoms = [b + h for b, h in zip(bottoms, heights)]

    ax_bar.set_xticks(list(x_pos))
    ax_bar.set_xticklabels(x_labels, rotation=45, ha="right", fontsize=9)
    ax_bar.yaxis.set_major_locator(mticker.MaxNLocator(integer=True))
    ax_bar.set_ylabel("Submissions")
    ax_bar.set_title("Submissions per Day", fontsize=12)
    ax_bar.legend(loc="upper left", fontsize=8)

    plt.tight_layout(rect=[0, 0, 1, 0.93])
    out_path = OUT_DIR / "aristotle_outcomes_gv.png"
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved to {out_path}")


if __name__ == "__main__":
    main()
