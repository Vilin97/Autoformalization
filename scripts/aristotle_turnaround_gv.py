#!/usr/bin/env python3
"""
Generate an Aristotle ATP turnaround-time chart for the Grothendieck Vanishing project.

Fetches all projects created on or after 2026-03-27, computes turnaround
(last_updated_at - created_at), and produces a two-panel figure:
  Left  — stacked histogram of turnaround by outcome
  Right — median turnaround bar chart by outcome
"""

import asyncio
import os
from datetime import datetime

os.environ["ARISTOTLE_API_KEY"] = "arstl_JpLO92RXUx_X6rpIn78M8_ksUhFgUAbdqZKQ4gNBLxs"

import matplotlib.pyplot as plt
import numpy as np
from aristotlelib import Project

# ── Configuration ──────────────────────────────────────────────────────────

GV_CUTOFF = datetime(2026, 3, 27)
OUTPUT_PATH = "/Users/vasil/Github/aristotle/artifacts/aristotle_turnaround_gv.png"

STATUS_COLORS = {
    "COMPLETE": "green",
    "COMPLETE_WITH_ERRORS": "salmon",
    "CANCELED": "gray",
    "FAILED": "darkgray",
}

# ── Data collection ───────────────────────────────────────────────────────

async def fetch_all_projects():
    """Paginate through all projects and return those in the GV era."""
    all_projects = []
    next_key = None
    while True:
        projects, next_key = await Project.list_projects(
            limit=100, pagination_key=next_key
        )
        if not projects:
            break
        for p in projects:
            if p.created_at is None or p.last_updated_at is None:
                continue
            created = p.created_at.replace(tzinfo=None)
            if created >= GV_CUTOFF:
                all_projects.append(p)
        # If the oldest project in this page is before our cutoff, stop
        oldest = min(
            (p.created_at.replace(tzinfo=None) for p in projects if p.created_at),
            default=None,
        )
        if oldest is not None and oldest < GV_CUTOFF:
            break
        if next_key is None:
            break
    return all_projects


def compute_turnarounds(projects):
    """Return {status: [turnaround_hours, ...]}."""
    data = {}
    for p in projects:
        status = p.status.value if p.status else "UNKNOWN"
        created = p.created_at.replace(tzinfo=None)
        updated = p.last_updated_at.replace(tzinfo=None)
        hours = (updated - created).total_seconds() / 3600.0
        data.setdefault(status, []).append(hours)
    return data


# ── Plotting ──────────────────────────────────────────────────────────────

def make_figure(turnarounds):
    fig, (ax_hist, ax_bar) = plt.subplots(1, 2, figsize=(12, 5), dpi=150)
    fig.suptitle("Aristotle ATP \u2014 Turnaround Times", fontsize=14, fontweight="bold")

    # Determine the statuses that actually appear, in a stable order
    ordered_statuses = [
        s for s in ("COMPLETE", "COMPLETE_WITH_ERRORS", "CANCELED", "FAILED")
        if s in turnarounds
    ]
    # Add any unexpected statuses at the end
    for s in sorted(turnarounds):
        if s not in ordered_statuses:
            ordered_statuses.append(s)

    colors = [STATUS_COLORS.get(s, "steelblue") for s in ordered_statuses]

    # ── Left panel: stacked histogram ──────────────────────────────────
    max_hours = 120
    bin_edges = np.arange(0, max_hours + 2, 2)

    hist_data = []
    hist_labels = []
    hist_colors = []
    for s, c in zip(ordered_statuses, colors):
        vals = [min(h, max_hours) for h in turnarounds[s]]
        hist_data.append(vals)
        hist_labels.append(s)
        hist_colors.append(c)

    ax_hist.hist(
        hist_data,
        bins=bin_edges,
        stacked=True,
        color=hist_colors,
        label=hist_labels,
        edgecolor="white",
        linewidth=0.5,
    )
    ax_hist.set_xlabel("Turnaround time (hours)")
    ax_hist.set_ylabel("Number of jobs")
    ax_hist.legend(fontsize=8, loc="upper right")
    ax_hist.set_xlim(0, max_hours)

    # ── Right panel: median turnaround bar chart ───────────────────────
    medians = []
    for s in ordered_statuses:
        medians.append(float(np.median(turnarounds[s])))

    x_pos = np.arange(len(ordered_statuses))
    bars = ax_bar.bar(x_pos, medians, color=colors, edgecolor="white", linewidth=0.5)
    ax_bar.set_xticks(x_pos)
    ax_bar.set_xticklabels(
        [s.replace("_", "\n") for s in ordered_statuses], fontsize=8
    )
    ax_bar.set_ylabel("Median turnaround (hours)")

    # Add value labels on bars
    for bar, med in zip(bars, medians):
        ax_bar.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height() + 0.3,
            f"{med:.1f}h",
            ha="center",
            va="bottom",
            fontsize=9,
            fontweight="bold",
        )

    # Add count annotations on bars
    for i, (bar, s) in enumerate(zip(bars, ordered_statuses)):
        n = len(turnarounds[s])
        ax_bar.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height() / 2,
            f"n={n}",
            ha="center",
            va="center",
            fontsize=8,
            color="white",
            fontweight="bold",
        )

    fig.tight_layout(rect=[0, 0, 1, 0.94])
    return fig


# ── Main ──────────────────────────────────────────────────────────────────

async def main():
    print("Fetching projects from Aristotle API...")
    projects = await fetch_all_projects()
    print(f"  Found {len(projects)} GV-era projects (created >= {GV_CUTOFF.date()})")

    turnarounds = compute_turnarounds(projects)
    for status, vals in sorted(turnarounds.items()):
        med = float(np.median(vals))
        print(f"  {status}: {len(vals)} jobs, median {med:.1f}h")

    fig = make_figure(turnarounds)
    os.makedirs(os.path.dirname(OUTPUT_PATH), exist_ok=True)
    fig.savefig(OUTPUT_PATH)
    plt.close(fig)
    print(f"\nSaved to {OUTPUT_PATH}")


if __name__ == "__main__":
    asyncio.run(main())
