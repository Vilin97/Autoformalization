#!/usr/bin/env python3
"""Visualize Aristotle ATP turnaround times for Landau-related projects.

Uses the same outcome categories as aristotle_viz.py:
  Proved / Statement disproved / Returned with sorry / Failed or not started
"""

import asyncio
import os
import statistics
from collections import defaultdict
from datetime import timedelta

from aristotlelib import Project

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT_PNG = os.path.join(REPO, "artifacts", "aristotle_turnaround.png")

LANDAU_KEYWORDS = [
    "landau", "section", "coulomb", "torus", "schwartz", "velocity",
    "lorentz", "force", "fderiv", "integral", "ibp", "fubini",
    "maxwell", "entropy", "decay", "killing", "harmonic", "curl",
    "divergence", "transport", "flux", "mulvec", "dotproduct",
]


def is_landau_related(project):
    text = ""
    if project.file_name:
        text += project.file_name.lower()
    if project.description:
        text += " " + project.description.lower()
    return any(kw in text for kw in LANDAU_KEYWORDS)


async def classify_project(project):
    """Classify using same logic as aristotle_viz.py: download solution, check content."""
    status = project.status.value if hasattr(project.status, "value") else str(project.status)

    if "FAILED" in status or "NOT_STARTED" in status:
        return "Failed / not started"

    # Download solution file and read its content
    try:
        solution_path = await project.get_solution()
        if solution_path is None:
            return "Failed / not started"
        import pathlib
        p = pathlib.Path(solution_path)
        if not p.exists():
            return "Failed / not started"
        content = p.read_text()
        if "Negation" in content or "negation" in content:
            return "Statement disproved"
        if "sorry" in content:
            return "Returned with sorry"
        return "Proved"
    except Exception:
        return "Failed / not started"


async def fetch_all_projects():
    all_projects = []
    pagination_key = None
    while True:
        projects, next_key = await Project.list_projects(
            pagination_key=pagination_key, limit=100
        )
        all_projects.extend(projects)
        if next_key is None or len(projects) == 0:
            break
        pagination_key = next_key
    return all_projects


async def amain():
    print("Fetching projects from Aristotle API...")
    all_projects = await fetch_all_projects()
    landau = [p for p in all_projects if is_landau_related(p)]
    print(f"Total: {len(all_projects)}, Landau-related: {len(landau)}")

    # Classify each project
    print("Classifying solutions...")
    data = []
    for i, p in enumerate(landau):
        if (i + 1) % 50 == 0:
            print(f"  {i+1}/{len(landau)}")
        category = await classify_project(p)
        turnaround = (p.last_updated_at - p.created_at).total_seconds() / 60  # minutes
        data.append({"turnaround_min": turnaround, "category": category})

    cats = defaultdict(list)
    for d in data:
        cats[d["category"]].append(d["turnaround_min"])

    for cat, vals in sorted(cats.items()):
        med = statistics.median(vals)
        print(f"  {cat}: {len(vals)} submissions, median {med:.0f} min")

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    # Category order and colors (same as aristotle_viz.py)
    order = [
        ("Proved", "#2ecc71"),
        ("Statement disproved", "#f39c12"),
        ("Returned with sorry", "#e74c3c"),
        ("Failed / not started", "#95a5a6"),
    ]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13, 5),
                                    gridspec_kw={"width_ratios": [1.3, 1]})

    # ── Left: histogram of turnaround times, stacked by category ──
    bins = np.concatenate([
        np.arange(0, 60, 5),       # 0-60 min in 5-min bins
        np.arange(60, 180, 15),     # 1-3 hours in 15-min bins
        np.arange(180, 960, 60),    # 3-16 hours in 1-hour bins
    ])

    hist_data = []
    hist_colors = []
    hist_labels = []
    for name, color in order:
        vals = cats.get(name, [])
        if vals:
            hist_data.append(vals)
            hist_colors.append(color)
            hist_labels.append(f"{name} ({len(vals)})")

    ax1.hist(hist_data, bins=bins, color=hist_colors, label=hist_labels,
             stacked=True, alpha=0.85, edgecolor="white", linewidth=0.3)

    all_times = [d["turnaround_min"] for d in data]
    med_all = statistics.median(all_times) if all_times else 0
    ax1.axvline(med_all, color="#2c3e50", linestyle="--", linewidth=2)
    ax1.text(med_all + 5, ax1.get_ylim()[1] * 0.9, f"Median: {med_all:.0f} min",
             fontsize=9, fontweight="bold", color="#2c3e50")

    ax1.set_xlabel("Turnaround time (minutes)")
    ax1.set_ylabel("Number of submissions")
    ax1.set_title("Turnaround Time Distribution")
    ax1.legend(fontsize=8, loc="upper right")
    ax1.grid(True, axis="y", alpha=0.3)

    # ── Right: median turnaround by category ──
    bar_cats = []
    bar_medians = []
    bar_colors = []
    bar_counts = []
    for name, color in order:
        vals = cats.get(name, [])
        if vals:
            bar_cats.append(name.replace(" / ", "/\n"))
            bar_medians.append(statistics.median(vals))
            bar_colors.append(color)
            bar_counts.append(len(vals))

    bars = ax2.bar(bar_cats, bar_medians, color=bar_colors, alpha=0.85, edgecolor="white")
    for bar, med, count in zip(bars, bar_medians, bar_counts):
        if med >= 60:
            label = f"{med/60:.1f}h"
        else:
            label = f"{med:.0f}m"
        ax2.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 2,
                 f"{label}\n(n={count})", ha="center", va="bottom", fontsize=9, fontweight="bold")

    ax2.set_ylabel("Median turnaround (minutes)")
    ax2.set_title("Median Turnaround by Outcome")
    ax2.grid(True, axis="y", alpha=0.3)

    total = len(data)
    fig.suptitle(
        f"Aristotle ATP: {total} Submissions, Median Turnaround {med_all:.0f} Minutes",
        fontsize=12, fontweight="bold", y=1.01,
    )
    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150, bbox_inches="tight")
    print(f"\nWrote {OUT_PNG}")


if __name__ == "__main__":
    asyncio.run(amain())
