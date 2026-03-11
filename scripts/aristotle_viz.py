#!/usr/bin/env python3
"""Visualize Aristotle automated theorem prover integration.

Reads project data from Aristotle/Landau/aristotle-out/landau_projects.json
and solution analysis from Aristotle/Landau/aristotle-out/solution_analysis.json.

To refresh the data, run:
  source .env && python3 scripts/aristotle_fetch.py
"""

import json
import os
from collections import Counter
from datetime import datetime, timedelta, timezone

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROJECTS_FILE = os.path.join(REPO, "Aristotle", "Landau", "aristotle-out", "landau_projects.json")
SOLUTIONS_FILE = os.path.join(REPO, "Aristotle", "Landau", "aristotle-out", "solution_analysis.json")
OUT_PNG = os.path.join(REPO, "scripts", "aristotle_outcomes.png")

PT = timezone(timedelta(hours=-7))


def classify(project, sol_by_id):
    """Classify a project into an outcome category."""
    pid = project["project_id"]
    status = project["status"]

    if "FAILED" in status or "NOT_STARTED" in status:
        return "Failed / not started"

    sol = sol_by_id.get(pid)
    if not sol:
        return "Failed / not started"
    if sol.get("has_negation"):
        return "Statement disproved"
    if sol.get("has_sorry"):
        return "Returned with sorry"
    return "Proved"


def main():
    with open(PROJECTS_FILE) as f:
        projects = json.load(f)
    with open(SOLUTIONS_FILE) as f:
        solutions = json.load(f)

    sol_by_id = {s["id"]: s for s in solutions}

    # Classify all projects
    outcomes = []
    for p in projects:
        cat = classify(p, sol_by_id)
        outcomes.append((p, cat))

    cats = Counter(cat for _, cat in outcomes)
    print(f"Total Landau submissions: {len(projects)}")
    for cat, count in cats.most_common():
        print(f"  {cat}: {count}")

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.dates as mdates
    import numpy as np

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13, 5),
                                    gridspec_kw={"width_ratios": [1.3, 1]})

    # ── Left: stacked bar chart by day ──
    order = [
        ("Proved", "#2ecc71"),
        ("Statement disproved", "#f39c12"),
        ("Returned with sorry", "#e74c3c"),
        ("Failed / not started", "#95a5a6"),
    ]

    # Group by date
    dates_all = sorted(set(p["created_at"][:10] for p in projects))
    day_counts = {name: [] for name, _ in order}
    for day in dates_all:
        day_outcomes = [cat for p, cat in outcomes if p["created_at"][:10] == day]
        for name, _ in order:
            day_counts[name].append(day_outcomes.count(name))

    x = np.arange(len(dates_all))
    width = 0.6
    bottom = np.zeros(len(dates_all))

    for name, color in order:
        vals = np.array(day_counts[name])
        if vals.sum() > 0:
            ax1.bar(x, vals, width, bottom=bottom, label=name, color=color, alpha=0.85)
            bottom += vals

    ax1.set_xticks(x)
    ax1.set_xticklabels([d[5:] for d in dates_all], rotation=45, ha="right", fontsize=8)
    ax1.set_xlabel("")
    ax1.set_ylabel("Submissions")
    ax1.set_title("Submissions per Day")
    ax1.legend(fontsize=8, loc="upper left")
    ax1.grid(True, axis="y", alpha=0.3)

    # ── Right: donut chart of outcomes ──
    labels = []
    counts = []
    colors = []
    for name, color in order:
        c = cats.get(name, 0)
        if c > 0:
            labels.append(f"{name}\n({c})")
            counts.append(c)
            colors.append(color)

    wedges, texts, autotexts = ax2.pie(
        counts, labels=labels, colors=colors,
        autopct="%1.0f%%", startangle=90,
        textprops={"fontsize": 9},
        pctdistance=0.75,
        wedgeprops=dict(width=0.5),
    )
    for t in autotexts:
        t.set_fontweight("bold")
        t.set_fontsize(10)
    ax2.set_title("Overall Outcomes")

    fig.suptitle(
        f"Aristotle Integration: {len(projects)} Submissions for VML Steady-State Formalization",
        fontsize=12, fontweight="bold", y=1.01,
    )
    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150, bbox_inches="tight")
    print(f"\nWrote {OUT_PNG}")


if __name__ == "__main__":
    main()
