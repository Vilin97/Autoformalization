#!/usr/bin/env python3
"""Generate Lean LOC-over-time graphs for Aristotle/Landau/."""

import subprocess
import csv
import os
from datetime import datetime

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LANDAU_DIR = "Aristotle/Landau"
OUT_CSV = os.path.join(REPO, "scripts", "loc_history.csv")
OUT_PNG = os.path.join(REPO, "artifacts", "loc_history.png")
OUT_BREAKDOWN_PNG = os.path.join(REPO, "artifacts", "loc_breakdown.png")

# Notable events: (commit_hash_prefix, label, vertical_offset)
EVENTS = [
    ("944984b1f1", "Abstract proof\n(Sections 2\u20138)", 40),
    ("61eeb02", "Validate 22 axioms\non T\u00b3 = (\u211d/\u2124)\u00b3", 40),
    ("a445b2b364", "Coulomb kernel\nanalysis begins", -70),
    ("20d0f4b0fe", "Main theorem:\n0 sorry\u2019s", 40),
    ("96f389e62f", "Dead code removal\n(\u22123K lines)", 40),
    ("46b87fbc43", "Non-vacuousness\ncomplete", -70),
    ("5b62d21624", "Relax C\u221e \u2192 finite\norder differentiability", -70),
    ("62610d06ee", "Derive log growth\nbound via MVT", 40),
]

# File categories for the breakdown chart.
# "argument" = the mathematical proof chain (warm colors)
# "background" = supporting infrastructure (cool colors)
ARGUMENT_FILES = {
    "landau-steady-state.lean",  # monolithic precursor
    "Section2.lean", "Section3.lean", "Section3Helpers.lean",
    "Section4.lean", "Section5.lean", "Section6.lean",
    "Section7.lean", "Section8.lean", "Section9.lean",
    "VMLInputDerive.lean", "Theorem42.lean",
    "CoulombConcreteTheorem42.lean",
}

BACKGROUND_FILES = {
    "Defs.lean", "TorusInstance.lean", "TorusDefs.lean",
    "SchwartzDecayDefs.lean", "ConcreteTheorem42.lean",
    "VelocityDecayInstance.lean", "VelocityDecayHelpers.lean",
    "CoulombKernel.lean", "NewtonianPotential.lean",
    "CoulombFlux.lean", "CoulombFluxDiff.lean",
    "CoulombPSD.lean", "CoulombSpatialTransport.lean",
    "LandauMatrixDerivBound.lean",
    "DomainExperiments.lean",
}


def parse_iso(s):
    if s[-3] == ':' and (s[-6] == '+' or s[-6] == '-'):
        s = s[:-3] + s[-2:]
    return datetime.strptime(s, "%Y-%m-%dT%H:%M:%S%z")


def get_commits():
    result = subprocess.run(
        ["git", "log", "--format=%H %aI", "--reverse", "--", "Aristotle/Landau/"],
        capture_output=True, text=True, cwd=REPO,
    )
    commits = []
    for line in result.stdout.strip().split("\n"):
        if not line:
            continue
        parts = line.split(" ", 1)
        commits.append((parts[0], parts[1]))
    return commits


def get_file_loc(commit_hash):
    """Return dict of {basename: loc} for all .lean files at commit.

    Excludes monolithic file when main/ exists (avoids double-counting).
    Also excludes aristotle-in/ submission files.
    """
    result = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", commit_hash, "--", LANDAU_DIR],
        capture_output=True, text=True, cwd=REPO,
    )
    files = [f for f in result.stdout.strip().split("\n")
             if f.endswith(".lean") and "/aristotle-in/" not in f]
    has_main = any("/main/" in f for f in files)

    loc = {}
    for filepath in files:
        if has_main and "/main/" not in filepath:
            continue
        blob = subprocess.run(
            ["git", "show", f"{commit_hash}:{filepath}"],
            capture_output=True, text=True, cwd=REPO,
        )
        basename = os.path.basename(filepath)
        loc[basename] = loc.get(basename, 0) + len(blob.stdout.split("\n"))
    return loc


def main():
    commits = get_commits()
    print(f"Found {len(commits)} commits")

    rows = []  # (timestamp, total_loc, hash, file_loc_dict)
    prev_date = None
    for h, timestamp in commits:
        file_loc = get_file_loc(h)
        total = sum(file_loc.values())
        rows.append((timestamp, total, h, file_loc))
        date = timestamp[:10]
        if date != prev_date:
            print(f"  {date}: {total} LOC ({len(file_loc)} files)")
            prev_date = date

    # Write CSV (total only)
    with open(OUT_CSV, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["timestamp", "loc"])
        for r in rows:
            w.writerow([r[0], r[1]])
    print(f"Wrote {OUT_CSV}")

    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import matplotlib.dates as mdates
        import numpy as np
    except ImportError:
        print("matplotlib not available; CSV written, skip PNG")
        return

    dates = [parse_iso(r[0]) for r in rows]
    locs = [r[1] for r in rows]
    hashes = [r[2] for r in rows]

    # ── Chart 1: total LOC with event annotations ──
    fig, ax = plt.subplots(figsize=(10, 5))
    ax.plot(dates, locs, color="#2563eb", linewidth=2)
    ax.fill_between(dates, locs, alpha=0.1, color="#2563eb")
    ax.set_xlabel("")
    ax.set_ylabel("Lines of Lean code")
    ax.set_title("Formalization Progress: Lines of Lean 4 Code")
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=1))
    fig.autofmt_xdate()
    ax.set_ylim(bottom=0, top=max(locs) * 1.25)
    ax.grid(True, alpha=0.3)

    for prefix, label, y_offset in EVENTS:
        for i, h in enumerate(hashes):
            if h.startswith(prefix):
                ax.annotate(
                    label, xy=(dates[i], locs[i]),
                    xytext=(0, y_offset), textcoords="offset points",
                    fontsize=8, fontweight="bold", ha="center",
                    va="bottom" if y_offset > 0 else "top",
                    arrowprops=dict(arrowstyle="->", color="#666",
                                    connectionstyle="arc3,rad=0.2"),
                    bbox=dict(boxstyle="round,pad=0.3", facecolor="white",
                              edgecolor="#ccc", alpha=0.9),
                )
                break

    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150)
    print(f"Wrote {OUT_PNG}")

    # ── Chart 2: stacked area by grouped file category ──

    # Groups: coarser than individual files for a clean legend.
    # Each group: (display_name, set_of_basenames, category)
    GROUPS = [
        # Background (blues) — bottom of stack
        ("Defs", {"Defs.lean"}, "bg"),
        ("TorusInstance", {"TorusInstance.lean", "TorusDefs.lean"}, "bg"),
        ("Coulomb kernel files", {
            "CoulombKernel.lean", "NewtonianPotential.lean",
            "CoulombFlux.lean", "CoulombFluxDiff.lean",
            "CoulombPSD.lean", "CoulombSpatialTransport.lean",
            "LandauMatrixDerivBound.lean",
        }, "bg"),
        ("Decay & helpers", {
            "VelocityDecayInstance.lean", "VelocityDecayHelpers.lean",
            "SchwartzDecayDefs.lean", "ConcreteTheorem42.lean",
            "DomainExperiments.lean",
        }, "bg"),
        # Argument (reds) — top of stack
        ("Sections 2\u20138", {
            "Section2.lean", "Section3.lean", "Section3Helpers.lean",
            "Section4.lean", "Section5.lean", "Section6.lean",
            "Section7.lean", "Section8.lean", "Section9.lean",
        }, "arg"),
        ("VMLInputDerive", {"VMLInputDerive.lean"}, "arg"),
        ("Theorem42", {"Theorem42.lean"}, "arg"),
        ("CoulombConcreteTheorem42", {"CoulombConcreteTheorem42.lean"}, "arg"),
        ("Monolithic (pre-split)", {"landau-steady-state.lean"}, "arg"),
    ]

    # Build grouped time series
    group_series = {}
    for name, fileset, cat in GROUPS:
        series = []
        for _, _, _, floc in rows:
            series.append(sum(floc.get(f, 0) for f in fileset))
        group_series[name] = series

    # Colors
    bg_groups = [g for g in GROUPS if g[2] == "bg"]
    arg_groups = [g for g in GROUPS if g[2] == "arg"]
    blues = plt.cm.Blues(np.linspace(0.3, 0.7, max(len(bg_groups), 1)))
    reds = plt.cm.Reds(np.linspace(0.3, 0.8, max(len(arg_groups), 1)))

    ordered_names = [g[0] for g in GROUPS]
    colors = []
    bi, ri = 0, 0
    for name, _, cat in GROUPS:
        if cat == "bg":
            colors.append(blues[bi]); bi += 1
        else:
            colors.append(reds[ri]); ri += 1

    fig2, ax2 = plt.subplots(figsize=(12, 5.5))
    y_stack = np.array([group_series[n] for n in ordered_names])
    ax2.stackplot(dates, y_stack, labels=ordered_names, colors=colors, alpha=0.85)
    ax2.set_xlabel("")
    ax2.set_ylabel("Lines of Lean code")
    ax2.set_title("LOC by File Group: Infrastructure (blue) vs Proof Chain (red)")
    ax2.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax2.xaxis.set_major_locator(mdates.DayLocator(interval=1))
    fig2.autofmt_xdate()
    ax2.set_ylim(bottom=0)
    ax2.grid(True, alpha=0.3)

    # Legend outside on right, skip groups that never exceed 50 LOC
    handles, labels = ax2.get_legend_handles_labels()
    filtered = [(h, l) for h, l, n in zip(handles, labels, ordered_names)
                if max(group_series[n]) > 50]
    if filtered:
        fh, fl = zip(*filtered)
        ax2.legend(fh, fl, loc="center left", bbox_to_anchor=(1.01, 0.5),
                   fontsize=8.5, framealpha=0.9)

    fig2.tight_layout()
    fig2.savefig(OUT_BREAKDOWN_PNG, dpi=150)
    print(f"Wrote {OUT_BREAKDOWN_PNG}")


if __name__ == "__main__":
    main()
