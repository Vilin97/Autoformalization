#!/usr/bin/env python3
"""Generate a Lean LOC-over-time graph for Aristotle/Landau/."""

import subprocess
import csv
import os

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LANDAU_DIR = "Aristotle/Landau"
OUT_CSV = os.path.join(REPO, "scripts", "loc_history.csv")
OUT_PNG = os.path.join(REPO, "scripts", "loc_history.png")

# Notable events: (commit_hash_prefix, label, vertical_offset)
# vertical_offset adjusts label placement to avoid overlap
EVENTS = [
    ("944984b1f1", "Abstract proof\n(Sections 2\u20138)", 40),
    ("61eeb02", "Validate 22 axioms\non T\u00b3 = (\u211d/\u2124)\u00b3", 40),
    ("a445b2b364", "Coulomb kernel\nanalysis begins", -70),
    ("20d0f4b0fe", "Main theorem:\n0 sorry\u2019s", 40),
    ("96f389e62f", "Dead code removal\n(\u22123K lines)", 40),
    ("46b87fbc43", "Non-vacuousness\ncomplete", -70),
]


def get_commits():
    """Get all commits touching Landau/ with full timestamps, oldest first."""
    result = subprocess.run(
        ["git", "log", "--format=%H %aI", "--reverse", "--", "Aristotle/Landau/"],
        capture_output=True, text=True, cwd=REPO,
    )
    commits = []
    for line in result.stdout.strip().split("\n"):
        if not line:
            continue
        parts = line.split(" ", 1)
        commits.append((parts[0], parts[1]))  # hash, full ISO timestamp
    return commits


def count_lean_loc(commit_hash):
    """Count total Lean LOC in Aristotle/Landau/ at a given commit.

    Excludes the monolithic landau-steady-state.lean when main/ already exists,
    since it was duplicated code during the transition.
    """
    result = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", commit_hash, "--", LANDAU_DIR],
        capture_output=True, text=True, cwd=REPO,
    )
    files = [f for f in result.stdout.strip().split("\n") if f.endswith(".lean")]
    has_main = any("/main/" in f for f in files)
    total = 0
    for filepath in files:
        if has_main and "/main/" not in filepath:
            continue  # skip monolithic file when main/ exists
        blob = subprocess.run(
            ["git", "show", f"{commit_hash}:{filepath}"],
            capture_output=True, text=True, cwd=REPO,
        )
        total += len(blob.stdout.split("\n"))
    return total


def parse_iso(s):
    """Parse ISO 8601 with timezone offset like 2026-03-02T15:40:39-08:00."""
    if s[-3] == ':' and (s[-6] == '+' or s[-6] == '-'):
        s = s[:-3] + s[-2:]
    from datetime import datetime
    return datetime.strptime(s, "%Y-%m-%dT%H:%M:%S%z")


def main():
    commits = get_commits()
    print(f"Found {len(commits)} commits")

    rows = []
    prev_date = None
    for i, (h, timestamp) in enumerate(commits):
        loc = count_lean_loc(h)
        rows.append((timestamp, loc, h))
        date = timestamp[:10]
        if date != prev_date:
            print(f"  {date}: {loc} LOC")
            prev_date = date

    # Write CSV
    with open(OUT_CSV, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["timestamp", "loc"])
        for r in rows:
            w.writerow([r[0], r[1]])
    print(f"Wrote {OUT_CSV}")

    # Plot
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import matplotlib.dates as mdates

        dates = [parse_iso(r[0]) for r in rows]
        locs = [r[1] for r in rows]
        hashes = [r[2] for r in rows]

        fig, ax = plt.subplots(figsize=(10, 5))
        ax.plot(dates, locs, color="#2563eb", linewidth=2)
        ax.fill_between(dates, locs, alpha=0.1, color="#2563eb")
        ax.set_xlabel("Date")
        ax.set_ylabel("Lines of Lean code")
        ax.set_title("Lean LOC in Aristotle/Landau/")
        ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
        ax.xaxis.set_major_locator(mdates.DayLocator(interval=1))
        fig.autofmt_xdate()
        ax.set_ylim(bottom=0, top=max(locs) * 1.25)
        ax.grid(True, alpha=0.3)

        # Add event annotations
        for prefix, label, y_offset in EVENTS:
            for i, h in enumerate(hashes):
                if h.startswith(prefix):
                    ax.annotate(
                        label,
                        xy=(dates[i], locs[i]),
                        xytext=(0, y_offset),
                        textcoords="offset points",
                        fontsize=8,
                        fontweight="bold",
                        ha="center",
                        va="bottom" if y_offset > 0 else "top",
                        arrowprops=dict(
                            arrowstyle="->",
                            color="#666",
                            connectionstyle="arc3,rad=0.2",
                        ),
                        bbox=dict(
                            boxstyle="round,pad=0.3",
                            facecolor="white",
                            edgecolor="#ccc",
                            alpha=0.9,
                        ),
                    )
                    break

        fig.tight_layout()
        fig.savefig(OUT_PNG, dpi=150)
        print(f"Wrote {OUT_PNG}")
    except ImportError:
        print("matplotlib not available; CSV written, skip PNG")


if __name__ == "__main__":
    main()
