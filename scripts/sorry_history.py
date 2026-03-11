#!/usr/bin/env python3
"""Visualize the number of sorry's in the Lean codebase over time."""

import subprocess
import os
from datetime import datetime, timezone, timedelta

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT_PNG = os.path.join(REPO, "scripts", "sorry_history.png")
LANDAU_DIR = "Aristotle/Landau"
PDT = timezone(timedelta(hours=-7))


def parse_iso(s):
    if s[-3] == ':' and (s[-6] == '+' or s[-6] == '-'):
        s = s[:-3] + s[-2:]
    return datetime.strptime(s, "%Y-%m-%dT%H:%M:%S%z").astimezone(PDT)


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


def has_main_dir(commit_hash):
    """Check if Aristotle/Landau/main/ exists at this commit."""
    result = subprocess.run(
        ["git", "ls-tree", "--name-only", commit_hash, "--", "Aristotle/Landau/main/"],
        capture_output=True, text=True, cwd=REPO,
    )
    return bool(result.stdout.strip())


def count_sorries(commit_hash):
    """Count actual sorry tactic usages at a given commit.

    Only counts in main/ (or the monolithic file before main/ existed).
    Excludes aristotle-in/, aristotle-out/, and non-.lean files.
    """
    if has_main_dir(commit_hash):
        search_path = "Aristotle/Landau/main/*.lean"
    else:
        search_path = "Aristotle/Landau/*.lean"

    result = subprocess.run(
        ["git", "grep", "-w", "sorry", commit_hash, "--", search_path],
        capture_output=True, text=True, cwd=REPO,
    )
    if result.returncode != 0:
        return 0

    count = 0
    for line in result.stdout.strip().split("\n"):
        if not line:
            continue
        parts = line.split(":", 2)
        if len(parts) < 3:
            continue
        content = parts[2].strip()
        if content.startswith("--"):
            continue
        if "sorry'" in line or "sorry's" in line or "0 sorry" in line:
            continue
        count += 1
    return count


def main():
    commits = get_commits()
    print(f"Found {len(commits)} commits to analyze")

    dates = []
    sorries = []
    prev_date = None

    for i, (h, timestamp) in enumerate(commits):
        dt = parse_iso(timestamp)
        n = count_sorries(h)
        dates.append(dt)
        sorries.append(n)

        date_str = timestamp[:10]
        if date_str != prev_date:
            print(f"  [{i+1}/{len(commits)}] {date_str}: {n} sorry's")
            prev_date = date_str

    # Find notable events for labeling
    events = []  # (index, label, y_offset)

    # 1. Peak sorry count in first wave (Mar 1-4): abstract proof skeleton
    first_wave = [(i, s) for i, s in enumerate(sorries) if dates[i] < datetime(2026, 3, 5, tzinfo=PDT)]
    if first_wave:
        peak_idx, peak_val = max(first_wave, key=lambda x: x[1])
        events.append((peak_idx, f"Peak: {peak_val} sorry's\n(abstract proof skeleton)", 30))

    # 2. Big drop: monolithic split + Aristotle proofs (Mar 3→4)
    for i in range(1, len(sorries)):
        if dates[i] >= datetime(2026, 3, 3, 18, tzinfo=PDT) and dates[i] < datetime(2026, 3, 4, 12, tzinfo=PDT):
            if sorries[i-1] - sorries[i] >= 10:
                events.append((i, f"Monolithic split\n+ Aristotle proofs\n({sorries[i-1]}→{sorries[i]})", -55))
                break

    # 3. Mar 5 evening spike: TorusInstance added with sorry's for 22 axioms
    for i in range(1, len(sorries)):
        if (dates[i] >= datetime(2026, 3, 5, 20, tzinfo=PDT)
                and dates[i] < datetime(2026, 3, 6, tzinfo=PDT)
                and sorries[i] - sorries[i-1] >= 10):
            events.append((i, f"TorusInstance added\n(+{sorries[i] - sorries[i-1]} sorry's\nfor 22 axioms)", 35))
            break

    # 4. First time 0 sorry's reached (brief, Mar 8)
    for i in range(1, len(sorries)):
        if sorries[i] == 0 and sorries[i-1] > 0:
            events.append((i, "First 0 sorry's\n(abstract theorem)", -70))
            break

    # 4b. Second time 0 sorry's reached (Mar 8, before CoulombConcrete spike)
    zero_count = 0
    for i in range(1, len(sorries)):
        if sorries[i] == 0 and sorries[i-1] > 0:
            zero_count += 1
            if zero_count == 2:
                events.append((i, "0 sorry's again\n(torus + decay closed)", 35))
                break

    # 5. Coulomb spike: CoulombConcreteTheorem42 added
    max_jump = 0
    max_jump_idx = None
    for i in range(1, len(sorries)):
        jump = sorries[i] - sorries[i-1]
        if jump > max_jump:
            max_jump = jump
            max_jump_idx = i
    if max_jump_idx and max_jump >= 20:
        events.append((max_jump_idx, f"CoulombConcrete\nadded (+{max_jump} sorry's)", 25))

    # 6. Stale file cleanup (43→6): split into 6 files, delete stale Aristotle artifacts
    for i in range(1, len(sorries)):
        if sorries[i-1] >= 40 and sorries[i] <= 10 and sorries[i-1] - sorries[i] >= 30:
            events.append((i, f"File split + stale\nartifact cleanup\n({sorries[i-1]}→{sorries[i]})", -60))
            break

    # 7. Coulomb sorry sprint (6→0 on Mar 9 evening)
    for i in range(1, len(sorries)):
        if (sorries[i] == 0 and sorries[i-1] > 0
                and dates[i] >= datetime(2026, 3, 9, 20, tzinfo=PDT)
                and dates[i] < datetime(2026, 3, 10, 6, tzinfo=PDT)):
            events.append((i, "0 sorry's\n(Coulomb proved)", 40))
            break

    # 8. Non-vacuousness spike (small bump near end)
    for i in range(len(sorries) - 1, 0, -1):
        if sorries[i] > 0 and i > 0 and sorries[i-1] == 0 and dates[i] > datetime(2026, 3, 10, tzinfo=PDT):
            events.append((i, f"Non-vacuousness\n(+{sorries[i]})", 45))
            break

    # 9. Final 0 sorry's (last time)
    for i in range(len(sorries) - 1, -1, -1):
        if sorries[i] == 0 and any(s > 0 for s in sorries[max(0,i-5):i]):
            while i > 0 and sorries[i - 1] == 0:
                i -= 1
            events.append((i, "0 sorry's (final)", -50))
            break

    # Plot
    fig, ax = plt.subplots(figsize=(14, 5.5))
    ax.plot(dates, sorries, color="#e05530", linewidth=2)
    ax.fill_between(dates, sorries, alpha=0.15, color="#e05530")

    # Annotate events
    for idx, label, y_offset in events:
        ax.annotate(
            label, xy=(dates[idx], sorries[idx]),
            xytext=(0, y_offset), textcoords="offset points",
            fontsize=8, fontweight="bold", ha="center",
            va="bottom" if y_offset > 0 else "top",
            arrowprops=dict(arrowstyle="->", color="#666",
                            connectionstyle="arc3,rad=0.2"),
            bbox=dict(boxstyle="round,pad=0.3", facecolor="#fff3e0",
                      edgecolor="#e05530", alpha=0.9),
        )

    ax.set_ylabel("Number of sorry's")
    ax.set_title("Sorry Count Over Time", fontsize=13, fontweight="bold")
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=PDT))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=1, tz=PDT))
    fig.autofmt_xdate()
    ax.set_ylim(bottom=0, top=max(sorries) * 1.3 if max(sorries) > 0 else 5)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150)
    print(f"\nWrote {OUT_PNG}")


if __name__ == "__main__":
    main()
