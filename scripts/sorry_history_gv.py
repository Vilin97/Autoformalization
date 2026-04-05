#!/usr/bin/env python3
"""
Generate a sorry-count-over-time chart for the Grothendieck Vanishing project.

Walks through all git commits on wip/grothendieck-vanishing that touch
Aristotle/GrothendieckVanishing/main/*.lean, counts sorry/admit keywords
(excluding comments), and produces a matplotlib chart.
"""

import subprocess
import re
from datetime import datetime, timezone, timedelta
from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib.dates as mdates

REPO = Path("/Users/vasil/Github/aristotle")
OUT_DIR = REPO / "artifacts"
OUT_DIR.mkdir(parents=True, exist_ok=True)

PDT = timezone(timedelta(hours=-7))


def git(*args: str) -> str:
    """Run a git command in the repo and return stdout."""
    result = subprocess.run(
        ["git"] + list(args),
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    return result.stdout


def count_sorry_in_content(content: str) -> int:
    """Count sorry/admit keywords in Lean code, excluding comments."""
    count = 0
    in_block_comment = 0  # nesting depth
    for line in content.splitlines():
        stripped = line.strip()

        # Handle block comments (can nest in Lean 4)
        i = 0
        code_chars = []
        while i < len(stripped):
            if i + 1 < len(stripped):
                two = stripped[i : i + 2]
                if two == "/-":
                    in_block_comment += 1
                    i += 2
                    continue
                if two == "-/" and in_block_comment > 0:
                    in_block_comment -= 1
                    i += 2
                    continue
            if in_block_comment > 0:
                i += 1
                continue
            code_chars.append(stripped[i])
            i += 1

        if in_block_comment > 0:
            continue

        code_part = "".join(code_chars)

        # Remove line comments (-- to end of line)
        code_part = re.split(r"--", code_part)[0]

        # Count sorry and admit (word boundary, not sorry')
        count += len(re.findall(r"\b(?:sorry|admit)\b(?!')", code_part))

    return count


def collect_data():
    """Collect (datetime, sorry_count) for each commit."""
    # Get all commit hashes and dates in chronological order
    log_output = git(
        "log",
        "wip/grothendieck-vanishing",
        "--format=%H %aI",
        "--reverse",
        "--",
        "Aristotle/GrothendieckVanishing/main/*.lean",
    )

    data = []
    for line in log_output.strip().splitlines():
        if not line.strip():
            continue
        parts = line.split(None, 1)
        if len(parts) != 2:
            continue
        commit_hash, date_str = parts

        # Parse date
        dt = datetime.fromisoformat(date_str)

        # List lean files at this commit
        tree_output = git(
            "ls-tree", "-r", "--name-only", commit_hash,
            "--", "Aristotle/GrothendieckVanishing/main/",
        )
        lean_files = [
            f for f in tree_output.strip().splitlines()
            if f.endswith(".lean")
        ]

        # Count sorry's across all files
        total_sorry = 0
        for filepath in lean_files:
            content_result = subprocess.run(
                ["git", "show", f"{commit_hash}:{filepath}"],
                cwd=REPO,
                capture_output=True,
                text=True,
            )
            if content_result.returncode == 0:
                total_sorry += count_sorry_in_content(content_result.stdout)

        data.append((dt, total_sorry))

    return data


def make_chart(data):
    """Generate the sorry count chart."""
    dates = [d[0] for d in data]
    counts = [d[1] for d in data]

    fig, ax = plt.subplots(figsize=(12, 5))

    # Step plot with dots
    ax.step(dates, counts, where="post", color="#cc3333", linewidth=1.5,
            zorder=3)
    ax.plot(dates, counts, "o", color="#cc3333", markersize=2.5, zorder=4)

    # Fill below
    ax.fill_between(dates, counts, step="post", color="#cc3333", alpha=0.12)

    # Title and labels
    ax.set_title("Grothendieck Vanishing \u2014 Sorry Count",
                 fontsize=15, fontweight="bold", pad=12)
    ax.set_xlabel("Date (PDT)", fontsize=11)
    ax.set_ylabel("Number of sorry\u2019s", fontsize=11)

    # X-axis: Mar 27 - Apr 4
    ax.set_xlim(
        datetime(2026, 3, 27, 0, 0, tzinfo=PDT),
        datetime(2026, 4, 5, 0, 0, tzinfo=PDT),
    )
    ax.xaxis.set_major_locator(mdates.DayLocator(tz=PDT))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=PDT))
    plt.setp(ax.get_xticklabels(), rotation=30, ha="right", fontsize=9)

    # Y-axis
    ax.set_ylim(-0.5, max(counts) + 3)
    ax.yaxis.set_major_locator(plt.MaxNLocator(integer=True))

    # Grid
    ax.grid(True, color="gray", alpha=0.3, linestyle="-", linewidth=0.5)
    ax.set_axisbelow(True)

    # --- Annotations ---

    # Find the peak (24 sorry's on Apr 1)
    peak_idx = max(range(len(counts)), key=lambda i: counts[i])
    peak_date = dates[peak_idx]
    peak_val = counts[peak_idx]

    ax.annotate(
        f"Regression: automated prover\n(peak {peak_val} sorry\u2019s)",
        xy=(peak_date, peak_val),
        xytext=(datetime(2026, 4, 1, 20, 0, tzinfo=PDT), peak_val - 1),
        fontsize=8,
        color="#990000",
        arrowprops=dict(arrowstyle="->", color="#990000", lw=1),
        ha="left", va="top",
    )

    # Find the "decompose sorry's" peak on Mar 28 (~7)
    mar28_data = [(d, c) for d, c in data
                  if d.date() == datetime(2026, 3, 28).date()]
    if mar28_data:
        mar28_peak = max(mar28_data, key=lambda x: x[1])
        ax.annotate(
            f"Sub-lemma decomposition\n({mar28_peak[1]} sorry\u2019s)",
            xy=(mar28_peak[0], mar28_peak[1]),
            xytext=(datetime(2026, 3, 28, 18, 0, tzinfo=PDT), mar28_peak[1] + 4),
            fontsize=8,
            color="#666666",
            arrowprops=dict(arrowstyle="->", color="#666666", lw=1),
            ha="center", va="bottom",
        )

    # Drop to 2 around Mar 30
    mar30_data = [(d, c) for d, c in data
                  if d.date() == datetime(2026, 3, 30).date()]
    if mar30_data:
        mar30_point = mar30_data[-1]
        ax.annotate(
            f"Stable at {mar30_point[1]}",
            xy=(mar30_point[0], mar30_point[1]),
            xytext=(datetime(2026, 3, 30, 18, 0, tzinfo=PDT), mar30_point[1] + 5),
            fontsize=8,
            color="#666666",
            arrowprops=dict(arrowstyle="->", color="#666666", lw=1),
            ha="center", va="bottom",
        )

    # Restored to 2 on Apr 1 afternoon
    apr1_restored = [(d, c) for d, c in data
                     if d.date() == datetime(2026, 4, 1).date()
                     and d.hour >= 13 and c <= 3]
    if apr1_restored:
        restore_point = apr1_restored[0]
        ax.annotate(
            f"Restored to {restore_point[1]}",
            xy=(restore_point[0], restore_point[1]),
            xytext=(datetime(2026, 4, 1, 7, 0, tzinfo=PDT), 10),
            fontsize=8,
            color="#336633",
            arrowprops=dict(arrowstyle="->", color="#336633", lw=1),
            ha="center", va="bottom",
        )

    # Drop to 1 on Apr 2
    apr2_1 = [(d, c) for d, c in data
              if d.date() == datetime(2026, 4, 2).date() and c == 1]
    if apr2_1:
        ax.annotate(
            "Down to 1",
            xy=(apr2_1[0][0], 1),
            xytext=(datetime(2026, 4, 2, 6, 0, tzinfo=PDT), 7),
            fontsize=8,
            color="#336633",
            arrowprops=dict(arrowstyle="->", color="#336633", lw=1),
            ha="center", va="bottom",
        )

    # Final 0 on Apr 4
    final = data[-1]
    ax.annotate(
        "0 sorry\u2019s \u2014 DONE",
        xy=(final[0], final[1]),
        xytext=(datetime(2026, 4, 4, 6, 0, tzinfo=PDT), 4),
        fontsize=9,
        fontweight="bold",
        color="#006600",
        arrowprops=dict(arrowstyle="->", color="#006600", lw=1.2),
        ha="center", va="bottom",
    )

    # Horizontal line at y=0
    ax.axhline(y=0, color="green", linewidth=0.8, alpha=0.5, linestyle="--")

    fig.tight_layout()
    out_path = OUT_DIR / "sorry_history_gv.png"
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    print(f"Saved to {out_path}")
    plt.close(fig)


def main():
    print("Collecting sorry counts from git history...")
    data = collect_data()
    print(f"Collected {len(data)} data points.")
    if data:
        print(f"  Date range: {data[0][0].isoformat()} to {data[-1][0].isoformat()}")
        print(f"  Sorry range: {min(c for _, c in data)} to {max(c for _, c in data)}")
    make_chart(data)


if __name__ == "__main__":
    main()
