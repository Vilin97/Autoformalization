#!/usr/bin/env python3
"""Generate a tool usage chart for the Grothendieck Vanishing project.

Reads Claude Code session logs (.jsonl) and produces a two-panel figure:
  Left  — horizontal bar chart of total calls per tool category
  Right — stacked bar chart of daily tool calls by category
"""

import json
import os
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib.dates as mdates
import numpy as np

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------
SESSION_DIR = Path.home() / ".claude/projects/-Users-vasil-Github-aristotle"
OUT = "/Users/vasil/Github/aristotle/artifacts/tool_use_gv.png"

# Only include session files modified on or after this date
CUTOFF_DATE = datetime(2026, 3, 27)

# PDT = UTC-7
PDT = timezone(timedelta(hours=-7))

# Tool categories (order matters for legend/color assignment)
CATEGORY_ORDER = [
    "Reading",
    "Editing",
    "Lean LSP",
    "Lean Explore",
    "Aristotle",
    "Axle",
    "Agent/Task",
    "Other",
]

# Warm colors for editing/reading, cool colors for Lean tools, muted for the rest
CATEGORY_COLORS = {
    "Reading":      "#e8590c",  # warm orange-red
    "Editing":      "#f76707",  # warm orange
    "Lean LSP":     "#1971c2",  # cool blue
    "Lean Explore": "#4dabf7",  # light blue
    "Aristotle":    "#099268",  # teal
    "Axle":         "#20c997",  # mint
    "Agent/Task":   "#845ef7",  # purple
    "Other":        "#868e96",  # gray
}


def categorize(tool_name: str) -> str:
    """Map a tool name to its category."""
    if tool_name in ("Edit", "Write"):
        return "Editing"
    if tool_name in ("Read", "Bash", "Grep", "Glob"):
        return "Reading"
    if tool_name.startswith("mcp__lean-lsp__"):
        return "Lean LSP"
    if tool_name.startswith("mcp__lean-explore__"):
        return "Lean Explore"
    if tool_name.startswith("mcp__aristotle__"):
        return "Aristotle"
    if tool_name.startswith("mcp__axle-mcp-server__"):
        return "Axle"
    if tool_name in ("Agent", "TaskCreate", "TaskUpdate", "TaskGet", "Skill", "ToolSearch"):
        return "Agent/Task"
    return "Other"


def collect_tool_calls():
    """Parse all qualifying session logs and return (total_by_cat, daily_by_cat)."""
    total = defaultdict(int)          # category -> count
    daily = defaultdict(lambda: defaultdict(int))  # date -> category -> count

    for fpath in SESSION_DIR.glob("*.jsonl"):
        # Filter by file modification time
        mtime = datetime.fromtimestamp(fpath.stat().st_mtime)
        if mtime < CUTOFF_DATE:
            continue

        with open(fpath, "r") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except json.JSONDecodeError:
                    continue

                if obj.get("type") != "assistant":
                    continue

                timestamp_str = obj.get("timestamp")
                if not timestamp_str:
                    continue

                # Parse the ISO timestamp and convert to PDT date
                try:
                    ts = datetime.fromisoformat(timestamp_str).astimezone(PDT)
                except (ValueError, TypeError):
                    continue
                day = ts.date()

                content = obj.get("message", {}).get("content", [])
                if not isinstance(content, list):
                    continue

                for block in content:
                    if isinstance(block, dict) and block.get("type") == "tool_use":
                        name = block.get("name", "unknown")
                        cat = categorize(name)
                        total[cat] += 1
                        daily[day][cat] += 1

    return total, daily


def build_figure(total, daily):
    """Create and save the two-panel figure."""
    fig, (ax_bar, ax_stack) = plt.subplots(1, 2, figsize=(14, 6), dpi=150)
    fig.suptitle("Tool Usage — Grothendieck Vanishing Project", fontsize=14, fontweight="bold")

    # --- Left panel: horizontal bar chart (sorted descending) ---
    cats_sorted = sorted(
        [c for c in CATEGORY_ORDER if total.get(c, 0) > 0],
        key=lambda c: total[c],
    )
    counts = [total[c] for c in cats_sorted]
    colors = [CATEGORY_COLORS[c] for c in cats_sorted]

    bars = ax_bar.barh(cats_sorted, counts, color=colors, edgecolor="white", linewidth=0.5)
    ax_bar.set_xlabel("Total tool calls")
    ax_bar.set_title("Total Calls by Category")
    ax_bar.grid(axis="x", color="#cccccc", linewidth=0.5)
    ax_bar.set_axisbelow(True)

    # Annotate counts
    for bar, count in zip(bars, counts):
        ax_bar.text(
            bar.get_width() + max(counts) * 0.01,
            bar.get_y() + bar.get_height() / 2,
            f"{count:,}",
            va="center",
            fontsize=9,
        )

    # --- Right panel: stacked bar chart by day ---
    if daily:
        all_days = sorted(daily.keys())
        day_labels = [d.strftime("%-m/%d") for d in all_days]

        # Only show categories that have nonzero totals
        active_cats = [c for c in CATEGORY_ORDER if total.get(c, 0) > 0]
        bottoms = np.zeros(len(all_days))

        for cat in active_cats:
            vals = [daily[d].get(cat, 0) for d in all_days]
            ax_stack.bar(
                day_labels, vals,
                bottom=bottoms,
                color=CATEGORY_COLORS[cat],
                edgecolor="white",
                linewidth=0.3,
                label=cat,
            )
            bottoms += np.array(vals)

        ax_stack.set_xlabel("Date")
        ax_stack.set_ylabel("Tool calls")
        ax_stack.set_title("Daily Tool Calls by Category")
        ax_stack.legend(loc="upper left", fontsize=8, framealpha=0.9)
        ax_stack.grid(axis="y", color="#cccccc", linewidth=0.5)
        ax_stack.set_axisbelow(True)
        plt.setp(ax_stack.get_xticklabels(), rotation=45, ha="right", fontsize=8)

    plt.tight_layout()
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    fig.savefig(OUT, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved: {OUT}")


def main():
    print(f"Scanning session logs in {SESSION_DIR} ...")
    total, daily = collect_tool_calls()

    grand_total = sum(total.values())
    print(f"Found {grand_total:,} tool calls across {len(daily)} days")
    for cat in CATEGORY_ORDER:
        if total.get(cat, 0) > 0:
            print(f"  {cat:15s}: {total[cat]:>6,}")

    build_figure(total, daily)


if __name__ == "__main__":
    main()
