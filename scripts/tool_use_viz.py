#!/usr/bin/env python3
"""Visualize Claude Code tool usage over the project."""

import json
import glob
import os
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SESSION_DIRS = [
    os.path.expanduser("~/.claude/projects/-Users-vasil-Github-aristotle/"),
    os.path.expanduser("~/.claude/projects/-home-vilin-aristotle/"),
    "/tmp/americano-sessions/",  # from university machine
]
OUT_PNG = os.path.join(REPO, "scripts", "tool_use.png")

PT = timezone(timedelta(hours=-7))  # PDT


def parse_ts(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(PT)


# Display groups: collapse MCP tools into categories
def tool_group(name):
    if name.startswith("mcp__lean-lsp__"):
        return "Lean LSP"
    if name.startswith("mcp__lean-lsp-mcp__"):
        return "Lean LSP"
    if name.startswith("mcp__axle__"):
        return "Axle"
    if name.startswith("mcp__gemini"):
        return "Gemini"
    return name


def load_tool_data():
    files = []
    for d in SESSION_DIRS:
        files.extend(glob.glob(os.path.join(d, "*.jsonl")))
    files = sorted(files)

    tool_counts = Counter()       # tool_name -> total count
    tool_by_day = defaultdict(Counter)  # date -> tool_group -> count
    tool_timestamps = []          # (timestamp, tool_name)

    for f in files:
        for line in open(f):
            line = line.strip()
            if not line:
                continue
            try:
                d = json.loads(line)
            except Exception:
                continue
            if d.get("type") != "assistant":
                continue
            ts = d.get("timestamp")
            if not ts:
                continue
            t = parse_ts(ts)
            content = d.get("message", {}).get("content", [])
            if not isinstance(content, list):
                continue
            for block in content:
                if isinstance(block, dict) and block.get("type") == "tool_use":
                    name = block.get("name", "unknown")
                    tool_counts[name] += 1
                    tool_timestamps.append((t, name))
                    day = t.date()
                    tool_by_day[day][tool_group(name)] += 1

    tool_timestamps.sort(key=lambda x: x[0])
    return tool_counts, tool_by_day, tool_timestamps


def main():
    tool_counts, tool_by_day, tool_timestamps = load_tool_data()

    total = sum(tool_counts.values())
    print(f"Total tool calls: {total:,}")
    print(f"\nBy tool:")
    for name, count in tool_counts.most_common():
        print(f"  {count:6d}  {name}")

    # Group stats
    grouped = Counter()
    for name, count in tool_counts.items():
        grouped[tool_group(name)] += count
    print(f"\nBy group:")
    for name, count in grouped.most_common():
        print(f"  {count:6d}  {name}")

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.dates as mdates
    import numpy as np

    fig, axes = plt.subplots(2, 2, figsize=(16, 10))

    # ── Top-left: bar chart of tool counts (grouped) ──
    ax1 = axes[0, 0]
    names = [n for n, _ in grouped.most_common()]
    counts = [c for _, c in grouped.most_common()]

    colors_map = {
        "Bash": "#e74c3c",
        "Read": "#3498db",
        "Edit": "#2ecc71",
        "Write": "#9b59b6",
        "Grep": "#f39c12",
        "Glob": "#1abc9c",
        "Agent": "#e67e22",
        "Lean LSP": "#34495e",
        "Skill": "#d35400",
        "ToolSearch": "#7f8c8d",
        "Axle": "#2c3e50",
        "Gemini": "#8e44ad",
    }
    bar_colors = [colors_map.get(n, "#95a5a6") for n in names]

    bars = ax1.barh(range(len(names)), counts, color=bar_colors, alpha=0.85)
    ax1.set_yticks(range(len(names)))
    ax1.set_yticklabels(names, fontsize=9)
    ax1.invert_yaxis()
    ax1.set_xlabel("Total calls")
    ax1.set_title(f"Tool Usage by Category ({total:,} total)")
    ax1.grid(True, axis="x", alpha=0.3)

    for bar, count in zip(bars, counts):
        ax1.text(bar.get_width() + total * 0.005, bar.get_y() + bar.get_height() / 2,
                 f"{count:,}", va="center", fontsize=8, fontweight="bold")

    # ── Top-right: stacked bar chart over time ──
    ax2 = axes[0, 1]

    all_days = sorted(tool_by_day.keys())
    # Pick top groups for stacking
    top_groups = [n for n, _ in grouped.most_common(8)]
    other_label = "Other"

    stacked_data = {}
    for g in top_groups:
        stacked_data[g] = [tool_by_day[day].get(g, 0) for day in all_days]
    # Other
    other_vals = []
    for day in all_days:
        other = sum(c for g, c in tool_by_day[day].items() if g not in top_groups)
        other_vals.append(other)
    if sum(other_vals) > 0:
        stacked_data[other_label] = other_vals
        top_groups.append(other_label)

    bottom = np.zeros(len(all_days))
    for g in top_groups:
        vals = np.array(stacked_data[g])
        color = colors_map.get(g, "#bdc3c7")
        ax2.bar(all_days, vals, bottom=bottom, label=g, color=color, alpha=0.85, width=0.8)
        bottom += vals

    ax2.set_ylabel("Tool calls per day")
    ax2.set_title("Tool Usage Over Time")
    ax2.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax2.xaxis.set_major_locator(mdates.DayLocator(interval=1))
    ax2.legend(fontsize=7, loc="upper left", ncol=2)
    ax2.grid(True, axis="y", alpha=0.3)
    fig.autofmt_xdate()

    # ── Bottom-left: cumulative tool calls over time ──
    ax3 = axes[1, 0]

    timestamps = [t for t, _ in tool_timestamps]
    cumulative = np.arange(1, len(timestamps) + 1)
    ax3.plot(timestamps, cumulative, color="#2563eb", linewidth=2)
    ax3.fill_between(timestamps, cumulative, alpha=0.1, color="#2563eb")
    ax3.set_ylabel("Cumulative tool calls")
    ax3.set_title(f"Cumulative Tool Usage ({total:,} total)")
    ax3.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=PT))
    ax3.xaxis.set_major_locator(mdates.DayLocator(interval=1, tz=PT))
    ax3.grid(True, alpha=0.3)

    # ── Bottom-right: detailed Lean LSP breakdown ──
    ax4 = axes[1, 1]

    lean_tools = Counter()
    for name, count in tool_counts.items():
        if name.startswith("mcp__lean-lsp"):
            short = name.split("__")[-1]
            lean_tools[short] += count

    if lean_tools:
        lean_names = [n for n, _ in lean_tools.most_common()]
        lean_counts = [c for _, c in lean_tools.most_common()]
        lean_colors = plt.cm.viridis(np.linspace(0.2, 0.9, len(lean_names)))
        bars4 = ax4.barh(range(len(lean_names)), lean_counts, color=lean_colors, alpha=0.85)
        ax4.set_yticks(range(len(lean_names)))
        ax4.set_yticklabels(lean_names, fontsize=8)
        ax4.invert_yaxis()
        ax4.set_xlabel("Total calls")
        ax4.set_title(f"Lean LSP Tool Breakdown ({sum(lean_counts):,} total)")
        ax4.grid(True, axis="x", alpha=0.3)
        for bar, count in zip(bars4, lean_counts):
            ax4.text(bar.get_width() + max(lean_counts) * 0.01,
                     bar.get_y() + bar.get_height() / 2,
                     f"{count}", va="center", fontsize=7)

    fig.suptitle(
        f"Claude Code Tool Usage: {total:,} Calls Across {len(tool_counts)} Tools "
        f"over {len(all_days)} Days",
        fontsize=13, fontweight="bold", y=1.01,
    )
    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150, bbox_inches="tight")
    print(f"\nWrote {OUT_PNG}")


if __name__ == "__main__":
    main()
