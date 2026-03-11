#!/usr/bin/env python3
"""Visualize Claude Code token usage over the project."""

import json
import glob
import os
from datetime import datetime, timedelta, timezone

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SESSION_DIRS = [
    os.path.expanduser("~/.claude/projects/-Users-vasil-Github-aristotle/"),
    "/tmp/americano-sessions/",  # from university machine
]
OUT_PNG = os.path.join(REPO, "scripts", "token_usage.png")

PT = timezone(timedelta(hours=-7))  # PDT (March = daylight saving)


def parse_ts(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(PT)


def load_data():
    files = []
    for d in SESSION_DIRS:
        files.extend(glob.glob(os.path.join(d, "*.jsonl")))
    files = sorted(files)

    turns = []
    compacts = []

    for f in files:
        for line in open(f):
            line = line.strip()
            if not line:
                continue
            try:
                d = json.loads(line)
            except Exception:
                continue

            if d.get("type") == "assistant":
                usage = d.get("message", {}).get("usage", {})
                ts = d.get("timestamp")
                if not usage or not ts:
                    continue
                t = parse_ts(ts)
                turns.append({
                    "t": t,
                    "input": usage.get("input_tokens", 0),
                    "cache_create": usage.get("cache_creation_input_tokens", 0),
                    "cache_read": usage.get("cache_read_input_tokens", 0),
                    "output": usage.get("output_tokens", 0),
                })
            elif d.get("type") == "system" and d.get("subtype") == "compact_boundary":
                ts = d.get("timestamp")
                if ts:
                    compacts.append(parse_ts(ts))

    turns.sort(key=lambda x: x["t"])
    compacts.sort()
    return turns, compacts


def main():
    turns, compacts = load_data()

    print(f"Assistant turns: {len(turns):,}")
    print(f"Autocompacts:    {len(compacts)}")

    total_input = sum(t["input"] + t["cache_create"] + t["cache_read"] for t in turns)
    total_output = sum(t["output"] for t in turns)
    print(f"Total input tokens (incl. cache): {total_input:,}")
    print(f"Total output tokens:              {total_output:,}")
    print(f"Grand total:                      {total_input + total_output:,}")

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.dates as mdates
    import numpy as np

    fig, axes = plt.subplots(2, 1, figsize=(12, 8), height_ratios=[1.2, 1])

    # ── Top: cumulative tokens over time (dual y-axes) ──
    ax1 = axes[0]

    timestamps = [t["t"] for t in turns]
    cum_input = np.cumsum([t["input"] + t["cache_create"] + t["cache_read"] for t in turns])
    cum_output = np.cumsum([t["output"] for t in turns])

    line1, = ax1.plot(timestamps, cum_input / 1e9, color="#3498db", linewidth=2,
                      label=f"Input tokens (incl. cache): {total_input/1e9:.2f}B")
    ax1.set_ylabel("Cumulative input tokens (billions)", color="#3498db")
    ax1.tick_params(axis="y", labelcolor="#3498db")

    ax1_r = ax1.twinx()
    line2, = ax1_r.plot(timestamps, cum_output / 1e6, color="#e74c3c", linewidth=2,
                        label=f"Output tokens: {total_output/1e6:.1f}M")
    ax1_r.set_ylabel("Cumulative output tokens (millions)", color="#e74c3c")
    ax1_r.tick_params(axis="y", labelcolor="#e74c3c")

    ax1.set_title("Cumulative Token Usage Over Time")
    ax1.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=PT))
    ax1.xaxis.set_major_locator(mdates.DayLocator(interval=1, tz=PT))
    ax1.legend(handles=[line1, line2], loc="upper left", fontsize=9)
    ax1.grid(True, alpha=0.3)

    # ── Bottom: context size per turn (sawtooth) with autocompact markers ──
    ax2 = axes[1]

    context_sizes = [t["input"] + t["cache_create"] + t["cache_read"] for t in turns]

    ax2.scatter(timestamps, [c / 1000 for c in context_sizes], s=0.3, alpha=0.4,
                color="#3498db", rasterized=True)

    # Mark compactions
    for c in compacts:
        ax2.axvline(c, color="#e74c3c", alpha=0.3, linewidth=0.5)

    ax2.set_ylabel("Context size per turn (K tokens)")
    ax2.set_title(f"Context Window Usage ({len(compacts)} Autocompacts, marked in red)")
    ax2.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=PT))
    ax2.xaxis.set_major_locator(mdates.DayLocator(interval=1, tz=PT))
    ax2.set_ylim(bottom=0)
    ax2.grid(True, alpha=0.3)

    fig.suptitle(
        f"Claude Code Token Usage: {total_input/1e9:.1f}B Input + "
        f"{total_output/1e6:.0f}M Output = {(total_input+total_output)/1e9:.1f}B Total",
        fontsize=12, fontweight="bold", y=1.01,
    )
    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150, bbox_inches="tight")
    print(f"\nWrote {OUT_PNG}")


if __name__ == "__main__":
    main()
