#!/usr/bin/env python3
"""
Generate session activity and token usage charts for the Grothendieck Vanishing project.

Reads JSONL session logs from ~/.claude/projects/-Users-vasil-Github-aristotle/
and produces two figures in artifacts/:
  - session_activity_gv.png  (messages per hour + hour-of-day heatmap)
  - token_usage_gv.png       (cumulative tokens + per-turn context size)
"""

import json
import os
import sys
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib.dates as mdates
import matplotlib.colors as mcolors
import numpy as np

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
SESSION_DIR = Path.home() / ".claude" / "projects" / "-Users-vasil-Github-aristotle"
ARTIFACTS_DIR = Path(__file__).resolve().parent.parent / "artifacts"
ARTIFACTS_DIR.mkdir(parents=True, exist_ok=True)

PDT = timezone(timedelta(hours=-7))
CUTOFF = datetime(2026, 3, 27, tzinfo=PDT)
DATE_END = datetime(2026, 4, 6, tzinfo=PDT)  # exclusive upper bound (Apr 5 inclusive)

AUTOMATED_PREFIXES = ("/babysit", "/compact", "/clear")


# ---------------------------------------------------------------------------
# Data loading
# ---------------------------------------------------------------------------
def load_sessions():
    """Load all JSONL session files modified on or after the cutoff date."""
    cutoff_epoch = CUTOFF.timestamp()
    records = []
    for path in SESSION_DIR.glob("*.jsonl"):
        if os.path.getmtime(path) < cutoff_epoch:
            continue
        with open(path, "r") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except json.JSONDecodeError:
                    continue
                ts_str = obj.get("timestamp")
                msg_type = obj.get("type")
                if not ts_str or msg_type not in ("user", "assistant"):
                    continue
                # Parse ISO timestamp
                try:
                    ts = datetime.fromisoformat(ts_str)
                except ValueError:
                    continue
                # Convert to PDT
                ts_pdt = ts.astimezone(PDT)
                if ts_pdt < CUTOFF or ts_pdt >= DATE_END:
                    continue
                records.append({
                    "type": msg_type,
                    "timestamp": ts_pdt,
                    "message": obj.get("message", {}),
                })
    records.sort(key=lambda r: r["timestamp"])
    return records


def classify_user_message(record):
    """
    Classify a user message as:
      'interactive' - real human prompt
      'automated'   - slash command (/babysit, /compact, /clear)
      None          - tool result or meta message (skip)
    """
    content = record["message"].get("content", "")
    # tool_result messages come as list of dicts
    if isinstance(content, list):
        # Check if every item is a tool_result
        if all(isinstance(c, dict) and c.get("type") == "tool_result" for c in content):
            return None
        # Sometimes mixed: tool_result + text. Check for slash commands in text blocks.
        texts = [c.get("text", "") for c in content if isinstance(c, dict) and c.get("type") == "text"]
        combined = " ".join(texts)
        if not combined.strip():
            return None
        # Check for automated slash commands in the text
        for prefix in AUTOMATED_PREFIXES:
            if prefix in combined.lower():
                return "automated"
        return "interactive"
    if not isinstance(content, str):
        return None
    # Skip local-command-caveat wrappers with no actual user content
    if content.strip().startswith("<local-command-caveat>"):
        return None
    # Check for command-name tags
    if "<command-name>" in content:
        # Extract the command
        start = content.find("<command-name>") + len("<command-name>")
        end = content.find("</command-name>")
        if end > start:
            cmd = content[start:end].strip().lower()
            for prefix in AUTOMATED_PREFIXES:
                if cmd.startswith(prefix):
                    return "automated"
            # Other slash commands (like /prove, /plan) are interactive user actions
            return "interactive"
        return "automated"
    if not content.strip():
        return None
    # Check for slash command at start of plain text
    stripped = content.strip()
    for prefix in AUTOMATED_PREFIXES:
        if stripped.lower().startswith(prefix):
            return "automated"
    return "interactive"


# ---------------------------------------------------------------------------
# Figure 1: Session Activity
# ---------------------------------------------------------------------------
def make_session_activity(records):
    # Buckets per hour
    interactive_by_hour = defaultdict(int)
    automated_by_hour = defaultdict(int)
    assistant_by_hour = defaultdict(int)
    # For heatmap: (date, hour) -> count of assistant messages
    heatmap = defaultdict(int)

    for r in records:
        ts = r["timestamp"]
        hour_key = ts.replace(minute=0, second=0, microsecond=0)
        date_key = ts.date()
        hour_of_day = ts.hour

        if r["type"] == "assistant":
            assistant_by_hour[hour_key] += 1
            heatmap[(date_key, hour_of_day)] += 1
        elif r["type"] == "user":
            cls = classify_user_message(r)
            if cls == "interactive":
                interactive_by_hour[hour_key] += 1
            elif cls == "automated":
                automated_by_hour[hour_key] += 1

    # Build time axis: every hour from CUTOFF to DATE_END
    all_hours = []
    t = CUTOFF.replace(minute=0, second=0, microsecond=0)
    while t < DATE_END:
        all_hours.append(t)
        t += timedelta(hours=1)

    interactive_vals = [interactive_by_hour.get(h, 0) for h in all_hours]
    automated_vals = [automated_by_hour.get(h, 0) for h in all_hours]
    assistant_vals = [assistant_by_hour.get(h, 0) for h in all_hours]

    # --- Figure ---
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(14, 8), gridspec_kw={"height_ratios": [3, 2]})

    # Top: stacked bar chart
    bar_width = timedelta(hours=0.8)
    ax1.bar(all_hours, interactive_vals, width=bar_width, color="#d32f2f", label="Human prompts", alpha=0.9)
    ax1.bar(all_hours, automated_vals, width=bar_width, bottom=interactive_vals,
            color="#ff9800", label="Automated (/babysit, /compact, /clear)", alpha=0.9)
    bottoms = [i + a for i, a in zip(interactive_vals, automated_vals)]
    ax1.bar(all_hours, assistant_vals, width=bar_width, bottom=bottoms,
            color="#1976d2", label="Assistant turns", alpha=0.9)
    ax1.set_ylabel("Messages per hour")
    ax1.set_title("Grothendieck Vanishing — Session Activity (PDT)", fontsize=13, fontweight="bold")
    ax1.legend(loc="upper left", fontsize=9)
    ax1.xaxis.set_major_formatter(mdates.DateFormatter("%-m/%-d", tz=PDT))
    ax1.xaxis.set_major_locator(mdates.DayLocator(tz=PDT))
    ax1.grid(True, alpha=0.3, color="gray")
    ax1.set_xlim(CUTOFF, DATE_END)

    # Bottom: heatmap
    # Date range
    start_date = CUTOFF.date()
    end_date = (DATE_END - timedelta(days=1)).date()
    dates = []
    d = start_date
    while d <= end_date:
        dates.append(d)
        d += timedelta(days=1)
    hours = list(range(24))
    heatmap_arr = np.zeros((24, len(dates)))
    for di, date in enumerate(dates):
        for hi, hour in enumerate(hours):
            heatmap_arr[hi, di] = heatmap.get((date, hour), 0)

    # Use a colormap that's white for 0
    cmap = plt.cm.YlOrRd.copy()
    cmap.set_under("white")
    vmax = max(heatmap_arr.max(), 1)
    im = ax2.imshow(
        heatmap_arr,
        aspect="auto",
        origin="lower",
        cmap=cmap,
        vmin=0.5,
        vmax=vmax,
        interpolation="nearest",
        extent=[-0.5, len(dates) - 0.5, -0.5, 23.5],
    )
    ax2.set_xticks(range(len(dates)))
    ax2.set_xticklabels([d.strftime("%-m/%-d") for d in dates], fontsize=9)
    ax2.set_yticks([0, 4, 8, 12, 16, 20, 23])
    ax2.set_yticklabels(["12am", "4am", "8am", "12pm", "4pm", "8pm", "11pm"], fontsize=9)
    ax2.set_ylabel("Hour of day (PDT)")
    ax2.set_xlabel("Date (PDT)")
    ax2.set_title("Assistant Activity Heatmap (hour x date)", fontsize=11)
    cbar = fig.colorbar(im, ax=ax2, shrink=0.8, pad=0.02)
    cbar.set_label("Assistant messages", fontsize=9)

    fig.tight_layout()
    out = ARTIFACTS_DIR / "session_activity_gv.png"
    fig.savefig(out, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {out}")


# ---------------------------------------------------------------------------
# Figure 2: Token Usage
# ---------------------------------------------------------------------------
def make_token_usage(records):
    # Collect assistant turns with token usage
    turns = []
    for r in records:
        if r["type"] != "assistant":
            continue
        usage = r["message"].get("usage", {})
        if not usage:
            continue
        input_tokens = usage.get("input_tokens", 0)
        output_tokens = usage.get("output_tokens", 0)
        cache_creation = usage.get("cache_creation_input_tokens", 0)
        cache_read = usage.get("cache_read_input_tokens", 0)
        turns.append({
            "timestamp": r["timestamp"],
            "input_tokens": input_tokens,
            "output_tokens": output_tokens,
            "cache_creation": cache_creation,
            "cache_read": cache_read,
            "total_context": input_tokens + cache_creation + cache_read,
        })

    if not turns:
        print("No assistant turns with token data found.", file=sys.stderr)
        return

    timestamps = [t["timestamp"] for t in turns]
    cum_input = np.cumsum([t["input_tokens"] + t["cache_creation"] + t["cache_read"] for t in turns])
    cum_output = np.cumsum([t["output_tokens"] for t in turns])
    context_per_turn = [t["total_context"] for t in turns]

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 7), gridspec_kw={"height_ratios": [1, 1]})

    # Top: cumulative tokens
    color_input = "#1976d2"
    color_output = "#d32f2f"
    ax1.plot(timestamps, cum_input / 1e6, color=color_input, linewidth=1.5, label="Cumulative input (M)")
    ax1.set_ylabel("Input tokens (millions)", color=color_input, fontsize=10)
    ax1.tick_params(axis="y", labelcolor=color_input)
    ax1r = ax1.twinx()
    ax1r.plot(timestamps, cum_output / 1e6, color=color_output, linewidth=1.5, label="Cumulative output (M)")
    ax1r.set_ylabel("Output tokens (millions)", color=color_output, fontsize=10)
    ax1r.tick_params(axis="y", labelcolor=color_output)
    ax1.set_title("Grothendieck Vanishing — Token Usage (PDT)", fontsize=13, fontweight="bold")
    ax1.xaxis.set_major_formatter(mdates.DateFormatter("%-m/%-d", tz=PDT))
    ax1.xaxis.set_major_locator(mdates.DayLocator(tz=PDT))
    ax1.grid(True, alpha=0.3, color="gray")
    ax1.set_xlim(CUTOFF, DATE_END)
    # Combined legend
    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax1r.get_legend_handles_labels()
    ax1.legend(lines1 + lines2, labels1 + labels2, loc="upper left", fontsize=9)

    # Bottom: per-turn context size (sawtooth)
    ax2.scatter(timestamps, np.array(context_per_turn) / 1e3, s=4, color="#1976d2", alpha=0.5)
    ax2.plot(timestamps, np.array(context_per_turn) / 1e3, color="#1976d2", linewidth=0.4, alpha=0.6)
    ax2.set_ylabel("Context size per turn (K tokens)", fontsize=10)
    ax2.set_xlabel("Date (PDT)")
    ax2.set_title("Per-Turn Context Size (input + cache)", fontsize=11)
    ax2.xaxis.set_major_formatter(mdates.DateFormatter("%-m/%-d", tz=PDT))
    ax2.xaxis.set_major_locator(mdates.DayLocator(tz=PDT))
    ax2.grid(True, alpha=0.3, color="gray")
    ax2.set_xlim(CUTOFF, DATE_END)

    fig.tight_layout()
    out = ARTIFACTS_DIR / "token_usage_gv.png"
    fig.savefig(out, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {out}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main():
    print(f"Loading sessions from {SESSION_DIR} ...")
    records = load_sessions()
    print(f"  {len(records)} messages in date range (PDT {CUTOFF.date()} to {DATE_END.date()})")

    user_msgs = [r for r in records if r["type"] == "user"]
    asst_msgs = [r for r in records if r["type"] == "assistant"]
    interactive = sum(1 for r in user_msgs if classify_user_message(r) == "interactive")
    automated = sum(1 for r in user_msgs if classify_user_message(r) == "automated")
    print(f"  User: {interactive} interactive, {automated} automated, {len(user_msgs) - interactive - automated} tool/meta")
    print(f"  Assistant: {len(asst_msgs)} turns")

    make_session_activity(records)
    make_token_usage(records)
    print("Done.")


if __name__ == "__main__":
    main()
