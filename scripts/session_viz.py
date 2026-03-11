#!/usr/bin/env python3
"""Visualize Claude Code session activity over the project."""

import json
import glob
import os
import re
from collections import Counter
from datetime import datetime, timedelta, timezone

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SESSION_DIRS = [
    os.path.expanduser("~/.claude/projects/-Users-vasil-Github-aristotle/"),
    "/tmp/americano-sessions/",  # from university machine
]
OUT_PNG = os.path.join(REPO, "scripts", "session_activity.png")

PT = timezone(timedelta(hours=-7))  # PDT (March = daylight saving)

# Pattern for slash command invocations in message content
SLASH_CMD_RE = re.compile(r"<command-name>(/\w+)</command-name>")


def parse_ts(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(PT)


def classify_user_message(content):
    """Classify a user message as 'automated', 'interactive', or None (skip).

    Returns (category, slash_command_or_None).
    """
    text_parts = []
    has_text = False

    if isinstance(content, str):
        if content.strip():
            text_parts.append(content)
            has_text = True
    elif isinstance(content, list):
        for item in content:
            if isinstance(item, dict) and item.get("type") == "text":
                t = item.get("text", "").strip()
                if t:
                    text_parts.append(t)
                    has_text = True

    if not has_text:
        return None, None

    full_text = "\n".join(text_parts)

    # Check for slash command invocation
    match = SLASH_CMD_RE.search(full_text)
    if match:
        return "automated", match.group(1)

    # Context continuation messages
    if "continue" in full_text.lower() and "context" in full_text.lower():
        return "continuation", None
    if full_text.startswith("This session is being continued"):
        return "continuation", None

    return "interactive", None


def load_messages():
    """Load all messages, classifying human prompts by type."""
    files = []
    for d in SESSION_DIRS:
        files.extend(glob.glob(os.path.join(d, "*.jsonl")))
    files = sorted(files)

    interactive_prompts = []
    automated_prompts = []
    continuation_prompts = []
    assistant_turns = []
    slash_cmds = Counter()

    for f in files:
        for line in open(f):
            line = line.strip()
            if not line:
                continue
            try:
                d = json.loads(line)
            except Exception:
                continue
            ts = d.get("timestamp")
            if not ts:
                continue
            typ = d.get("type")

            if typ == "user":
                msg = d.get("message", {})
                content = msg.get("content", [])
                cat, cmd = classify_user_message(content)
                t = parse_ts(ts)
                if cat == "automated":
                    automated_prompts.append(t)
                    if cmd:
                        slash_cmds[cmd] += 1
                elif cat == "interactive":
                    interactive_prompts.append(t)
                elif cat == "continuation":
                    continuation_prompts.append(t)
            elif typ == "assistant":
                assistant_turns.append(t)

    return (sorted(interactive_prompts), sorted(automated_prompts),
            sorted(continuation_prompts), sorted(assistant_turns), slash_cmds)


def main():
    interactive, automated, continuations, assistant_turns, slash_cmds = load_messages()

    total_human = len(interactive) + len(automated) + len(continuations)
    print(f"Interactive human prompts: {len(interactive)}")
    print(f"Automated slash commands:  {len(automated)}")
    for cmd, count in slash_cmds.most_common():
        print(f"    {cmd}: {count}")
    print(f"Context continuations:     {len(continuations)}")
    print(f"Total human messages:      {total_human}")
    print(f"Assistant turns:           {len(assistant_turns)}")

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.dates as mdates
    import numpy as np

    fig, axes = plt.subplots(2, 1, figsize=(12, 8), height_ratios=[1.2, 1])

    # ── Top: activity over time ──
    ax1 = axes[0]

    all_msgs = sorted(interactive + automated + continuations + assistant_turns)
    if not all_msgs:
        return

    start = all_msgs[0].replace(minute=0, second=0, microsecond=0)
    end = all_msgs[-1].replace(minute=0, second=0, microsecond=0) + timedelta(hours=1)
    hours = []
    t = start
    while t < end:
        hours.append(t)
        t += timedelta(hours=1)

    interactive_counts = [0] * len(hours)
    automated_counts = [0] * len(hours)
    asst_counts = [0] * len(hours)

    for msg in interactive:
        idx = int((msg - start).total_seconds() // 3600)
        if 0 <= idx < len(hours):
            interactive_counts[idx] += 1
    for msg in automated:
        idx = int((msg - start).total_seconds() // 3600)
        if 0 <= idx < len(hours):
            automated_counts[idx] += 1
    for msg in assistant_turns:
        idx = int((msg - start).total_seconds() // 3600)
        if 0 <= idx < len(hours):
            asst_counts[idx] += 1

    ax1.bar(hours, asst_counts, width=1 / 24, color="#3498db", alpha=0.5,
            label=f"Assistant turns ({len(assistant_turns):,})")
    ax1.bar(hours, automated_counts, width=1 / 24, color="#f39c12", alpha=0.9,
            label=f"Automated slash commands ({len(automated):,})")
    ax1.bar(hours, interactive_counts, width=1 / 24, color="#e74c3c", alpha=0.9,
            label=f"Interactive human prompts ({len(interactive):,})")

    ax1.set_ylabel("Messages per hour")
    ax1.set_title("Claude Code Activity Over Time (Pacific Time)")
    ax1.xaxis.set_major_formatter(mdates.DateFormatter("%b %d", tz=PT))
    ax1.xaxis.set_major_locator(mdates.DayLocator(interval=1, tz=PT))
    ax1.legend(loc="upper left", fontsize=9)
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(hours[0] - timedelta(hours=6), hours[-1] + timedelta(hours=6))

    # ── Bottom: hour-of-day heatmap (assistant turns only) ──
    ax2 = axes[1]

    day_start = all_msgs[0].date()
    day_end = all_msgs[-1].date()
    days = []
    d = day_start
    while d <= day_end:
        days.append(d)
        d += timedelta(days=1)

    grid = np.zeros((24, len(days)))
    for msg in assistant_turns:
        day_idx = (msg.date() - day_start).days
        if 0 <= day_idx < len(days):
            grid[msg.hour, day_idx] += 1

    im = ax2.imshow(grid, aspect="auto", cmap="YlOrRd", origin="lower",
                    interpolation="nearest")
    ax2.set_ylabel("Hour of day (Pacific)")
    ax2.set_title("Activity Heatmap (Assistant Turns)")

    ax2.set_xticks(range(len(days)))
    ax2.set_xticklabels([d.strftime("%b %d") for d in days],
                        rotation=45, ha="right", fontsize=8)
    ax2.set_yticks(range(0, 24, 3))
    ax2.set_yticklabels([f"{h:02d}:00" for h in range(0, 24, 3)])

    cbar = fig.colorbar(im, ax=ax2, shrink=0.8, pad=0.02)
    cbar.set_label("Turns per hour")

    fig.suptitle(
        f"Claude Code: {len(interactive):,} Interactive + "
        f"{len(automated):,} Automated Prompts \u2192 "
        f"{len(assistant_turns):,} Assistant Turns over {len(days)} Days",
        fontsize=12, fontweight="bold", y=1.01,
    )
    fig.tight_layout()
    fig.savefig(OUT_PNG, dpi=150, bbox_inches="tight")
    print(f"\nWrote {OUT_PNG}")


if __name__ == "__main__":
    main()
