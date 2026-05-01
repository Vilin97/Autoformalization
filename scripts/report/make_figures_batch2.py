#!/usr/bin/env python3
"""Batch 2: figures that need the per-commit walk + tool_use extraction."""
import json
from collections import Counter, defaultdict
from datetime import datetime, timezone, timedelta
from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib.dates as mdates
import numpy as np

import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import DATA, ART, PDT, PHASES, load_jsonl, parse_ts, annotate_phases


def fig_sorry_history():
    rows = load_jsonl("per_commit_loc_sorry.jsonl")
    times = [parse_ts(r["ts"]) for r in rows]
    sorries = [r["sorry"] for r in rows]
    fig, ax = plt.subplots(figsize=(13, 5))
    ax.step(times, sorries, where="post", color="#dc2626", linewidth=1.5)
    ax.fill_between(times, sorries, step="post", color="#dc2626", alpha=0.20)
    annotate_phases(ax)
    # mark zero crossings
    for i in range(1, len(sorries)):
        if sorries[i-1] > 0 and sorries[i] == 0:
            ax.axvline(times[i], color="green", linestyle=":", alpha=0.5)
            ax.text(times[i], max(sorries)*0.85, " 0 sorries", color="green", fontsize=9, rotation=90, va="top")
            break
    ax.set_ylabel("`sorry` count (excl. comments)")
    ax.set_title(f"Sorry count over time — {len(rows):,} commits walked")
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=3))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")
    ax.grid(alpha=0.3)
    plt.tight_layout()
    out = ART / "sorry_history_gv.png"
    plt.savefig(out, dpi=130); plt.close()
    print(f"  {out}")


def fig_loc_history():
    rows = load_jsonl("per_commit_loc_sorry.jsonl")
    comp = load_jsonl("cycle_history_compress.jsonl")
    times = [parse_ts(r["ts"]) for r in rows]
    raw = [r["raw_loc"] for r in rows]

    # normalized LOC: from compress cycles only
    comp_t  = [parse_ts(c["timestamp"]) for c in comp]
    comp_no = [c["loc_after"] for c in comp]

    fig, ax = plt.subplots(figsize=(13, 5))
    ax.plot(times, raw, color="#1f77b4", linewidth=1.5, label=f"raw LOC ({raw[-1]:,} at HEAD)")
    if comp_t:
        ax.plot(comp_t, comp_no, color="#f59e0b", linewidth=1.5, marker="o", markersize=3,
                label=f"normalized LOC (compress cycles, {comp_no[-1]:,} after cycle 86)")
    annotate_phases(ax)
    ax.set_ylabel("lines of code")
    ax.set_title(f"LOC history — Aristotle/GrothendieckVanishing/ across {len(rows):,} commits")
    ax.legend(loc="upper right", fontsize=9)
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=3))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")
    ax.grid(alpha=0.3)
    plt.tight_layout()
    out = ART / "loc_history_gv.png"
    plt.savefig(out, dpi=130); plt.close()
    print(f"  {out}")


def fig_loc_breakdown():
    """Stacked area: raw LOC per file at HEAD."""
    import subprocess
    files = subprocess.check_output(
        ["find","Aristotle/GrothendieckVanishing","-name","*.lean"],
        cwd="/Users/vasil/Github/Clawristotle", text=True).splitlines()
    sizes = []
    for f in files:
        with open(f"/Users/vasil/Github/Clawristotle/{f}") as fh:
            n = sum(1 for _ in fh)
        sizes.append((f.replace("Aristotle/GrothendieckVanishing/main/",""), n))
    sizes.sort(key=lambda x: -x[1])

    fig, ax = plt.subplots(figsize=(11, 6))
    names = [s[0] for s in sizes]
    vals  = [s[1] for s in sizes]
    bars = ax.barh(names[::-1], vals[::-1], color="#3b82f6")
    for bar, v in zip(bars, vals[::-1]):
        ax.text(v + max(vals)*0.005, bar.get_y() + bar.get_height()/2, f"{v}", va="center", fontsize=9)
    ax.set_xlabel("raw LOC")
    ax.set_title(f"LOC breakdown at HEAD — {len(files)} files, total {sum(vals):,} lines")
    plt.tight_layout()
    out = ART / "loc_breakdown_gv.png"
    plt.savefig(out, dpi=130); plt.close()
    print(f"  {out}")


def fig_tool_use():
    rows = load_jsonl("tool_use.jsonl")
    # categorize tools
    def cat(name):
        n = (name or "").lower()
        if n in ("bash","read","edit","write","grep","glob","ls","multiedit"):
            return f"file/shell:{name.lower()}"
        if n.startswith("mcp__lean-lsp"): return "mcp:lean-lsp"
        if n.startswith("mcp__lean-explore"): return "mcp:lean-explore"
        if n.startswith("mcp__aristotle"): return "mcp:aristotle"
        if n.startswith("mcp__"): return "mcp:other"
        if n in ("agent","skill","toolsearch","webfetch","websearch"): return f"agent/skill:{n}"
        if n in ("taskcreate","taskupdate","tasklist","taskget"): return "task tools"
        return f"other:{name}"

    by_cat = Counter()
    by_name = Counter()
    by_day_cat = defaultdict(Counter)
    for r in rows:
        c = cat(r["name"])
        by_cat[c] += 1
        by_name[r["name"]] += 1
        ts = parse_ts(r["ts"])
        if ts: by_day_cat[ts.astimezone(PDT).date()][c] += 1

    fig, axes = plt.subplots(1, 2, figsize=(16, 7))
    # Top: top 20 by name
    top = by_name.most_common(20)
    ax = axes[0]
    names = [t[0].replace("mcp__","") for t in top[::-1]]
    vals  = [t[1] for t in top[::-1]]
    ax.barh(names, vals, color="#2563eb")
    for i, v in enumerate(vals):
        ax.text(v + max(vals)*0.005, i, f"{v}", va="center", fontsize=8)
    ax.set_title(f"Top 20 tools by call count ({sum(by_name.values()):,} total calls)")
    ax.set_xlabel("calls")

    # Right: daily stacked by category
    ax = axes[1]
    cats = [c for c,_ in by_cat.most_common(10)]
    days = sorted(by_day_cat)
    bottom = np.zeros(len(days))
    cmap = plt.get_cmap("tab10")
    for i, c in enumerate(cats):
        vals = np.array([by_day_cat[d].get(c, 0) for d in days])
        ax.bar(days, vals, bottom=bottom, label=f"{c} ({vals.sum()})", color=cmap(i), width=0.9)
        bottom += vals
    ax.set_title(f"Daily tool calls by category")
    ax.set_ylabel("calls / day")
    ax.legend(loc="upper left", fontsize=8, ncols=1)
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=3))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")
    annotate_phases(ax)

    plt.tight_layout()
    out = ART / "tool_use_gv.png"
    plt.savefig(out, dpi=130); plt.close()
    print(f"  {out}")


if __name__ == "__main__":
    print("Building batch 2 figures:")
    fig_sorry_history()
    fig_loc_history()
    fig_loc_breakdown()
    fig_tool_use()
