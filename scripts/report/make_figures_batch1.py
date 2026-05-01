#!/usr/bin/env python3
"""Batch 1: figures that only need the gathered data (no per-commit walk)."""
import json
from collections import Counter, defaultdict
from datetime import datetime, timezone, timedelta
from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib.dates as mdates
import numpy as np

import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    DATA, ART, PDT, PHASES, load_jsonl, load_aristotle, parse_ts, annotate_phases
)


def fig_session_activity():
    cl = load_jsonl("claude_turns_laptop.jsonl") + load_jsonl("claude_turns_hyak.jsonl")
    co = load_jsonl("codex_turns_laptop.jsonl") + load_jsonl("codex_turns_hyak.jsonl")
    by_day_machine = defaultdict(lambda: Counter())
    for r in cl:
        ts = parse_ts(r.get("ts"))
        if ts: by_day_machine[ts.astimezone(PDT).date()][("Claude", r["machine"])] += 1
    for r in co:
        ts = parse_ts(r.get("ts"))
        if ts: by_day_machine[ts.astimezone(PDT).date()][("Codex", r["machine"])] += 1
    days = sorted(by_day_machine)
    keys = [("Claude","laptop"), ("Claude","hyak"), ("Codex","laptop"), ("Codex","hyak")]
    colors = {"Claude_laptop":"#2563eb", "Claude_hyak":"#60a5fa",
              "Codex_laptop":"#16a34a",  "Codex_hyak":"#86efac"}
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(13, 7), gridspec_kw={"height_ratios":[2,1]})
    bottom = np.zeros(len(days))
    for tool, mach in keys:
        vals = np.array([by_day_machine[d].get((tool, mach), 0) for d in days])
        ax1.bar(days, vals, bottom=bottom, color=colors[f"{tool}_{mach}"],
                label=f"{tool} ({mach})", width=0.9)
        bottom += vals
    ax1.set_title("Session activity over time (assistant turns / day) — by tool & machine")
    ax1.set_ylabel("turns / day")
    annotate_phases(ax1)
    for name, lo, hi, color in PHASES:
        d_lo = datetime.fromisoformat(lo).date()
        ax1.text(d_lo, ax1.get_ylim()[1]*0.95, name, fontsize=8, color=color, ha="left", va="top")
    ax1.legend(loc="upper left", fontsize=9, ncols=4)
    ax1.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax1.xaxis.set_major_locator(mdates.DayLocator(interval=3))
    plt.setp(ax1.xaxis.get_majorticklabels(), rotation=30, ha="right")

    # hour-of-day heatmap, separate for laptop vs hyak
    hour_mat = np.zeros((2, 24))  # row 0=laptop, 1=hyak
    for r in cl + co:
        ts = parse_ts(r.get("ts"))
        if not ts: continue
        local = ts.astimezone(PDT)
        m = 0 if r["machine"] == "laptop" else 1
        hour_mat[m, local.hour] += 1
    im = ax2.imshow(hour_mat, aspect="auto", cmap="YlGnBu")
    ax2.set_yticks([0,1]); ax2.set_yticklabels(["laptop","hyak"])
    ax2.set_xticks(range(0,24,2))
    ax2.set_xlabel("hour of day (PDT)")
    ax2.set_title("Hour-of-day distribution (turns)")
    plt.colorbar(im, ax=ax2, fraction=0.04, pad=0.02, label="turns")
    plt.tight_layout()
    out = ART / "session_activity_gv.png"
    plt.savefig(out, dpi=130)
    plt.close()
    print(f"  {out}")


def fig_token_usage():
    cl = load_jsonl("claude_turns_laptop.jsonl") + load_jsonl("claude_turns_hyak.jsonl")
    co = load_jsonl("codex_turns_laptop.jsonl") + load_jsonl("codex_turns_hyak.jsonl")
    cl_sorted = sorted(((parse_ts(r["ts"]), r) for r in cl if r.get("ts")), key=lambda x: x[0])

    fig, axes = plt.subplots(2, 1, figsize=(13, 8))

    # Top: cumulative tokens (Claude split by category) over time
    ax = axes[0]
    times = [t for t,_ in cl_sorted]
    inp = np.cumsum([r.get("input_tokens") or 0 for _,r in cl_sorted])
    cc  = np.cumsum([r.get("cache_creation_input_tokens") or 0 for _,r in cl_sorted])
    cr  = np.cumsum([r.get("cache_read_input_tokens") or 0 for _,r in cl_sorted])
    out = np.cumsum([r.get("output_tokens") or 0 for _,r in cl_sorted])
    ax.stackplot(times, [out/1e6, cc/1e6, inp/1e6], labels=["output","cache creation","fresh input"],
                 colors=["#1f77b4", "#ff7f0e", "#9467bd"], alpha=0.85)
    # cache reads on a secondary axis
    ax2 = ax.twinx()
    ax2.plot(times, cr/1e9, color="#d62728", linewidth=2, label="cache read (RHS, billions)")
    ax2.set_ylabel("cache read (billions of tokens)", color="#d62728")
    ax2.tick_params(axis="y", labelcolor="#d62728")
    ax.set_ylabel("tokens (millions)")
    ax.set_title(f"Claude: cumulative tokens — {len(cl):,} turns across {len(set((r.get('project'),r.get('session_id')) for r in cl)):,} sessions")
    ax.legend(loc="upper left", fontsize=9)
    ax2.legend(loc="upper right", fontsize=9)
    annotate_phases(ax)
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")

    # Bottom: Codex token rows (per-turn)
    ax = axes[1]
    co_sorted = sorted(((parse_ts(r["ts"]), r) for r in co if r.get("ts")), key=lambda x: x[0])
    if co_sorted:
        times = [t for t,_ in co_sorted]
        # cumulative across sessions: just stack last-call deltas
        lt_in  = np.cumsum([r.get("lt_input") or 0 for _,r in co_sorted])
        lt_out = np.cumsum([r.get("lt_output") or 0 for _,r in co_sorted])
        ax.plot(times, lt_in/1e6, color="#16a34a", linewidth=2, label=f"input (sum {lt_in[-1]/1e6:.1f}M)")
        ax.plot(times, lt_out/1e6, color="#dc2626", linewidth=2, label=f"output (sum {lt_out[-1]/1e6:.2f}M)")
    ax.set_title(f"Codex: cumulative per-call tokens (5 GV sessions only — compress/refactor cycles ephemeral, not captured)")
    ax.set_ylabel("tokens (millions)")
    ax.legend(loc="upper left", fontsize=9)
    annotate_phases(ax)
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")

    plt.tight_layout()
    out_p = ART / "token_usage_gv.png"
    plt.savefig(out_p, dpi=130)
    plt.close()
    print(f"  {out_p}")


def fig_aristotle():
    projects = load_aristotle()

    def gv_subset(p):
        # date window + filename match
        d = (p.get("created") or "")[:10]
        if not d: return False
        if "2026-03-27" <= d <= "2026-05-01":
            fn = (p.get("file_name") or "").lower()
            pr = (p.get("input_prompt") or "").lower()
            tags = ("clawristotle","aristotle-loop","flasque","irreducible","grothendieck",
                    "constant_sheaf","closed_immersion","zero_outside","cohomologyapi","topologicalkrull")
            anti = ("bseries","closed_form_replicate","cycle_587","augmented")
            if any(t in fn or t in pr for t in tags): return True
            if any(t in fn or t in pr for t in anti): return False
            # date-window-only: include if in the proving phase or aristotle-loop day (apr 27)
            return ("2026-03-27" <= d <= "2026-04-04") or d == "2026-04-27"
        return False

    gv = [p for p in projects if gv_subset(p)]
    print(f"    Aristotle GV-filtered: {len(gv)} of {len(projects)}")

    by_date_status = defaultdict(Counter)
    for p in gv:
        d = p["created"][:10]
        by_date_status[d][p.get("status") or "?"] += 1
    days = sorted(by_date_status)
    statuses = ["COMPLETE", "COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET", "FAILED", "CANCELED", "NOT_STARTED"]
    colors = {"COMPLETE":"#16a34a","COMPLETE_WITH_ERRORS":"#f59e0b","OUT_OF_BUDGET":"#a855f7",
              "FAILED":"#dc2626","CANCELED":"#9ca3af","NOT_STARTED":"#e5e7eb"}

    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    ax = axes[0]
    bottom = np.zeros(len(days))
    xs = [datetime.fromisoformat(d) for d in days]
    for s in statuses:
        vals = np.array([by_date_status[d].get(s, 0) for d in days])
        if vals.sum() == 0: continue
        ax.bar(xs, vals, bottom=bottom, color=colors[s], label=f"{s} ({vals.sum()})", width=0.9)
        bottom += vals
    ax.set_title(f"Aristotle outcomes — GV-filtered ({len(gv)} jobs)")
    ax.set_ylabel("jobs / day")
    ax.legend(loc="upper left", fontsize=8)
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=3))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")

    # Turnaround histogram
    ax = axes[1]
    turn = []
    for p in gv:
        c = parse_ts(p.get("created"))
        u = parse_ts(p.get("updated"))
        s = p.get("status") or "?"
        if c and u and s in ("COMPLETE","COMPLETE_WITH_ERRORS","CANCELED"):
            turn.append((s, (u - c).total_seconds() / 60.0))
    if turn:
        for s in ["COMPLETE","COMPLETE_WITH_ERRORS","CANCELED"]:
            mins = [m for st, m in turn if st == s]
            if not mins: continue
            ax.hist(mins, bins=np.linspace(0, 240, 25), alpha=0.55, label=f"{s} (n={len(mins)})",
                    color=colors[s])
        ax.set_xlabel("turnaround (minutes)"); ax.set_ylabel("jobs")
        ax.set_title("Aristotle turnaround by outcome (GV-filtered)")
        ax.legend(fontsize=9)
    plt.tight_layout()
    out = ART / "aristotle_outcomes_gv.png"
    plt.savefig(out, dpi=130); plt.close()
    print(f"  {out}")


def fig_git_churn():
    commits = load_jsonl("commits.jsonl")
    by_day = defaultdict(lambda: {"ins":0, "del":0, "n":0})
    for c in commits:
        ts = parse_ts(c["ts"])
        if not ts: continue
        d = ts.astimezone(PDT).date()
        by_day[d]["ins"] += c.get("insertions", 0)
        by_day[d]["del"] += c.get("deletions", 0)
        by_day[d]["n"]   += 1
    days = sorted(by_day)
    ins = np.array([by_day[d]["ins"] for d in days])
    dlt = np.array([by_day[d]["del"] for d in days])
    n   = np.array([by_day[d]["n"]   for d in days])

    fig, axes = plt.subplots(2, 1, figsize=(13, 7), gridspec_kw={"height_ratios":[2,1]})
    ax = axes[0]
    ax.bar(days, ins, color="#16a34a", label=f"insertions (Σ {ins.sum():,})", width=0.9)
    ax.bar(days, -dlt, color="#dc2626", label=f"deletions (Σ {dlt.sum():,})", width=0.9)
    ax.plot(days, ins - dlt, color="black", linewidth=1.5, marker="o", markersize=3,
            label="net delta")
    ax.axhline(0, color="black", linewidth=0.5)
    ax.set_ylabel("lines")
    ax.set_title(f"Git churn over GV ({len(commits):,} commits since 2026-03-27)")
    ax.legend(loc="upper left", fontsize=9)
    annotate_phases(ax)
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=3))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")

    ax = axes[1]
    ax.bar(days, n, color="#3b82f6", width=0.9)
    ax.set_ylabel("commits / day"); ax.set_title("Commits per day")
    annotate_phases(ax)
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=3))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")

    plt.tight_layout()
    out = ART / "git_churn_gv.png"
    plt.savefig(out, dpi=130); plt.close()
    print(f"  {out}")


def fig_cycle_effectiveness():
    comp = load_jsonl("cycle_history_compress.jsonl")
    refac = load_jsonl("cycle_history_refactor.jsonl")
    fig, axes = plt.subplots(2, 2, figsize=(14, 9))

    # Compress: LOC delta per cycle + cumulative
    cyc = [c["cycle"] for c in comp]
    loc_after = [c["loc_after"] for c in comp]
    loc_delta = [c.get("loc_delta") or 0 for c in comp]
    raw_after = [c.get("raw_loc_after") or None for c in comp]
    ax = axes[0,0]
    ax.bar(cyc, loc_delta, color=["#16a34a" if d<0 else "#dc2626" for d in loc_delta], width=0.9)
    ax.axhline(0, color="black", lw=0.5)
    ax.set_xlabel("compress cycle"); ax.set_ylabel("normalized LOC Δ")
    ax.set_title(f"Compress loop: per-cycle Δ ({len(comp)} cycles, total Δ = {sum(loc_delta):,})")

    ax = axes[0,1]
    ax.plot(cyc, loc_after, label="normalized LOC", color="#1f77b4", linewidth=2)
    if any(r for r in raw_after):
        ax.plot(cyc, [r if r is not None else float('nan') for r in raw_after],
                label="raw LOC", color="#9ca3af", linewidth=1.5, linestyle="--")
    ax.set_xlabel("compress cycle"); ax.set_ylabel("LOC after cycle")
    ax.set_title("Compress: LOC trajectory (raw vs normalized)")
    ax.legend(); ax.grid(alpha=0.3)

    # Refactor: progress score distribution + cycles per day
    scores = [(r.get("evaluation") or {}).get("progress_score") for r in refac]
    scores = [s for s in scores if s is not None]
    ax = axes[1,0]
    ax.hist(scores, bins=np.arange(-0.5, 4.5, 1), color="#10b981", edgecolor="black")
    ax.set_xlabel("progress score"); ax.set_ylabel("cycles")
    ax.set_title(f"Refactor loop: progress score distribution ({len(refac)} cycles)")

    by_day = Counter()
    for r in refac:
        ts = parse_ts(r.get("timestamp"))
        if ts: by_day[ts.astimezone(PDT).date()] += 1
    for c in comp:
        ts = parse_ts(c.get("timestamp"))
        if ts: by_day[(ts.astimezone(PDT).date(), "compress")] = by_day.get((ts.astimezone(PDT).date(), "compress"), 0) + 1
    # split refactor vs compress
    days = sorted(set(d for d in by_day if not isinstance(d, tuple))) or sorted(set(d[0] for d in by_day if isinstance(d, tuple)))
    days_all = sorted(set(list(d if not isinstance(d, tuple) else d[0] for d in by_day)))
    refac_per = [by_day.get(d, 0) for d in days_all]
    comp_per = [by_day.get((d, "compress"), 0) for d in days_all]
    ax = axes[1,1]
    ax.bar(days_all, refac_per, color="#10b981", label=f"refactor ({sum(refac_per)})", width=0.9)
    ax.bar(days_all, comp_per,  color="#f59e0b", bottom=refac_per, label=f"compress ({sum(comp_per)})", width=0.9)
    ax.set_ylabel("cycles / day"); ax.set_title("Compress + refactor cycles per day")
    ax.legend(); ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")

    plt.tight_layout()
    out = ART / "cycle_effectiveness_gv.png"
    plt.savefig(out, dpi=130); plt.close()
    print(f"  {out}")


def fig_phase_timeline():
    commits = load_jsonl("commits.jsonl")
    # classify commits by tag
    def classify(s):
        s = (s or "").lower()
        if s.startswith("compress: codex cycle"): return "compress"
        if s.startswith("refactor:") or "codex refactor" in s: return "refactor"
        if s.startswith("aristotle-loop:") or "aristotle-loop" in s: return "aristotle-loop"
        if s.startswith("mathlib") or "mathlib-style" in s: return "mathlib-style"
        if "credit" in s or "doc" in s or "readme" in s: return "docs"
        if s.startswith("merge") or s.startswith("wip"): return "wip/merge"
        return "interactive"
    by_day_kind = defaultdict(Counter)
    for c in commits:
        ts = parse_ts(c["ts"])
        if not ts: continue
        d = ts.astimezone(PDT).date()
        by_day_kind[d][classify(c.get("subject",""))] += 1
    days = sorted(by_day_kind)
    kinds = ["interactive","docs","refactor","compress","aristotle-loop","mathlib-style","wip/merge"]
    colors = {"interactive":"#3b82f6","docs":"#8b5cf6","refactor":"#10b981",
              "compress":"#f59e0b","aristotle-loop":"#06b6d4","mathlib-style":"#ef4444",
              "wip/merge":"#9ca3af"}
    fig, ax = plt.subplots(figsize=(14, 6))
    bottom = np.zeros(len(days))
    for k in kinds:
        vals = np.array([by_day_kind[d].get(k, 0) for d in days])
        if vals.sum() == 0: continue
        ax.bar(days, vals, bottom=bottom, color=colors[k], label=f"{k} ({vals.sum()})", width=0.9)
        bottom += vals
    ax.set_title(f"Phase / loop-mode timeline — {len(commits):,} commits since 2026-03-27, classified by message tag")
    ax.set_ylabel("commits / day")
    ax.legend(loc="upper left", fontsize=9)
    annotate_phases(ax)
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    ax.xaxis.set_major_locator(mdates.DayLocator(interval=3))
    plt.setp(ax.xaxis.get_majorticklabels(), rotation=30, ha="right")
    plt.tight_layout()
    out = ART / "phase_timeline_gv.png"
    plt.savefig(out, dpi=130); plt.close()
    print(f"  {out}")


if __name__ == "__main__":
    print("Building batch 1 figures:")
    fig_session_activity()
    fig_token_usage()
    fig_aristotle()
    fig_git_churn()
    fig_cycle_effectiveness()
    fig_phase_timeline()
