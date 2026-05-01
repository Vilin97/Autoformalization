"""Shared helpers for GV report figures."""
import json, os
from datetime import datetime, timezone, timedelta
from pathlib import Path

ROOT = Path("/Users/vasil/Github/Clawristotle")
DATA = ROOT / "artifacts" / "report-data"
ART = ROOT / "artifacts"

PDT = timezone(timedelta(hours=-7))

PHASES = [
    ("Proving",   "2026-03-27", "2026-04-04", "#3b82f6"),
    ("Docs/PR",   "2026-04-05", "2026-04-08", "#8b5cf6"),
    ("Refactor",  "2026-04-19", "2026-04-27", "#10b981"),
    ("Compress",  "2026-04-27", "2026-04-29", "#f59e0b"),
    ("Mathlib-style", "2026-04-29", "2026-05-01", "#ef4444"),
]

def load_jsonl(name):
    p = DATA / "extracted" / name
    rows = []
    if not p.exists(): return rows
    with open(p) as f:
        for line in f:
            try: rows.append(json.loads(line))
            except: pass
    return rows

def load_aristotle():
    with open(DATA / "raw" / "aristotle" / "projects.json") as f:
        return json.load(f)

def parse_ts(s):
    if not s: return None
    try:
        return datetime.fromisoformat(s.replace("Z","+00:00"))
    except:
        return None

def annotate_phases(ax, ymax=None):
    import matplotlib.dates as mdates
    for name, lo, hi, color in PHASES:
        d_lo = datetime.fromisoformat(lo).replace(tzinfo=PDT)
        d_hi = datetime.fromisoformat(hi).replace(tzinfo=PDT)
        ax.axvspan(d_lo, d_hi, alpha=0.10, color=color, zorder=0)
