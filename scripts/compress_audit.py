#!/usr/bin/env python3.9
"""Per-cycle compress audit: emits .compress-state/audit.md with FRESH data
the planner uses to choose a target. Runs unused-decl scan, lists remaining
`_presheaf` decls, top long proofs by file, per-file LOC, and Phase-5 idea
status.

Idempotent and side-effect-free except for writing audit.md. Designed to be
called by the controller before each planner invocation.
"""
from __future__ import annotations

import re
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path

REPO_DIR = Path(__file__).resolve().parent.parent
MAIN_DIR = REPO_DIR / "Aristotle" / "GrothendieckVanishing" / "main"
STATE_DIR = REPO_DIR / ".compress-state"
AUDIT_FILE = STATE_DIR / "audit.md"

sys.path.insert(0, str(REPO_DIR / "scripts"))
import compress_initial_scan as scan  # noqa: E402  reuse parsing
import normalized_loc  # noqa: E402

PRESHEAF_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s+)*"
    r"(?:private|protected|noncomputable|partial|unsafe|\s)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"(\S*_presheaf[\w]*)\b"
)

# Phase-5 ideas: COMPLETE_IF expressed as a Python predicate evaluated against
# the current tree. The audit reports done/not-done so the planner can route.
PHASE5_IDEAS: list[tuple[str, str, "callable"]] = [
    (
        "Idea 1 — sheafify PresheafFilteredColimitCore.lean",
        "Replace 4 `_presheaf` decls with sheaf-level analogues; -150 to -250 LOC",
        lambda: not _has_pfc_core_presheaf_decls(),
    ),
    (
        "Idea 2 — collapse class IsFlasqueSheaf to def",
        "One-field wrapper around IsFlasque F.val; -30 to -50 LOC",
        lambda: not _has_class_is_flasque_sheaf(),
    ),
    (
        "Idea 3 — eliminate ULiftInt.lean",
        "Replace 5 call sites or inline; -20 to -28 LOC",
        lambda: not (MAIN_DIR / "ULiftInt.lean").exists(),
    ),
    (
        "Idea 4 — merge ZeroOutsideFinset.lean into ZeroOutside.lean",
        "Used only by FinitelyGeneratedVanishing; -10 to -20 LOC",
        lambda: not (MAIN_DIR / "ZeroOutsideFinset.lean").exists(),
    ),
]


def _has_pfc_core_presheaf_decls() -> bool:
    path = MAIN_DIR / "PresheafFilteredColimitCore.lean"
    if not path.exists():
        return False
    text = path.read_text()
    targets = (
        "sheafH_filtered_colimit_succ_inj_subsingleton_presheaf",
        "sheafH_filtered_colimit_surj_presheaf",
        "sheafH_filtered_colimit_comparison_presheaf",
        "sheafH_filtered_colimit_comparison_succ_compatibility_presheaf",
    )
    return any(t in text for t in targets)


def _has_class_is_flasque_sheaf() -> bool:
    path = MAIN_DIR / "FlasqueVanishing.lean"
    if not path.exists():
        return False
    return any(
        line.strip().startswith("class IsFlasqueSheaf")
        for line in path.read_text().splitlines()
    )


def per_file_loc() -> list[tuple[str, int]]:
    rows = []
    for p in sorted(MAIN_DIR.glob("*.lean")):
        rows.append((p.name, sum(1 for _ in p.read_text().splitlines())))
    return sorted(rows, key=lambda r: -r[1])


def remaining_presheaf_decls() -> list[tuple[str, int, str]]:
    out: list[tuple[str, int, str]] = []
    for path in sorted(MAIN_DIR.glob("*.lean")):
        for i, line in enumerate(path.read_text().splitlines(), start=1):
            m = PRESHEAF_DECL_RE.match(line)
            if m:
                out.append((path.name, i, m.group(1)))
    return out


def top_long_proofs_by_file(top_per_file: int = 3, body_min: int = 50) -> dict:
    decls = scan.all_decls()
    by_file: dict[str, list] = defaultdict(list)
    for d in decls:
        if d.body_lines >= body_min:
            by_file[d.file.name].append(d)
    for fname in by_file:
        by_file[fname] = sorted(by_file[fname], key=lambda d: -d.body_lines)[:top_per_file]
    return dict(by_file)


def fmt_unused(items: list[tuple[str, str]]) -> str:
    if not items:
        return "_(none — all public decls are reachable from `GrothendieckVanishing`)_\n"
    by_mod: dict[str, list[str]] = defaultdict(list)
    for mod, name in items:
        by_mod[mod].append(name)
    lines = []
    for mod in sorted(by_mod):
        lines.append(f"- **{mod}.lean**:")
        for n in sorted(by_mod[mod]):
            lines.append(f"  - `{n}`")
    return "\n".join(lines) + "\n"


def fmt_presheaf(items: list[tuple[str, int, str]]) -> str:
    if not items:
        return "_(none)_\n"
    by_file: dict[str, list[tuple[int, str]]] = defaultdict(list)
    for fname, lineno, name in items:
        by_file[fname].append((lineno, name))
    lines = []
    for fname in sorted(by_file):
        lines.append(f"- **{fname}** ({len(by_file[fname])} decls):")
        for lineno, name in sorted(by_file[fname]):
            lines.append(f"  - L{lineno}: `{name}`")
    return "\n".join(lines) + "\n"


def fmt_long_proofs(by_file: dict, file_loc: list[tuple[str, int]]) -> str:
    if not by_file:
        return "_(none ≥ 50 body lines)_\n"
    file_order = [name for name, _ in file_loc if name in by_file]
    lines = []
    for fname in file_order:
        lines.append(f"- **{fname}**:")
        for d in by_file[fname]:
            ratio = d.body_lines / max(1, d.signature_lines)
            lines.append(
                f"  - L{d.start_line}: `{d.name}`  body={d.body_lines}, "
                f"sig={d.signature_lines}, ratio={ratio:.1f}"
            )
    return "\n".join(lines) + "\n"


def fmt_phase5() -> str:
    lines = []
    for title, blurb, predicate in PHASE5_IDEAS:
        try:
            done = bool(predicate())
        except Exception as exc:
            lines.append(f"- ⚠️ {title} — predicate error: {exc}")
            continue
        marker = "✅ done" if done else "⬜ open"
        lines.append(f"- {marker} **{title}** — {blurb}")
    return "\n".join(lines) + "\n"


def main() -> int:
    cycle_arg = sys.argv[1] if len(sys.argv) > 1 else "?"
    started = time.time()
    raw_loc = sum(sum(1 for _ in p.read_text().splitlines())
                  for p in MAIN_DIR.glob("*.lean"))
    norm_loc = normalized_loc.total_normalized_count()

    print("running unused-decl scan (this takes ~30-60s)...", file=sys.stderr)
    unused_output = scan.run_unused_decls(timeout=600)
    unused_items = scan.parse_unused(unused_output) if unused_output else []
    if not unused_output:
        unused_status = "_(scan failed or timed out — see loop log)_"
    else:
        unused_status = f"_(scan ok; {len(unused_items)} reachable-from-`GrothendieckVanishing` is False)_"

    presheaf_decls = remaining_presheaf_decls()
    long_proofs = top_long_proofs_by_file(top_per_file=3, body_min=50)
    file_loc = per_file_loc()

    elapsed = time.time() - started
    body = (
        f"# Compress audit (cycle {cycle_arg})\n\n"
        f"Generated by `scripts/compress_audit.py` in {elapsed:.1f}s. The "
        f"planner reads this BEFORE picking a target — it represents the "
        f"current state of the tree, unlike `compress_tasks.md` which can be "
        f"stale.\n\n"
        f"## LOC summary\n"
        f"- raw: **{raw_loc}** (target <5000, gap = {raw_loc - 5000})\n"
        f"- normalized: **{norm_loc}**\n\n"
        f"## Per-file LOC (descending)\n"
        + "\n".join(f"- {name}: {n}" for name, n in file_loc)
        + "\n\n"
        f"## Unused public declarations {unused_status}\n"
        f"These are reachable-from-`GrothendieckVanishing` is False. Each is a\n"
        f"safe deletion candidate (verify `lake env lean <file>` and "
        f"`lake build` after deleting in case of `@[simp]`/`@[gcongr]` "
        f"hidden uses).\n\n"
        + fmt_unused(unused_items)
        + "\n"
        f"## Remaining `_presheaf` declarations\n"
        f"These are leftover from the Phase-1 sheaf-reversion. Reverting each "
        f"theorem to take `(F : Sheaf X _)` directly typically saves 20-60 "
        f"normalized LOC and removes a wrapper.\n\n"
        + fmt_presheaf(presheaf_decls)
        + "\n"
        f"## Top long proofs by file (body ≥ 50 lines)\n"
        f"Phase-4 golf candidates. Files appear in descending LOC order so "
        f"large files surface first. `ratio = body / signature`; high ratios "
        f"indicate proofs that may compress dramatically.\n\n"
        + fmt_long_proofs(long_proofs, file_loc)
        + "\n"
        f"## Phase 5 (structural) — auto-detected status\n"
        + fmt_phase5()
    )

    STATE_DIR.mkdir(exist_ok=True)
    AUDIT_FILE.write_text(body)
    print(f"wrote {AUDIT_FILE.relative_to(REPO_DIR)} ({len(body)} bytes, "
          f"{elapsed:.1f}s, raw={raw_loc}, norm={norm_loc}, "
          f"unused={len(unused_items)}, presheaf={len(presheaf_decls)})",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
