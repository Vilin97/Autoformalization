#!/usr/bin/env python3.9
"""
Comprehensive initial scan for the compress loop.

Combines four signals into a single `compress_tasks.md`:

  1. Phase 1 (hardcoded): the reviewer-flagged `(F : Presheaf X) (hF : F.IsSheaf)` →
     `(F : TopCat.Sheaf AddCommGrpCat.{u} X)` reversion. This is the highest-leverage
     change per the reviewer (CohomologyAPI:1734-1776 should be ~1 line).

  2. Phase 2 — unused declarations (from `lake env lean scripts/unused_decls.lean`).

  3. Phase 3 — repeated tactic blocks (from `find_repeated_blocks.py`).

  4. Phase 4 — long proofs / simple statements (a fresh scanner: declarations whose
     proof body is dramatically larger than their signature).

Periodically re-run by the auditor; full output is overwritten in
`.compress-state/compress_tasks.md`.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

REPO_DIR = Path(__file__).resolve().parent.parent
MAIN_DIR = REPO_DIR / "Aristotle" / "GrothendieckVanishing" / "main"
STATE_DIR = REPO_DIR / ".compress-state"

# Decl-start pattern: optional attributes/modifiers, then a kind keyword, then a name.
DECL_START = re.compile(
    r"^(?:(?:@\[[^\]]*\]|private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|class|structure|inductive)\s+"
    r"([\w\.]+)"
)


@dataclass
class Decl:
    file: Path
    name: str
    kind: str
    start_line: int  # 1-indexed
    end_line: int    # 1-indexed inclusive
    signature_lines: int
    body_lines: int

    @property
    def total_lines(self) -> int:
        return self.end_line - self.start_line + 1


def parse_decls(path: Path) -> list[Decl]:
    text = path.read_text()
    lines = text.splitlines()
    decls: list[Decl] = []
    starts: list[tuple[int, str, str]] = []  # (line idx, kind, name)
    for i, line in enumerate(lines):
        m = DECL_START.match(line)
        if m:
            starts.append((i, m.group(1), m.group(2)))
    starts.append((len(lines), "", ""))  # sentinel
    for k, (i, kind, name) in enumerate(starts[:-1]):
        next_i = starts[k + 1][0]
        block = lines[i:next_i]
        # Trim trailing blank lines from the block so the end_line is the last
        # non-blank line of the declaration.
        while block and not block[-1].strip():
            block.pop()
        if not block:
            continue
        # Signature/body split: signature is the part up to and including the
        # line that introduces the body (`:=` or `where` or `:= by` etc.).
        sig_count = len(block)
        for j, ln in enumerate(block):
            if ":=" in ln or ln.strip() == "where" or ln.endswith(" where"):
                sig_count = j + 1
                break
        body_count = len(block) - sig_count
        decls.append(Decl(
            file=path,
            name=name,
            kind=kind,
            start_line=i + 1,
            end_line=i + len(block),
            signature_lines=sig_count,
            body_lines=body_count,
        ))
    return decls


def all_decls() -> list[Decl]:
    out: list[Decl] = []
    for path in sorted(MAIN_DIR.glob("*.lean")):
        out.extend(parse_decls(path))
    return out


def long_proof_candidates(decls: list[Decl], top: int = 40) -> list[Decl]:
    """Top declarations by body line count. Worker uses this list to find
    proofs that look golfable."""
    return sorted(decls, key=lambda d: d.body_lines, reverse=True)[:top]


def simple_statement_candidates(decls: list[Decl], min_body: int = 15) -> list[Decl]:
    """Declarations with a short signature relative to their body. Heuristic
    threshold: body ≥ 15 lines AND body / signature ≥ 4."""
    return sorted(
        [d for d in decls
         if d.body_lines >= min_body and d.body_lines / max(1, d.signature_lines) >= 4],
        key=lambda d: d.body_lines / max(1, d.signature_lines),
        reverse=True,
    )[:30]


def run_unused_decls(timeout: int = 600) -> str:
    """Run `lake env lean scripts/unused_decls.lean` and return the captured
    output (stderr+stdout). Returns "" on failure (reported but non-fatal —
    the loop can re-run later)."""
    cmd = ["lake", "env", "lean", "scripts/unused_decls.lean"]
    try:
        result = subprocess.run(
            cmd,
            cwd=REPO_DIR,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return ""
    return (result.stdout or "") + "\n" + (result.stderr or "")


def parse_unused(output: str) -> list[tuple[str, str]]:
    """Extract `(module, decl)` from `#find_unused` output.

    Lean's logWarning prefixes each line with
        scripts/unused_decls.lean:NN:0: warning:
    after which the body is `  [ModuleName]` (group header) or
    `    DeclName` (an indented declaration). We strip the prefix and parse the body.
    """
    prefix_re = re.compile(r"^scripts/unused_decls\.lean:\d+:\d+:\s*warning:\s?")
    module_re = re.compile(r"^\[Aristotle\.GrothendieckVanishing\.main\.([\w\.]+)\]\s*$")
    items: list[tuple[str, str]] = []
    current_module = ""
    for raw in output.splitlines():
        body = prefix_re.sub("", raw, count=1)
        if body == raw:
            continue  # not a warning line
        stripped = body.strip()
        m = module_re.match(stripped)
        if m:
            current_module = m.group(1).split(".")[-1]
            continue
        if not current_module:
            continue
        # Decl lines: a single identifier path (no spaces, contains alnum/dot/unicode).
        if re.fullmatch(r"[\w\.\₁₂₃₄₅₆₇₈₉₀]+", stripped):
            # Skip auto-generated `.congr_simp` artifacts — those exist because Lean
            # emits them for `simp` lemmas; deleting the parent decl removes them.
            if stripped.endswith(".congr_simp"):
                continue
            items.append((current_module, stripped))
    return items


def run_repeated_blocks(min_lines: int = 4, timeout: int = 120) -> str:
    cmd = [
        "python3.9",
        "scripts/find_repeated_blocks.py",
        "Aristotle/GrothendieckVanishing/main/",
        "--min-lines",
        str(min_lines),
        "--min-occurrences",
        "2",
    ]
    try:
        result = subprocess.run(
            cmd,
            cwd=REPO_DIR,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return ""
    return result.stdout or ""


def parse_repeated_block_summary(output: str, top_n: int = 8) -> list[dict]:
    """Pick the top-N repeated blocks by `potential savings`. Each entry
    captures the headline line and the first 3 occurrences for the worker."""
    blocks: list[dict] = []
    current: dict | None = None
    for raw in output.splitlines():
        line = raw.rstrip()
        m = re.match(r"^#(\d+):\s*(\d+)\s*lines\s*×\s*(\d+)\s*occurrences\s*\(potential savings:\s*~(\d+)\s*lines\)", line)
        if m:
            if current is not None:
                blocks.append(current)
            current = {
                "rank": int(m.group(1)),
                "block_lines": int(m.group(2)),
                "occurrences": int(m.group(3)),
                "savings": int(m.group(4)),
                "locations": [],
                "snippet": [],
            }
            continue
        if current is None:
            continue
        m = re.match(r"^\s+([\w\./]+\.lean):(\d+)$", line)
        if m:
            current["locations"].append(f"{m.group(1)}:{m.group(2)}")
            continue
        if line and not line.startswith("=") and not line.startswith("Found"):
            current["snippet"].append(line)
    if current is not None:
        blocks.append(current)
    blocks.sort(key=lambda b: -b["savings"])
    return blocks[:top_n]


PHASE1_TEMPLATE = """## Phase 1: Sheaf reversion (highest leverage; reviewer-flagged)

The previous refactor over-applied the `(F : Presheaf X) (hF : F.IsSheaf)`
public idiom. Many lemmas should take `(F : TopCat.Sheaf AddCommGrpCat.{u} X)`
directly, especially when several presheaf+IsSheaf triples are packaged into
`(⟨F, h⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)` inside the theorem statement.

Canonical example: `CohomologyAPI.lean:1734-1776` is a 43-line theorem with
**six** `(F : Presheaf) (h : F.IsSheaf)` triples and six `(⟨F, h⟩ : Sheaf …)`
packagings inside a `ShortComplex.mk` body. It should be ~1 line if it took
`(S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))` directly.

Mechanical signal: `find_repeated_blocks.py` reports 40 occurrences of the
7-line `(X₁ := ⟨F₁, h₁⟩ : TopCat.Sheaf …) (X₂ := …) (X₃ := …)` packaging
boilerplate, with ~273 lines of potential savings. Phase 1 is the single
highest-leverage area in the entire compress loop.

- [ ] In `CohomologyAPI.lean`, rewrite each theorem that takes one or more
      `(F : Presheaf X) (h : F.IsSheaf)` triples and ends up packaging them
      into `(⟨F, h⟩ : Sheaf …)` inside its body. Replace each triple with a
      single `Sheaf` argument, delete the corresponding `_presheaf` wrapper
      where the sheaf-level lemma was the underlying truth, and propagate
      the change to call sites in the same file. Target: at least 600 LOC
      removed from `CohomologyAPI.lean`.
      COMPLETE_IF: test $(wc -l < Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean) -lt 1200

- [ ] Repeat the Phase-1 reversion across `FlasqueVanishing.lean`,
      `PresheafFilteredColimit{,Core,General}.lean`, `IrreducibleStep.lean`,
      `ClosedImmersion.lean`, `ClosedImmersionCohomology.lean`, and any other
      file with multi-arg `IsSheaf` packaging. Target: total `main/*.lean`
      raw `wc -l` below 6500 once Phase 1 is done across the tree.
      COMPLETE_IF: test $(cat Aristotle/GrothendieckVanishing/main/*.lean | wc -l) -lt 6500
"""


def extract_phase5(existing_path: Path) -> str:
    """Preserve a `## Phase 5: Structural opportunities` section verbatim.

    The auditor periodically rescans and overwrites `compress_tasks.md`. Phase 5
    is hand-curated (sourced from `structural_ideas.md`) and must survive.
    """
    if not existing_path.exists():
        return ""
    text = existing_path.read_text()
    marker = "## Phase 5: Structural opportunities"
    idx = text.find(marker)
    if idx == -1:
        return ""
    section = text[idx:]
    # Trim a trailing horizontal rule if a future Phase 6 is appended.
    next_phase = section.find("\n## Phase 6")
    if next_phase != -1:
        section = section[:next_phase]
    return section.rstrip() + "\n"


def write_compress_tasks(
    decls: list[Decl],
    unused_items: list[tuple[str, str]],
    repeated_blocks: list[dict],
    output_path: Path,
) -> None:
    long_proofs = long_proof_candidates(decls)
    simple_stmt = simple_statement_candidates(decls)
    preserved_phase5 = extract_phase5(output_path)

    lines: list[str] = []
    lines.append("# Compress Tasks")
    lines.append("")
    lines.append("Mechanically-derived task list seeded by the initial comprehensive scan.")
    lines.append("Each task may have a `COMPLETE_IF: <shell>` line; the loop controller")
    lines.append("does NOT flip to `- [x]` unless that command exits 0.")
    lines.append("")
    lines.append("Markers:")
    lines.append("- `- [ ]` = not started")
    lines.append("- `- [>]` = in progress (multi-cycle, may be re-targeted)")
    lines.append("- `- [x]` = complete")
    lines.append("")
    lines.append("Hard rules (enforced by the gate, not just by the prompts):")
    lines.append("- Every committed cycle MUST decrease normalized LOC")
    lines.append("  (`python3.9 scripts/normalized_loc.py`). No scaffolding cycles.")
    lines.append("- Deleting comments or blank lines does NOT count as compression.")
    lines.append("- Stacking tactics on one line via `;` or `<;>` does NOT count.")
    lines.append("- 0 sorry's, 0 axioms, 0 admits must be preserved.")
    lines.append("- Loop stops when raw `wc -l` of `main/*.lean` < 5000.")
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append(PHASE1_TEMPLATE)
    lines.append("---")
    lines.append("")
    lines.append("## Phase 2: Unused declarations")
    lines.append("")
    lines.append("Auto-extracted from `lake env lean scripts/unused_decls.lean`. Each item")
    lines.append("is a public declaration not transitively reached from `GrothendieckVanishing`.")
    lines.append("Verify reachability before deletion (private helpers it depends on may also")
    lines.append("become unreachable, cascading the deletion).")
    lines.append("")
    if not unused_items:
        lines.append("- _(scan reported no unused public declarations; rerun via auditor)_")
    else:
        for module, name in unused_items:
            lines.append(f"- [ ] Delete unused declaration `{name}` from `{module}.lean` "
                         f"(and any helpers it depended on that become unreachable).")
            lines.append(f"      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) {re.escape(name)}\\b' Aristotle/GrothendieckVanishing/main/{module}.lean")
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Phase 3: Factor repeated tactic blocks")
    lines.append("")
    lines.append("Auto-extracted from `find_repeated_blocks.py --min-lines 4`. Each entry is a")
    lines.append("multi-line tactic block that recurs ≥2x. Many of these will dissolve once")
    lines.append("Phase 1 is done — DO NOT extract a helper for a block that will go away after")
    lines.append("the Sheaf reversion. Only factor when the block is irreducibly necessary.")
    lines.append("")
    if not repeated_blocks:
        lines.append("- _(scan reported no repeated blocks at the configured threshold)_")
    else:
        for block in repeated_blocks:
            head_locs = ", ".join(block["locations"][:3])
            more = "" if len(block["locations"]) <= 3 else f" (+{len(block['locations']) - 3} more)"
            snippet = " / ".join(s.strip() for s in block["snippet"][:2] if s.strip())
            lines.append(
                f"- [ ] Repeated {block['block_lines']}-line block × {block['occurrences']} "
                f"(potential savings: ~{block['savings']} lines). First sites: "
                f"{head_locs}{more}. Snippet head: `{snippet[:120]}`. Decide whether "
                f"Phase 1 already eliminates it; otherwise factor a single helper."
            )
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Phase 4: Long proofs / simple statements")
    lines.append("")
    lines.append("Top declarations by body line count, plus declarations whose body is ≥4x their")
    lines.append("signature (the \"simple statement, long proof\" heuristic). These are golf")
    lines.append("candidates: a 60-line proof for a 3-line statement usually has a 10-line core.")
    lines.append("")
    lines.append("Top 40 declarations by body line count:")
    lines.append("")
    for d in long_proof_candidates(decls):
        rel = d.file.relative_to(REPO_DIR)
        lines.append(f"- [ ] Golf `{d.name}` in `{rel}:{d.start_line}` "
                     f"(signature {d.signature_lines}L, body {d.body_lines}L). "
                     "Look for redundant `simp` chains, manual `rfl`s after `simp`, "
                     "unfolded `apply` sequences that `exact?`/`aesop` could close.")
    lines.append("")
    lines.append("Body-to-signature ratio outliers (≥4x, body ≥ 15 lines):")
    lines.append("")
    if not simple_stmt:
        lines.append("- _(no outliers at the configured threshold)_")
    else:
        for d in simple_stmt:
            rel = d.file.relative_to(REPO_DIR)
            ratio = d.body_lines / max(1, d.signature_lines)
            lines.append(f"- [ ] Golf `{d.name}` in `{rel}:{d.start_line}` "
                         f"(body/sig ratio {ratio:.1f}, body {d.body_lines}L, sig {d.signature_lines}L).")
    lines.append("")

    if preserved_phase5:
        lines.append("---")
        lines.append("")
        lines.append(preserved_phase5)
    else:
        lines.append("---")
        lines.append("")
        lines.append("## Phase 5: Structural opportunities")
        lines.append("")
        lines.append("See `.compress-state/structural_ideas.md` for the durable backlog of")
        lines.append("higher-leverage cross-file restructurings the auto-scanner cannot detect.")
        lines.append("Pick an entry-point cycle from there when mechanical Phase 1-4 items")
        lines.append("offer only small yields.")
        lines.append("")

    output_path.write_text("\n".join(lines) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compress loop initial scan")
    parser.add_argument("--skip-unused", action="store_true",
                        help="Skip the slow lake env lean scripts/unused_decls.lean step")
    parser.add_argument("--output", type=Path,
                        default=STATE_DIR / "compress_tasks.md")
    args = parser.parse_args()

    print("Parsing main/*.lean for declarations...")
    decls = all_decls()
    print(f"  {len(decls)} declarations across {len(set(d.file for d in decls))} files")

    if args.skip_unused:
        print("Skipping unused-decl scan (--skip-unused).")
        unused_items: list[tuple[str, str]] = []
    else:
        print("Running unused-decl scan (lake env lean scripts/unused_decls.lean)...")
        unused_output = run_unused_decls()
        unused_items = parse_unused(unused_output)
        print(f"  {len(unused_items)} unused public declarations")

    print("Running find_repeated_blocks.py...")
    rep_output = run_repeated_blocks()
    repeated_blocks = parse_repeated_block_summary(rep_output)
    print(f"  {len(repeated_blocks)} repeated-block clusters surfaced")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    write_compress_tasks(decls, unused_items, repeated_blocks, args.output)
    print(f"Wrote {args.output.relative_to(REPO_DIR)}")


if __name__ == "__main__":
    main()
