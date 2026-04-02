# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-02T18:00Z
**Reviewer verdict**: CONDITIONAL PASS

## 1. Sorry's (2)

Two `sorry` terms, both in `IrreducibleStep.lean`:
- **Line 1235**: `ext_comm_filtered_colimit_mono_zero` (n=0 base case)
- **Line 1250**: `ext_comm_filtered_colimit_mono_succ` (n+1 inductive step)

Both are sub-lemmas of `ext_comm_filtered_colimit_mono`. The parent theorem and
`cohomology_vanishing_of_finitelyGenerated_vanishing` are proved modulo these two.

CLAUDE.md and plan.md claim "1 sorry remains" but there are **2 sorry terms**. The
discrepancy arises because the documents count `ext_comm_filtered_colimit_mono` as one
logical sorry, but the Lean kernel sees two distinct `sorry` invocations.

**Assessment**: Genuine Mathlib API gap (Ext^n commutes with filtered colimits of mono
diagrams). Cannot be closed without new Mathlib infrastructure.

## 2. Hidden Axioms

None. No `admit`, `axiom`, or `native_decide` in any `.lean` file.

Note: IrreducibleStep.lean line 1259 comment says "This is the ONLY axiom in the
formalization" referring to a `theorem` with sorry inside. This is misleading
terminology (it is not a Lean `axiom` declaration) but not a soundness issue.

## 3. File Sizes

- `IrreducibleStep.lean`: **1609 lines** (over 1000-line guideline)

**Recommendation**: Extract `ext_comm_filtered_colimit_mono*` and the filtered diagram
infrastructure (lines ~1210-1400) into a dedicated file. Low priority.

## 4. Heartbeat Overrides

None in `main/*.lean`. All proofs compile within default 200000 heartbeats.

CLAUDE.md line 65 references "Existing violations in SetupCore.lean" but there are none.
That documentation is stale.

## 5. Stale Comments

| File | Line(s) | Issue |
|------|---------|-------|
| `main.lean` | 7-11 | Header lists 2 sorry's (`ext_comm_filtered_colimit_mono` + `cohomology_vanishing_of_finitelyGenerated_vanishing`) but the latter is now proved |
| `main.lean` | 16 | Says "IrreduciblePosVanishing (2 sorry's inside)" — the 2 sorry's are in sub-lemmas of `ext_comm_filtered_colimit_mono`, not directly inside `IrreduciblePosVanishing` |
| `GrothendieckVanishing.lean` | 8-10 | Says "modulo 2 sorry's... Ext filtered colimits + Hartshorne 2.9" but Hartshorne 2.9 is proved |
| `IrreducibleStep.lean` | 1259 | Calls the sorry "the ONLY axiom" — it is not a Lean `axiom`, and there are 2 sorry terms not 1 |

## 6. Documentation Consistency

| Doc | Issue |
|-----|-------|
| `CLAUDE.md` code structure | Missing `FlasqueVanishing.lean` (616 lines, split from SetupCore). Says FlasqueVanishing lives in SetupCore.lean — it does not. |
| `CLAUDE.md` line 65 | References "Existing violations in SetupCore.lean" for heartbeat overrides — there are none. |
| `CLAUDE.md` line 75 | Says "1 sorry remains" — there are 2 sorry terms. Acceptable if counting logical gaps (1 gap, 2 sub-lemmas). |
| `plan.md` line 9 | Says "~6600 lines" — actual total is 5074 lines. |
| `plan.md` line 8 | Says "1" sorry — same counting caveat as CLAUDE.md. |

## 7. Open Issues

1. **P1 — Stale sorry counts in file headers** (main.lean, GrothendieckVanishing.lean, IrreducibleStep.lean): multiple comments reference outdated sorry counts or list proved lemmas as sorry.
2. **P2 — CLAUDE.md code structure is stale**: `FlasqueVanishing.lean` missing from tree; SetupCore description wrong; heartbeat violation reference outdated.
3. **P3 — File size** (IrreducibleStep.lean 1609 lines) — splitting is disruptive but would improve maintainability.
4. **P3 — plan.md line count** ("~6600") is inflated vs actual (5074).
