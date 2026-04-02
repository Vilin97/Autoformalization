# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-02T03:00Z
**Reviewer verdict**: CONDITIONAL PASS

## 0. CI Status

CI GREEN on PR #5. Auto-merge pending rebase.

## 1. Sorry's (1)

Only `cohomology_vanishing_of_finitelyGenerated_vanishing` (line 1227 of IrreducibleStep.lean).

This is Hartshorne 2.9: "if H^m = 0 for all f.g. subsheaves, then H^m(K) = 0". Requires Ext commuting with filtered colimits — not in Mathlib v4.28.0. The Grothendieck abelian structure (`Sheaf.instIsGrothendieckAbelian`) and `extFunctorObj` exist, but `PreservesFilteredColimits (extFunctorObj Z m)` does not.

**Assessment**: Genuine Mathlib API gap. Cannot be closed without new Mathlib infrastructure.

## 2. Hidden Axioms

None. No `admit`, `axiom`, or `native_decide`.

## 3. File Sizes

- `IrreducibleStep.lean`: 1430 lines (over 1000-line guideline, but contains the entire inductive step)
- `ZeroOutside.lean`: 733 lines
- `FlasqueVanishing.lean`: 616 lines

**Recommendation**: IrreducibleStep.lean could be split (e.g., extract stalk lemmas, finset infrastructure). Low priority.

## 4. Heartbeat Overrides

None. All proofs compile within default 200000 heartbeats.

## 5. Stale Comments

Lines 10 and 317 of IrreducibleStep.lean reference "2 sorry's" in comments but only 1 remains. Should be updated.

## 6. Documentation

- `plan.md`: Up to date (1 sorry)
- `CLAUDE.md`: Up to date (1 sorry)
- `critique.md`: This file (freshly written)

## 7. Open Issues

1. ~~**P2 — Stale sorry count in file header comments**~~ FIXED
2. **P3 — File size** (IrreducibleStep.lean 1430 lines) — low priority, splitting is disruptive
3. **P3 — Docs deployment** (blueprint 404s — preexisting, out of scope)
