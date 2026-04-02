# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-02T08:30Z
**Reviewer verdict**: CONDITIONAL PASS

## 0. CI Status

CI GREEN on PR #5. Auto-merge pending rebase. Local changes (decomposition) not yet pushed.

## 1. Sorry's (2 — decomposed from 1)

Both in IrreducibleStep.lean:

1. **`ext_comm_filtered_colimit_mono`** (line ~1229): Pure categorical statement — Ext^n(Z,-)
   preserves filtered colimits of mono diagrams in Grothendieck abelian categories. The n=0
   case follows from `preservesColimit_coyoneda_obj_of_mono`; higher n requires dimension
   shifting via injective presentations + LES (quotient system has epi, not mono, transitions).

2. **`cohomology_vanishing_of_finitelyGenerated_vanishing`** (line ~1246): Applies (1) to
   the specific sheaf case. Needs the filtered diagram construction + `ext_comm_filtered_colimit_mono`.

**Assessment**: Both are genuine Mathlib API gaps. The decomposition isolates the categorical
core (`ext_comm_filtered_colimit_mono`) from the sheaf-specific application.

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

1. **P2 — Stale sorry count in file header comments** (IrreducibleStep.lean lines 10, 317 — may reference "1 sorry" but now 2 after decomposition)
2. **P3 — File size** (IrreducibleStep.lean ~1450 lines after decomposition)
3. **P3 — Docs deployment** (blueprint 404s — preexisting)
