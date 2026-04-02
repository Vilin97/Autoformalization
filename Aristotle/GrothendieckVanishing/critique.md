# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-02T18:35Z
**Reviewer verdict**: CONDITIONAL PASS

## 0. CI Status

Latest CI run (push dd87a8d) is **in_progress**. Previous runs both **green**.
Local `lake build` succeeds with 0 errors.

**Docs deployment is BROKEN**: both `https://vilin97.github.io/aristotle/blueprint/` and
`https://vilin97.github.io/aristotle/blueprint/dep_graph_document.html` return **HTTP 404**.

**Assessment**: P1 — docs are inaccessible.

## 1. Sorry's (2, decomposed from 1)

Two sorry terms in `IrreducibleStep.lean`, both inside `ext_comm_filtered_colimit_mono`:
- Line 1238: `hom_subsingleton_of_filtered_colimit_mono` (n=0 case: Hom preserves colimit)
- Line 1262: inductive step (n≥1: Ext case, genuine Mathlib gap)

The n=0 case is properly wired via `Nat.induction` — proving the sub-lemma
auto-closes the zero case. The n≥1 case requires infrastructure not in Mathlib.

Both statements are mathematically true (Hartshorne III.2.9). No risk of falsity.

## 2. Hidden Axioms

None. No `admit`, `axiom`, `native_decide`, or linter/heartbeat overrides.

## 3. File Sizes

- `IrreducibleStep.lean`: **1582 lines** (over 1000-line guideline by 58%)

25 `private` declarations. Should be split: extract filtered diagram infrastructure
(~1238-1357) and finitely generated vanishing (~1359-1515) into a separate file.

## 4. Dead Code: Cascade Theorems

`sheafH_vanishing_succ` and `sheafH_vanishing_cascade` in `GrothendieckVanishing.lean`
are **private and never used** outside their own file. Neither is called from
`grothendieck_vanishing_aux` or `GrothendieckVanishing`. Dead code.

## 5. Documentation Issues

All previously flagged issues (misleading "axiom" comment, "m₀ ≥ 1" docstring,
stale CLAUDE.md tree) were fixed in commit 8da54d7. No new issues detected.

## 6. Generalization Opportunities

1. **Drop NoetherianSpace from cascade theorems**: `sheafH_vanishing_succ` doesn't
   use `NoetherianSpace` — remove the unneeded `[NoetherianSpace X]` hypothesis.
   **Feasibility: trivial.**

2. **Drop mono condition from sorry**: Hartshorne III.2.9 states the result WITHOUT
   mono transitions. The mono condition is not necessary for the mathematical truth.
   **Feasibility: hard (proof infrastructure not in Mathlib).**

3. **Generalize to arbitrary Grothendieck topologies**: The theorem currently works
   for `Opens.grothendieckTopology` on `TopCat`. The cascade theorems already work
   for arbitrary sites. The sorry could be stated for general sites too.
   **Feasibility: moderate.**

## 7. Mathlib Upstreamability

1. **Cascade theorems**: General facts about Ext + injective presentations. Could go
   to `Mathlib.CategoryTheory.Sites.SheafCohomology` after making non-private and
   dropping `NoetherianSpace`.

2. **Filtered diagram of finitely generated subsheaves**: `finsetGenFunctor` etc.
   could be useful for other colimit arguments on Noetherian spaces.

## 8. Open Issues

| # | Priority | Issue |
|---|----------|-------|
| 1 | P0 | 2 sorry's in `ext_comm_filtered_colimit_mono` (lines 1238, 1262) |
| 2 | P1 | Docs/blueprint return 404 |
| 3 | P2 | IrreducibleStep.lean at 1584 lines — split |
| 4 | P2 | Dead code: cascade theorems unused |
