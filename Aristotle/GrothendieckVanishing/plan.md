# Work Plan — Grothendieck Vanishing
**Date**: 2026-03-27T18:50:00Z

## Status Summary

- **Files**: 7 Lean files, 331 total lines
- **Sorry's**: 2 mathematical (ClosedOpenDecomposition, IrreducibleStep) + 1 intentional axiom (FlasqueVanishing)
- **Build**: passes locally, CI stale (not pushed yet)
- **Aristotle**: 2 jobs submitted (`fca6885d`, `bc3176de`), not tracked in jobs file
- **Proved**: dim 0 base case, induction skeleton, Auxiliary.lean helpers

## Active Multi-Cycle Strategies

1. **Fill the two sorry's** — the core objective. Both are submitted to Aristotle but Aristotle is unreliable for this level of complexity (needs Mathlib infrastructure not yet available: extension by zero, Prop 2.9). Parallel manual work is essential.

2. **Validate the `grothendieck_vanishing_of_irreducible` callback** — critique flagged that the callback may be too weak. Must verify or fix before the sorry can be filled.

## This Cycle's Work Items

### 1. [P0] Fix critique issue #1: Validate/fix `grothendieck_vanishing_of_irreducible` callback (`/prove`)

The callback `ih_irred` only provides vanishing for irreducible Y. But Hartshorne's inner induction on components needs vanishing for the closure of X \ Y₁, which is NOT irreducible.

**Analysis**: The sorry'd proof of `grothendieck_vanishing_of_irreducible` must handle the inner induction on components INTERNALLY. This is possible because:
- For irreducible component Y₁ of X: vanishing on Y₁ comes from `ih_irred` (Y₁ is irreducible, dim Y₁ ≤ dim X)
- For cl(X \ Y₁): need vanishing, but cl(X \ Y₁) has fewer components than X
- The inner induction can recursively decompose cl(X \ Y₁) into its components (each irreducible, dim ≤ dim X) and apply `ih_irred`

So the callback IS sufficient — the inner induction lives inside the sorry'd proof. **No signature change needed.** But we should add a comment documenting this reasoning.

### 2. [P1] Track Aristotle jobs in `aristotle-jobs.json` (`/prove`)

Update the jobs file with the two submitted jobs so `/check-aristotle` can find them.

### 3. [P1] Handle empty space case explicitly (`/prove`)

Add a lemma handling the case where X is empty. When X = ∅, `Sheaf.H F n` should be subsingleton trivially (the constant sheaf on ∅ is zero, Ext from zero is zero). This could be proved directly or added as an explicit case in `grothendieck_vanishing_aux`.

### 4. [P2] Fix documentation: "PROVED" → "ASSEMBLED" in main.lean (`/prove`)

Minor wording fix.

### 5. [P3] Move `topologicalKrullDim_nonneg_of_irreducible` to Auxiliary.lean (`/prove`)

Better code organization.

## Backlog

- **Decompose `grothendieck_vanishing_irreducible_pos`** into sub-lemmas: constant sheaf flasque, Prop 2.9 statement, Z_U SES. Each can be proved or sorry'd independently.
- **Prove constant sheaf on irreducible space is flasque** — this is a concrete, provable sub-lemma.
- **Blueprint 404** — likely not configured for this project; ignore unless user asks.
- **Coarse `import Mathlib`** — low priority, not blocking.
- **Unbundle `TopCat`** — significant refactor, defer.
