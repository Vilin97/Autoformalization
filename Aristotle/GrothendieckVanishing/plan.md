# Work Plan — Grothendieck Vanishing
**Date**: 2026-03-27T19:05:00Z (Cycle 2)

## Status Summary

- **Files**: 7 Lean files, ~330 lines
- **Sorry's**: 2 mathematical + 1 axiom (unchanged from cycle 1)
- **Build**: passes, pushed as `a993c3f`
- **Aristotle**: 2 jobs in progress (fca6885d at 16%, bc3176de at 8%)
- **Done from cycle 1**: jobs tracked, docs fixed, code reorganized

## Active Multi-Cycle Strategies

1. **Fill the two sorry's** — Aristotle working on both. Manual decomposition needed in parallel.
2. **Callback validation** — Confirmed in cycle 1 that callback IS sufficient (inner induction lives inside the sorry'd proof). Document with comment.

## This Cycle's Work Items

### 1. [P1] Prove vanishing for empty space (`/prove`)

When X is empty, `Sheaf.H F n` should be trivially subsingleton. Add this as a standalone lemma in `Auxiliary.lean` and use it as an early exit in `grothendieck_vanishing_aux`. This closes critique issue #5.

### 2. [P1] Decompose `grothendieck_vanishing_irreducible_pos` into sub-lemmas (`/prove`)

Extract named sub-lemmas from IrreducibleStep.lean:
- `constantSheaf_flasque_of_irreducible`: constant sheaf Z on irreducible space has epi restrictions — attempt to prove
- `cohomology_direct_limit_noetherian` (Prop 2.9): sorry, statement only
- `constantSheaf_vanishing_of_irreducible`: vanishing for Z itself — follows from flasque + FlasqueVanishing

### 3. [P2] Add comment documenting callback sufficiency (`/prove`)

Add a comment in ClosedOpenDecomposition.lean explaining why the callback only needs irreducible Y.

## Backlog

- Prove constant sheaf flasque on irreducible space (hard — needs sheafification internals)
- Blueprint 404 — not blocking
- Coarse imports — not blocking
- Unbundle TopCat — defer
