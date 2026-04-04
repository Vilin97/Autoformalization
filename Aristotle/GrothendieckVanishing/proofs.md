# Project Status — Grothendieck Vanishing Theorem

**Last updated**: 2026-04-04

## Theorem

Grothendieck's vanishing theorem (Hartshorne III.2.7): for a Noetherian topological space X
of dimension n, and any sheaf F of abelian groups on X, H^i(X, F) = 0 for all i > n.

```lean
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

## Completion: ~99%

**1 logical gap remains**, manifesting as 3 `sorry` keywords in `FiniteGeneratorReduction.lean`.
All three trace to one sub-lemma: `isSheaf_presheaf_filtered_colimit` — proving that a
presheaf-level filtered colimit of sheaves is a sheaf on a Noetherian space (Stacks 009E).

| Location | Statement | Depends on |
|---|---|---|
| L502 | `hexist` — existence half of sheaf gluing | Direct gap |
| L538 | Base case n=0 of `sheafH_filtered_colimit_aux` | L502 via `createsFilteredColimit` |
| L557 | `hQ` — inductive step cokernel vanishing | L502 via `createsFilteredColimit` |

Once `hexist` is closed, all 3 sorry's vanish simultaneously and the main theorem is complete.

## Codebase

- **19 Lean files** in `Aristotle/GrothendieckVanishing/main/`, **5,433 lines** total
- **0 axioms**, 0 admits, 0 `maxHeartbeats` overrides, 0 linter overrides
- No circularity (well-founded induction on Krull dimension + plain N-induction on degree)
- CI: green (Lean Action CI, ~2m40s build time)

## Proof Architecture

The proof proceeds by well-founded induction on `topologicalKrullDim X : WithBot N-infinity`:

```
GrothendieckVanishing.lean        Main theorem (well-founded induction + degree cascade)
├── DimZeroVanishing.lean          Irreducible dim=0: constant sheaf is flasque (PROVED)
│   └── ConstantSheafFlasque.lean  constantSheaf_flasque_of_irreducible (PROVED)
├── IrreducibleStep.lean           Irreducible dim>=1: Steps 1-5 of Hartshorne III.2.7 (PROVED)
│   ├── SheafStalkAlgebra.lean     Stalk algebra + Ext LES lemmas (PROVED)
│   ├── StalkGeneratorAlgebra.lean exists_section_generating_stalks (PROVED)
│   └── FiniteGeneratorReduction.lean  Colimit step (1 SORRY: isSheaf_presheaf_filtered_colimit)
├── ClosedOpenDecomposition.lean   Reduction to irreducible spaces (PROVED)
│   └── ReducibleVanishing.lean    Reducible case via Finset.induction (PROVED)
└── (shared infrastructure, all PROVED)
    ├── SetupCore.lean             Category instances, ClosedImmissionSES
    ├── FlasqueVanishing.lean      Flasque sheaf theory + cohomological vanishing
    ├── FlasqueCohomology.lean     Flasque cohomology helpers
    ├── Setup.lean                 Wrapper theorems
    ├── ClosedImmersion.lean       Closed immersion counit/stalk
    ├── ZeroOutside.lean           Extension-by-zero sheaf machinery
    ├── ZeroOutsideFinset.lean     Finset-indexed extension-by-zero
    ├── CohomologyIso.lean         H'(top, F) isomorphic to H(F)
    └── Auxiliary.lean             Topology/dimension helpers
```

## The Remaining Gap: `hexist`

### What it is

The existence half of the sheaf gluing condition for a presheaf-level filtered colimit.
Given a compatible family `sf` of sections over an open cover `U`, construct a global section
`s` of the colimit presheaf `c.pt` with `s|_{U_i} = sf_i` for all `i`.

The separation half (`hsep`) was closed on 2026-04-04. The full proof chain:
1. Representative lifting via `Concrete.isColimit_exists_rep`
2. Restriction-maps-to-zero via `NatTrans.naturality`
3. Eventually-zero via `Types.FilteredColimit.isColimit_eq_iff'`
4. Common index via `filtered_colimit_kills_all_restrictions`
5. Sheaf separation via `sheaf_section_zero_of_zero_on_finite_cover`
6. Cocone factorization via `c.iota.naturality`

### Proof plan for `hexist` (~120-150 lines)

All building blocks are proved and compiled:
- `filtered_colimit_kills_all_restrictions_gen` (generalized merge of transitions)
- `colimit_presheaf_sep` (separation for `c.pt` at any open)
- `sheaf_section_zero_of_zero_on_finite_cover`

Steps:
1. Choose representatives for finite subcover and merge to common index via `IsFiltered.sup`
2. Check pairwise compatibility in common piece via `isColimit_eq_iff'` + merge
3. Glue in the piece via sheaf condition (`IsSheafUniqueGluing`)
4. Map to colimit via cocone morphism
5. Verify `s|_{U_k} = sf_k` for k in finite subcover (by construction)
6. Verify for general i via `colimit_presheaf_sep`
7. Package as `Presheaf.IsGluing`

Risk: **low** (standard argument, Stacks 009E). Effort: **medium** (mechanical complexity).

## Progress Timeline

| Date | Sorry's | Milestone |
|---|---|---|
| Mar 10 | ~23 | Initial proof skeleton |
| Mar 15 | 7 | Focus shift to Grothendieck vanishing |
| Mar 28 | 4 | ReducibleVanishing proved, major sub-goals closed |
| Mar 31 | 2 | Consolidation to single logical gap |
| Apr 2 | 1 (3 kw) | Infrastructure complete, FlasqueVanishing proved |
| Apr 3 | 1 (3 kw) | hsep closed, hexist proof plan written |

## Automated Prover (Aristotle)

Active jobs targeting the remaining sorry:
- `1676d0c9`: `sheafH_preserves_filtered_colimits` (in progress)
- `b1902f2c`: `isSheaf_presheaf_filtered_colimit` (queued)
- `782d0f32`: abstract categorical version (in progress, 38%)

## Backlog

- P1: Fix blueprint/docs 404
- P3: Delete 5 dead theorems/definitions
- P3: Fix 3 stale docstrings
- P3: Split FlasqueVanishing.lean (>600 lines)
- P3: Generalize `AddCommGrpCat` to `ModuleCat R`
- P4: Replace blanket `import Mathlib` with specific imports
