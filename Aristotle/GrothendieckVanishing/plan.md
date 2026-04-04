# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-03T21:05Z

## Status Summary
- **Sorry count**: 3 keywords, 1 logical gap (`isSheaf_presheaf_filtered_colimit`)
- **Files**: 16 `.lean` in `main/`, 5155 total lines
- **CI**: Green (all 3 latest runs pass)
- **Aristotle**: No active jobs
- **Docs**: 404 (blueprint broken)
- **Dead code**: 5 dead theorems/defs identified in critique

## Active Multi-Cycle Strategy

**Closing `isSheaf_presheaf_filtered_colimit`** (the last sorry):

The proof is partially scaffolded at FiniteGeneratorReduction.lean:191-202:
```
isSheaf_iff_isSheafUniqueGluing → intro cover → obtain finite subcover → ???
```

The gap after obtaining finite subcover `t` is:
1. Reduce unique gluing for the full cover `U` to unique gluing for the finite subcover `U ∘ t`
2. Show the presheaf colimit satisfies unique gluing for the finite subcover
3. Key insight: sheaf condition for finite cover = finite limit, and filtered colimits commute with finite limits (`colimitLimitIso`)

This is Stacks 009E. The approach: show that a compatible family on `U` restricts to a compatible family on the finite subcover, construct the gluing via the finite subcover, and use the cover refinement to get uniqueness for the full cover.

**Alternative approach**: Instead of `isSheafUniqueGluing`, use `Presheaf.isSheaf_of_isLimit` or similar Mathlib API that directly relates sheaf condition to finite limits, avoiding manual gluing.

## This Cycle's Work Items

1. **Delete dead code** (P3, `/cleanup`) — immediate, 2 min
   - Delete `ext_sandwich` + `addCommGrpCat_exact_sandwich` from FiniteGeneratorReduction.lean:29-63
   - Delete `subsingleton_ext_of_ses` + `subsingleton_ext_of_ses_middle` from SheafStalkAlgebra.lean:23-51
   - `createsFilteredColimit` stays — it's used by the sorry resolution path

2. **Fix stale docstrings** (P3, `/simplify`) — immediate, 2 min
   - main.lean:12 — SetupCore description wrong
   - SheafStalkAlgebra.lean:5 — claims to contain lemmas that are elsewhere
   - FiniteGeneratorReduction.lean:5 — lists dead code as key results

3. **Submit `isSheaf_presheaf_filtered_colimit` to Aristotle** (`/submit-aristotle`) — 1 min
   - May need to extract as standalone lemma for submission

4. **Work on `isSheaf_presheaf_filtered_colimit` directly** (P1, `/prove`) — main effort
   - Strategy: after obtaining finite subcover `t`, construct the gluing section
   - For existence: each `Y'.obj j` is a sheaf, so compatible sections on `U` glue in each `Y'.obj j`; the colimit of these gluings gives the global section
   - For uniqueness: if two global sections agree on each `U i`, they agree on the colimit
   - Key Mathlib lemma needed: `TopCat.Presheaf.IsSheafUniqueGluing` API for working with finite subcovers

5. **Work on L230 (base case n=0)** (P1, `/prove`) — if L202 progress made
   - Uses `createsFilteredColimit` → need L202 first
   - Alternative: prove directly that if `Ext^0(Z, F_j) = 0` for all j, then `Ext^0(Z, colim F_j) = 0`, using that `Ext^0 ≅ Hom` and Hom preserves filtered colimits in Grothendieck abelian categories

6. **Work on L249 (hQ)** (P1, `/prove`) — if L202 progress made
   - Construct the cokernel diagram: for each j, `Q_j = coker(Y'.obj j → I)`
   - Show `Q = colim Q_j` (cokernels commute with filtered colimits)
   - Apply IH: each `H^n(Q_j) = 0` by LES, so `H^n(Q) = 0`

## Backlog
- P1: Fix docs 404 (blueprint deployment)
- P3: Split FlasqueVanishing.lean (616 lines)
- P3: Generalize to ModuleCat R
- P4: Replace blanket `import Mathlib` with specific imports
