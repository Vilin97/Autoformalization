# Summary of changes
## Summary

I made significant progress on the formalization of Hartshorne III.2.7 Step 1 (reduction from general Noetherian spaces to irreducible ones).

### What was accomplished

The main theorem `grothendieck_vanishing_of_irreducible` is structured into three cases:

1. **Empty X** (fully proved): I proved that on the empty topological space, every abelian sheaf is a zero object (`sheaf_isZero_of_isEmpty`). The proof uses a novel argument: the empty sieve vacuously covers every open set in the empty space, and the sheaf condition for this sieve forces `Hom(E, F(U))` to be subsingleton for all `E` and `U`. Taking `E = F(U)` shows `End(F(U))` is subsingleton, so `id = 0`, meaning `F(U)` is trivial. Since all presheaf values are trivial, `F` is `IsZero`. Then `HasProjectiveDimensionLT.subsingleton` gives vanishing of all Ext groups from a zero object.

2. **Irreducible X** (fully proved): Direct application of the hypothesis `ih_irred` with `Y = X`, using `le_rfl` for the dimension bound.

3. **Reducible X** (one `sorry` remains): The lemma `sheaf_H_subsingleton_of_reducible` requires infrastructure not yet available in Mathlib v4.28.0, specifically:
   - The extension-by-zero / closed-open short exact sequence `0 → j_!F|_U → F → i_*F|_Y → 0`
   - Hartshorne's Lemma 2.10: `H^i(X, i_*G) ≅ H^i(Y, G)` for closed inclusions
   - The identification of `Sheaf.H F n` with `Ext(ℤ[⊤], F, n)` (listed as a TODO in Mathlib's `SheafCohomology/Basic.lean`)

   The file includes detailed documentation of the proof strategy (induction on number of irreducible components) and the three specific missing pieces.

### Helper lemmas proved
- `subsingleton_of_isSheafFor_empty`: The sheaf condition for the empty presieve forces presheaf values to be subsingleton
- `addCommGrpCat_subsingleton_of_end_subsingleton`: If `End(G)` is subsingleton then `G` is trivial (since `id = 0`)
- `ext_subsingleton_of_isZero`: Ext from an `IsZero` object is subsingleton (via `HasProjectiveDimensionLT`)
- `sheaf_isZero_of_isEmpty`: Every sheaf on the empty space is a zero object
- `sheaf_H_subsingleton_of_isEmpty`: Sheaf cohomology vanishes on the empty space

### File structure
- `ClosedOpenDecomposition.lean`: Contains all the code, compiles successfully with one `sorry` in `sheaf_H_subsingleton_of_reducible`