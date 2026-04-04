-- Harmonic `generalize_proofs` tactic
import Mathlib

/-!
# Presheaf-level filtered colimits of sheaves are sheaves on Noetherian spaces

On a Noetherian topological space X, the presheaf-level filtered colimit of a diagram
of sheaves is already a sheaf (no sheafification needed). This means `sheafToPresheaf`
creates filtered colimits on Noetherian spaces.

## Proof strategy

The sheaf condition asks: for every open cover {U_i} of U, the canonical map
F(U) → lim {F(U_i), F(U_i ∩ U_j)} is an isomorphism.

1. On a Noetherian space, every open cover has a finite subcover.
2. For a finite cover, the pairwise intersection diagram is finite.
3. Filtered colimits commute with finite limits (`colimitLimitIso`).
4. Each F_j in the diagram is a sheaf, so satisfies the limit condition.
5. Therefore the colimit presheaf satisfies the limit condition.

Alternative: use `IsSheafUniqueGluing` (concrete sheaf condition):
- Given compatible sections s_i ∈ (colim F_j)(U_i), they factor through some F_j
  (using finite cover + filtered colimit in AddCommGrpCat).
- Glue in F_j (which is a sheaf), then map to the colimit.
- Uniqueness by the same argument.

## Key Mathlib tools
- `TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections`
- `colimitLimitIso` / `filtered_colim_preservesFiniteLimits`
- `NoetherianSpace` → `isCompact_univ`, finite subcover
- `Concrete.isColimit_exists_rep` for elements of filtered colimits
- `IsFiltered.sup` for finding common upper bounds
-/

universe u

open CategoryTheory TopologicalSpace Limits Opposite TopCat

/-- On a Noetherian space, the presheaf-level filtered colimit of sheaves is a sheaf.
    This is because: Noetherian → every cover has finite subcover → sheaf condition is
    a finite limit → filtered colimits commute with finite limits → colimit is a sheaf. -/
theorem isSheaf_presheaf_filtered_colimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c : Cocone (Y' ⋙ sheafToPresheaf _ _)) (hc : IsColimit c) :
    TopCat.Presheaf.IsSheaf c.pt := by
  sorry
