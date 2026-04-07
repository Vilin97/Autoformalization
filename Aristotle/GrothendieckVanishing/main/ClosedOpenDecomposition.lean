/-
  ClosedOpenDecomposition.lean — Reduction from general to irreducible spaces

  All cases proved (sorry-free):
  - Empty X: all sheaves are zero → Ext vanishes
  - Irreducible X: apply ih_irred directly
  - Reducible X: delegates to reducibleVanishing' (Finset.induction on components)
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.Auxiliary
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

universe u

open CategoryTheory TopologicalSpace Limits

/-! ## Empty space vanishing -/

/-- On an empty space, all sheaf cohomology vanishes. -/
theorem sheaf_H_subsingleton_of_isEmpty'
    (X : TopCat.{u}) [hE : IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) : Subsingleton (Sheaf.H F n) := by
  unfold Sheaf.H
  have := (sheaf_isZero_of_zero_stalks X ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)))
    (fun x _ => (hE.false x).elim)).hasProjectiveDimensionLT_zero
  exact HasProjectiveDimensionLT.subsingleton _ 0 n (Nat.zero_le n) F

/-! ## Main theorem -/

/-- Reduction from general Noetherian spaces to irreducible ones: handles empty, irreducible,
and reducible cases separately. -/
theorem grothendieck_vanishing_of_irreducible
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih_irred : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      [IrreducibleSpace Y] (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      m > topologicalKrullDim Y → Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H F n) := by
  by_cases hEmpty : IsEmpty X
  · exact sheaf_H_subsingleton_of_isEmpty' X F n
  · rw [not_isEmpty_iff] at hEmpty
    by_cases hIrred : IrreducibleSpace X
    · exact @ih_irred X _ hIrred n F le_rfl hn
    · exact reducibleVanishing' X n hn F hIrred
        (fun Y [_] [_] G hle hY => ih_irred Y n G hle hY)
