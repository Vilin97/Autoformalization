/-
  ClosedOpenDecomposition.lean — Reduction from general to irreducible spaces

  All cases proved (sorry-free):
  - Empty X: all sheaves are zero → Ext vanishes
  - Irreducible X: apply ih_irred directly
  - Reducible X: delegates to ReducibleVanishing' (Finset.induction on components)
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.TopologicalKrullDim

universe u

open CategoryTheory TopologicalSpace Limits

/-! ## Empty space vanishing -/

private theorem sheaf_H_subsingleton_of_isEmpty'
    (X : TopCat.{u}) [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) : Subsingleton (Sheaf.H F n) :=
  sheafH_subsingleton_of_isEmpty F n

/-! ## Main theorem -/

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
    · exact ReducibleVanishing' X n hn F hIrred
        (fun Y [_] [_] G hle hY => ih_irred Y n G hle hY)
