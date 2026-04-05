/-
  ClosedOpenDecomposition.lean — Reduction from general to irreducible spaces

  All cases proved (sorry-free):
  - Empty X: all sheaves are zero → Ext vanishes
  - Irreducible X: apply ih_irred directly
  - Reducible X: delegates to ReducibleVanishing' (Finset.induction on components)
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.Auxiliary

universe u

open CategoryTheory TopologicalSpace Limits

/-! ## Empty space vanishing -/

theorem sheaf_isZero_of_isEmpty (X : TopCat.{u}) [hE : IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    IsZero F :=
  sheaf_isZero_of_zero_stalks X F (fun x _ => (hE.false x).elim)

theorem sheaf_H_subsingleton_of_isEmpty'
    (X : TopCat.{u}) [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) : Subsingleton (Sheaf.H F n) := by
  unfold Sheaf.H
  have := (sheaf_isZero_of_isEmpty X ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)))).hasProjectiveDimensionLT_zero
  exact HasProjectiveDimensionLT.subsingleton _ 0 n (Nat.zero_le n) F

/-! ## Reducible case (proved via ReducibleVanishing') -/

private theorem sheaf_H_subsingleton_of_reducible
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hNotIrred : ¬ IrreducibleSpace X) [Nonempty X]
    (ih_irred : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      [IrreducibleSpace Y] (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      m > topologicalKrullDim Y → Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H F n) :=
  ReducibleVanishing' X n hn F hNotIrred
    (fun (Y : TopCat.{u}) [_inst1 : NoetherianSpace Y] [_inst2 : IrreducibleSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y) hle hY => ih_irred Y n G hle hY)

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
    · exact sheaf_H_subsingleton_of_reducible X n hn F hIrred ih_irred
