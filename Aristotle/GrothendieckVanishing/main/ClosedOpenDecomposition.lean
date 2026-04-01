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

/-! ## Helper lemmas -/

private lemma subsingleton_of_isSheafFor_empty
    {C : Type*} [Category C] {U : C} {P : Cᵒᵖ ⥤ Type*}
    (h : Presieve.IsSheafFor P (⊥ : Presieve U)) :
    Subsingleton (P.obj (Opposite.op U)) := by
  constructor; intro a b
  have hemp : Presieve.FamilyOfElements P (⊥ : Presieve U) := fun _ _ hf => absurd hf id
  obtain ⟨t, _, huniq⟩ := h hemp (fun _ _ _ _ _ _ _ hf => absurd hf id)
  exact (huniq a (fun _ _ hf => absurd hf id)).trans
    (huniq b (fun _ _ hf => absurd hf id)).symm

private lemma addCommGrpCat_subsingleton_of_end_subsingleton
    (G : AddCommGrpCat.{u}) (h : Subsingleton (G ⟶ G)) :
    Subsingleton G := by
  have : ∀ (g : G), g = 0 := by
    intro g
    have := AddCommGrpCat.ext_iff.mp (Subsingleton.elim (𝟙 G : G ⟶ G) 0) g
    simp at this; exact this
  exact ⟨fun a b => (this a).trans (this b).symm⟩

/-! ## Empty space vanishing -/

theorem sheaf_isZero_of_isEmpty (X : TopCat.{u}) [hE : IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    IsZero F := by
  have hom_sub : ∀ (E : AddCommGrpCat.{u}) (U : Opens X),
      Subsingleton (E ⟶ F.val.obj (Opposite.op U)) := by
    intro E U
    have hmem : (⊥ : Sieve U) ∈ Opens.grothendieckTopology X U := by
      rw [Opens.grothendieckTopology]; intro x; exact IsEmpty.elim hE x
    have hsf := (F.cond E) (⊥ : Sieve U) hmem
    rw [show (⊥ : Sieve U).arrows = ⊥ from rfl] at hsf
    exact subsingleton_of_isSheafFor_empty hsf
  have val_sub : ∀ (U : Opens X), Subsingleton (F.val.obj (Opposite.op U)) :=
    fun U => addCommGrpCat_subsingleton_of_end_subsingleton _ (hom_sub _ U)
  have val_isZero : ∀ (U : (Opens X)ᵒᵖ), IsZero (F.val.obj U) := by
    intro ⟨U⟩; exact @AddCommGrpCat.isZero_of_subsingleton _ (val_sub U)
  apply IsZero.mk
  · intro G; exact ⟨{
      default := 0
      uniq := fun f => by
        apply Sheaf.Hom.ext; apply NatTrans.ext; funext U
        exact (val_isZero U).eq_zero_of_src (f.val.app U) }⟩
  · intro G; exact ⟨{
      default := 0
      uniq := fun f => by
        apply Sheaf.Hom.ext; apply NatTrans.ext; funext U
        exact (val_isZero U).eq_zero_of_tgt (f.val.app U) }⟩

theorem sheaf_H_subsingleton_of_isEmpty'
    (X : TopCat.{u}) [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) : Subsingleton (Sheaf.H F n) := by
  unfold Sheaf.H
  have hZ := sheaf_isZero_of_isEmpty X
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ)))
  have := hZ.hasProjectiveDimensionLT_zero
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
