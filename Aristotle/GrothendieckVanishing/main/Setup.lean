/-
  Setup.lean — Category instances and sorry'd lemmas for Grothendieck vanishing

  Provides:
  1. Categorical infrastructure for sheaf cohomology on AddCommGrpCat
  2. flasque_injective (sorry — Bredon's theorem, needs Zorn's lemma argument)
  3. FlasqueVanishing (proved from flasque_injective)
  4. ReducibleVanishing (sorry — needs j_! extension by zero, not in Mathlib v4.28)
  5. IrreduciblePosVanishing (sorry — needs j_! or Prop 2.9)
-/
import Mathlib

universe u

open CategoryTheory TopologicalSpace

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h
    simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x
    specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1
    aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

set_option synthInstance.maxHeartbeats 80000 in
/-- A flasque sheaf is injective in the sheaf category (Bredon's theorem).
    Proof requires Zorn's lemma on partial extensions of sheaf morphisms. -/
theorem flasque_injective (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (h : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)) :
    Injective F := by
  sorry

set_option synthInstance.maxHeartbeats 80000 in
/-- Flasque sheaves have vanishing higher cohomology.
    Follows from flasque → injective + HasInjectiveDimensionLT. -/
theorem FlasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (h : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op))
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  haveI := flasque_injective X F h
  unfold Sheaf.H
  exact HasInjectiveDimensionLT.subsingleton F 1 (n + 1) (by omega) _

set_option synthInstance.maxHeartbeats 80000 in
/-- Reducible case: cohomology vanishing for non-irreducible Noetherian X.
    Proof requires j_! (extension by zero, NOT in Mathlib v4.28). -/
theorem ReducibleVanishing
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hNotIrred : ¬ IrreducibleSpace X) [Nonempty X]
    (ih_irred : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      [IrreducibleSpace Y] (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y → Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  sorry

set_option synthInstance.maxHeartbeats 80000 in
/-- Irreducible positive-dim case: cohomology vanishing for irreducible X of dim ≥ 1.
    Proof requires j_! or Prop 2.9 (cohomology commutes with direct limits). -/
theorem IrreduciblePosVanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  sorry
