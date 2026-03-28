/-
  Setup.lean — Category instances and sorry'd lemmas for Grothendieck vanishing

  Provides:
  1. Categorical infrastructure for sheaf cohomology on AddCommGrpCat
  2. FlasqueVanishing (sorry — flasque sheaves have vanishing higher cohomology)
  3. ReducibleVanishing (sorry — needs j_! extension by zero)
  4. IrreduciblePosVanishing (sorry — needs j_! or Prop 2.9)
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
/-- Flasque sheaves have vanishing higher cohomology.
    A sheaf is flasque if all restriction maps are epi.

    The proof (Brian Nugent, Mathlib PR #35790) uses dimension shifting:
    embed F ↪ I (injective), form cokernel Q = I/F. The key Zorn argument
    shows Γ(I) → Γ(Q) is surjective when F is flasque, giving H¹(F) = 0.
    Then Q is also flasque, and H^{n+1}(F) ≅ H^n(Q) = 0 by induction. -/
theorem FlasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (h : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op))
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  sorry

set_option synthInstance.maxHeartbeats 80000 in
/-- Reducible case: for a non-irreducible Noetherian space X, cohomology vanishing
    follows from vanishing on all irreducible spaces of dim ≤ dim X.

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
/-- Irreducible positive-dim case: for an irreducible Noetherian space X of dim ≥ 1,
    cohomology vanishing follows from vanishing on all lower-dim spaces.

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
