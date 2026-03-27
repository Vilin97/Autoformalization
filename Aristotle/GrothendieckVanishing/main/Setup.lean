/-
  Setup.lean — Category instances and FlasqueVanishing axiom

  Provides the categorical infrastructure needed for sheaf cohomology
  on topological spaces with values in AddCommGrpCat.
-/
import Mathlib

universe u

open CategoryTheory

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h; simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x; specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1; aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

/-- Flasque sheaves have vanishing higher cohomology.
A sheaf is flasque if all restriction maps are epi.
DO NOT PROVE — use as axiom. -/
theorem FlasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (h : ∀ {U V : TopologicalSpace.Opens X} (i : U ⟶ V),
      CategoryTheory.Epi (F.val.map i.op))
    (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  admit
