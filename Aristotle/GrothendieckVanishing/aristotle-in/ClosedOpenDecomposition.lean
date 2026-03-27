import Mathlib

universe u

open CategoryTheory TopologicalSpace

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

/-- Reduction from general Noetherian spaces to irreducible ones.

    If vanishing holds for all irreducible Noetherian spaces Y with
    dim Y ≤ dim X and n > dim Y, then it holds for X.

    Hartshorne Step 1: decompose X by irreducible components, use the closed/open
    exact sequence and Lemma 2.10 to reduce to each component.
    The irreducible spaces Y that appear all have dim Y ≤ dim X.

    Key ingredients needed:
    - Extension by zero: for Y ⊆ X closed and U = X \ Y open,
      there is a short exact sequence 0 → F̄_U → F → F̄_Y → 0
    - Lemma 2.10 (Hartshorne): H^i(X, j_*F) = H^i(Y, F) for j : Y → X closed inclusion
    - Induction on the number of irreducible components of X
    - For each component Y_i of X: dim Y_i ≤ dim X (since Y_i is a closed subset)
    - The closure of X \ Y_i has fewer irreducible components than X -/
theorem grothendieck_vanishing_of_irreducible
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih_irred : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      [IrreducibleSpace Y] (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y → Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  sorry
