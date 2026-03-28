import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits

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

set_option synthInstance.maxHeartbeats 80000

/-- For a Noetherian space X that is NOT irreducible and is nonempty,
    sheaf cohomology vanishes in degrees > dim X, assuming vanishing
    holds for all irreducible spaces of dimension ≤ dim X.

    Proof strategy (Hartshorne III.2.7 Step 1, reducible case):
    X has ≥ 2 irreducible components Y₁, ..., Yₖ (k ≥ 2).
    Pick Y₁. Let Z = closure(X \ Y₁).

    Need: H^n(X, F) is subsingleton.

    Key idea: Use the Mayer-Vietoris sequence for the open cover
    U₁ = X \ Z and U₂ = X \ Y₁, where U₁ ∪ U₂ = X \ (Y₁ ∩ Z).

    Alternative: use that on a Noetherian space, the sheaf category
    decomposes by support. If F is supported on Y₁, vanishing follows
    from ih_irred. If F is supported on Z, vanishing follows by
    induction on the number of components.

    The cleanest approach uses the Mayer-Vietoris long exact sequence
    (Opens.mayerVietorisSquare, available in Mathlib) when the open
    cover happens to cover X. On a Noetherian space with k ≥ 2
    components, we can always find opens that cover X.

    Actually, the standard approach needs extension by zero (j_!)
    which is NOT in Mathlib. So this sorry may need to remain. -/
theorem sheaf_H_subsingleton_of_reducible
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
