import Mathlib

-- Harmonic `generalize_proofs` tactic

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

set_option synthInstance.maxHeartbeats 80000 in
/-- Flasque sheaves have vanishing higher cohomology.
    A sheaf F is "flasque" if all restriction maps F(V) → F(U) are surjective (epi).

    Proof strategy:
    1. H^n(X, F) = Ext(constantSheaf(Z), F, n) by definition (Sheaf.H)
    2. For flasque F: show Ext(A, F, n) = 0 for all A and n ≥ 1
    3. This follows from F being Ext-acyclic, which follows from:
       - Take 0 → F → I → Q → 0 with I injective
       - F flasque → Γ exact on F → the sequence 0 → Γ(F) → Γ(I) → Γ(Q) → 0 is exact
       - By dimension shifting: H^n(X, F) ≅ H^{n-1}(X, Q) for n ≥ 2
       - And H^1(X, F) = 0 directly from Γ-exactness

    Alternative: show flasque sheaves are injective objects in the sheaf category.
    This is TRUE for sheaves on topological spaces: flasque ↔ injective in Sh(X, Ab)
    (Bredon's theorem). Injective objects have Ext^n = 0 for n ≥ 1.

    Key Mathlib tools:
    - Ext.subsingleton_of_projective / Ext.subsingleton_of_injective
    - Sheaf.H is defined as Ext(constantSheaf(Z), F, n)
    - Injective.subsingleton_ext: Ext(A, I, n) = 0 for injective I and n ≥ 1

    If you can show that F with all restriction maps epi is injective in the sheaf
    category, then Ext vanishing follows immediately from existing Mathlib API.
-/
theorem FlasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (h : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op))
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  sorry
