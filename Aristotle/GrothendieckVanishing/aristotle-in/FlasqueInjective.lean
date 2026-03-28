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

set_option maxHeartbeats 800000

/-- A flasque sheaf of abelian groups on a topological space is injective
    in the sheaf category (Bredon's theorem).

    A sheaf F is flasque if all restriction maps F(V) → F(U) are epi (surjective).
    The proof uses Zorn's lemma on partial extensions:

    Given a mono f : G ↪ H and a morphism g : G → F, we need to find h : H → F
    with f ≫ h = g.

    Consider the poset of subsheaves G' with G ⊆ G' ⊆ H and extensions g' : G' → F.
    By Zorn: every chain has an upper bound (union of subsheaves), so there exists
    a maximal element (G_max, g_max).

    Claim: G_max = H. Otherwise, there exists an open U and a section s ∈ H(U) \ G_max(U).
    We can extend g_max to include s using flasqueness of F:
    - s restricts to some element in G_max on some open V ⊂ U
    - The extension from V to U exists because F is flasque
    - This contradicts maximality of G_max.

    Key tools:
    - Injective.mk: prove injectivity by the extension property
    - Zorn's lemma (in Lean: `zorn_le` or `zorn_nonempty_partialOrder`)
    - Sheaf morphisms are determined by their values on sections
    - Mono in sheaf category ↔ injective on stalks ↔ injective on sections

    Alternative approach: use injective_iff_subsingleton_ext_one and show
    every extension of F splits. An extension 0 → F → E → Y → 0 splits iff
    the identity on F lifts to a map E → F. For flasque F, construct this
    section-by-section using flasqueness.
-/
theorem flasque_injective (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (h : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)) :
    Injective F := by
  sorry
