-- Harmonic `generalize_proofs` tactic
import Mathlib
import Aristotle.GrothendieckVanishing.main.Auxiliary

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

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
  inferInstanceAs (Abelian (Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (Sheaf _ _))

def IsFlasqueSheaf {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)

-- ADMITTED HELPER: evaluated exactness of a SES of sheaves
-- If g_V(x) = 0 then x is in the image of f_V.
set_option maxHeartbeats 1600000 in
private lemma sections_exact_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (V : Opens X)
    (x : S.X₂.val.obj (op V))
    (hx : ConcreteCategory.hom (S.g.val.app (op V)) x = 0) :
    ∃ a : S.X₁.val.obj (op V),
      ConcreteCategory.hom (S.f.val.app (op V)) a = x := by
  admit

-- ADMITTED HELPER: f ≫ g = 0 at sections level
private lemma eval_comp_zero {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (V : Opens X) :
    S.f.val.app (op V) ≫ S.g.val.app (op V) = 0 := by
  admit

-- KEY THEOREM: Zorn argument for surjectivity.
-- In a SES 0 → X₁ → X₂ → X₃ → 0 with X₁ flasque, g(U): X₂(U) → X₃(U) is epi.
--
-- Proof strategy:
-- 1. Reduce to surjectivity via AddCommGrpCat.epi_iff_surjective
-- 2. Get IsLocallySurjective from epi (Sheaf.isLocallySurjective_iff_epi')
-- 3. Define Zorn set P = {(V,t) | V ≤ U, g(t) = s|_V}
-- 4. Define preorder: (V₁,t₁) ≤ (V₂,t₂) iff V₁ ≤ V₂ and t₂|_{V₁} = t₁
-- 5. Bottom: (⊥, 0) ∈ P via isTerminal_sheaf_bot
-- 6. Chain bound: TopCat.Sheaf.existsUnique_gluing' for compatible chain sections
-- 7. Maximality: if V₀ < U, pick x ∈ U\V₀, use imageSieve for local lift at x,
--    exactness for kernel element, flasqueness to extend, patch and glue,
--    contradicting maximality.
--
-- Key API:
-- - zorn_le₀ for Zorn's lemma
-- - Sheaf.IsLocallySurjective.imageSieve_mem for local lifts
-- - TopCat.Sheaf.existsUnique_gluing' for gluing compatible sections
-- - TopCat.Sheaf.eq_of_locally_eq' for sheaf separation
-- - NatTrans.naturality_apply for pointwise naturality
-- - CategoryTheory.comp_apply for composition of morphisms applied to elements
set_option maxHeartbeats 25600000 in
theorem epi_app_of_shortExact_flasque {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hFlasque₁ : IsFlasqueSheaf S.X₁) (U : Opens X) :
    Epi (S.g.val.app (op U)) := by
  sorry
