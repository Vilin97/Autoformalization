/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherGoodClassCount
import McKayConjecture.GroupTheory.ConjugationInvariant

/-!
# Transport of good quotient conjugacy classes

The ordinary Gallagher theorem counts conjugacy classes in a quotient that
satisfy the extension-semantic good-element predicate.  In applications such
as the Okuyama--Wajima comparison, the two quotient groups are related by a
multiplicative equivalence.

This file isolates the set-theoretic transport step: if a multiplicative
equivalence preserves goodness pointwise, it induces an equivalence between
the corresponding subtypes of good quotient conjugacy classes.  No character
invariance or finiteness hypothesis is needed because goodness of a class is
defined by existence of a good representative.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace IrreducibleCharacter

variable {A : Type u} {B : Type v} [Group A] [Group B]
variable (N : Subgroup A) [N.Normal]
variable (M : Subgroup B) [M.Normal]

/-- A quotient equivalence that preserves good elements also preserves the
existential good-conjugacy-class predicate. -/
theorem isGoodQuotientConjugacyClass_iff_of_mulEquiv
    (θ : IrreducibleCharacter N)
    (φ : IrreducibleCharacter M)
    (e : A ⧸ N ≃* B ⧸ M)
    (hgood :
      ∀ q : A ⧸ N,
        IsGoodQuotientElement N θ q ↔
          IsGoodQuotientElement M φ (e q))
    (c : ConjClasses (A ⧸ N)) :
    IsGoodQuotientConjugacyClass N θ c ↔
      IsGoodQuotientConjugacyClass M φ
        (GroupTheory.conjugacyClassesEquivOfMulEquiv e c) := by
  constructor
  · rintro ⟨q, hq, hqgood⟩
    refine ⟨e q, ?_, (hgood q).mp hqgood⟩
    rw [← hq]
    rfl
  · rintro ⟨r, hr, hrgood⟩
    refine ⟨e.symm r, ?_, ?_⟩
    · apply
        (GroupTheory.conjugacyClassesEquivOfMulEquiv e).injective
      change
        ConjClasses.mk (e (e.symm r)) =
          GroupTheory.conjugacyClassesEquivOfMulEquiv e c
      simpa only [e.apply_symm_apply] using hr
    · exact
        (hgood (e.symm r)).mpr
          (by simpa only [e.apply_symm_apply] using hrgood)

/-- Pointwise transport of good quotient elements along a multiplicative
equivalence induces an equivalence of good quotient conjugacy classes. -/
def goodQuotientConjugacyClassesEquivOfMulEquiv
    (θ : IrreducibleCharacter N)
    (φ : IrreducibleCharacter M)
    (e : A ⧸ N ≃* B ⧸ M)
    (hgood :
      ∀ q : A ⧸ N,
        IsGoodQuotientElement N θ q ↔
          IsGoodQuotientElement M φ (e q)) :
    GoodQuotientConjugacyClasses N θ ≃
      GoodQuotientConjugacyClasses M φ :=
  (GroupTheory.conjugacyClassesEquivOfMulEquiv e).subtypeEquiv
    (isGoodQuotientConjugacyClass_iff_of_mulEquiv
      N M θ φ e hgood)

@[simp]
theorem goodQuotientConjugacyClassesEquivOfMulEquiv_apply_coe
    (θ : IrreducibleCharacter N)
    (φ : IrreducibleCharacter M)
    (e : A ⧸ N ≃* B ⧸ M)
    (hgood :
      ∀ q : A ⧸ N,
        IsGoodQuotientElement N θ q ↔
          IsGoodQuotientElement M φ (e q))
    (c : GoodQuotientConjugacyClasses N θ) :
    (goodQuotientConjugacyClassesEquivOfMulEquiv
        N M θ φ e hgood c).1 =
      GroupTheory.conjugacyClassesEquivOfMulEquiv e c.1 :=
  rfl

end IrreducibleCharacter

namespace CliffordCorrespondence

-- The current Gallagher count is universe zero, so this downstream
-- cardinality adapter has the same limitation.  The class transport above
-- remains universe polymorphic.
variable {A B : Type} [Group A] [Group B]

/-- An equivalence of good quotient conjugacy classes converts the two
ordinary Gallagher counts into an equality of lying-over cardinalities. -/
theorem
    natCard_irreducibleCharactersOverAlong_eq_of_goodQuotientConjugacyClassesEquiv
    [Finite A] [Finite B]
    (N : Subgroup A) [N.Normal]
    (M : Subgroup B) [M.Normal]
    (θ : IrreducibleCharacter N)
    (φ : IrreducibleCharacter M)
    (hθ : ∀ a : A, a • θ = θ)
    (hφ : ∀ b : B, b • φ = φ)
    (e :
      IrreducibleCharacter.GoodQuotientConjugacyClasses N θ ≃
        IrreducibleCharacter.GoodQuotientConjugacyClasses M φ) :
    Nat.card (IrreducibleCharactersOverAlong N.subtype θ) =
      Nat.card (IrreducibleCharactersOverAlong M.subtype φ) := by
  calc
    Nat.card (IrreducibleCharactersOverAlong N.subtype θ) =
        Nat.card
          (IrreducibleCharacter.GoodQuotientConjugacyClasses N θ) :=
      natCard_irreducibleCharactersOverAlong_eq_goodQuotientConjugacyClasses
        N θ hθ
    _ =
        Nat.card
          (IrreducibleCharacter.GoodQuotientConjugacyClasses M φ) :=
      Nat.card_congr e
    _ =
        Nat.card (IrreducibleCharactersOverAlong M.subtype φ) :=
      (natCard_irreducibleCharactersOverAlong_eq_goodQuotientConjugacyClasses
        M φ hφ).symm

end CliffordCorrespondence
end McKayConjecture
