/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.IntegralDomain
import McKayConjecture.Character.GoodElementExtensionRatio

/-!
# Summing the good-element extension ratio

The extension ratio attached to a chosen cyclic-over-`N` extension is a
linear character of the good-element centralizer.  After coercing complex
units to complex numbers, the standard finite-group character sum is the
centralizer order when the ratio is trivial and zero otherwise.  The
triviality criterion from `GoodElementExtensionRatio` identifies the first
case exactly with Gallagher goodness of the quotient element.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

noncomputable local instance goodElementRatioSumFintype
    (G : Type*) [Finite G] : Fintype G :=
  Fintype.ofFinite G

local instance goodElementRatioSumDecidableProp
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {A : Type u} [Group A]
variable (N : Subgroup A) [N.Normal]

/-- The extension ratio, coerced from complex units to complex numbers. -/
def goodElementExtensionRatioComplex
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q) :
    goodElementCentralizer N q →* ℂ :=
  (Units.coeHom ℂ).comp
    (goodElementExtensionRatio N θ hinvariant q η)

@[simp]
theorem goodElementExtensionRatioComplex_apply
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q)
    (d : goodElementCentralizer N q) :
    goodElementExtensionRatioComplex
        N θ hinvariant q η d =
      (goodElementExtensionRatio
        N θ hinvariant q η d : ℂ) :=
  rfl

/-- Coercing the unit-valued extension ratio to `ℂ` is trivial exactly
when the original unit-valued homomorphism is trivial. -/
theorem goodElementExtensionRatioComplex_eq_one_iff
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q) :
    goodElementExtensionRatioComplex
        N θ hinvariant q η = 1 ↔
      goodElementExtensionRatio
        N θ hinvariant q η = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro d
    apply Units.coeHom_injective
    have hd := DFunLike.congr_fun h d
    simpa only [goodElementExtensionRatioComplex_apply,
      MonoidHom.one_apply, Units.coeHom_apply,
      Units.val_one] using hd
  · intro h
    apply MonoidHom.ext
    intro d
    have hd := DFunLike.congr_fun h d
    simpa only [goodElementExtensionRatioComplex_apply,
      MonoidHom.one_apply, Units.coeHom_apply,
      Units.val_one] using
        congrArg (Units.coeHom ℂ) hd

/-- The sum of the scalar extension ratio over the good-element centralizer
is its order when `q` is good and is zero otherwise. -/
theorem sum_goodElementExtensionRatio
    [Finite A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ b : A, b • θ = θ)
    (q : A ⧸ N)
    (η : CyclicOverExtensions N θ q) :
    (∑ d : goodElementCentralizer N q,
      (goodElementExtensionRatio
        N θ hinvariant q η d : ℂ)) =
      if IsGoodQuotientElement N θ q then
        (Nat.card (goodElementCentralizer N q) : ℂ)
      else 0 := by
  let ratioComplex :=
    goodElementExtensionRatioComplex
      N θ hinvariant q η
  have hsum :
      (∑ d : goodElementCentralizer N q,
        ratioComplex d) =
        if ratioComplex = 1 then
          (Fintype.card
            (goodElementCentralizer N q) : ℂ)
        else 0 := by
    simpa only [Nat.cast_ite, Nat.cast_zero] using
      (sum_hom_units ratioComplex)
  have htrivial :
      ratioComplex = 1 ↔
        IsGoodQuotientElement N θ q :=
    (goodElementExtensionRatioComplex_eq_one_iff
      N θ hinvariant q η).trans
      (goodElementExtensionRatio_eq_one_iff_isGood
        N θ hinvariant q η)
  simp only [ratioComplex,
    goodElementExtensionRatioComplex_apply] at hsum
  rw [htrivial] at hsum
  simpa only [Nat.card_eq_fintype_card] using hsum

end IrreducibleCharacter
end McKayConjecture
