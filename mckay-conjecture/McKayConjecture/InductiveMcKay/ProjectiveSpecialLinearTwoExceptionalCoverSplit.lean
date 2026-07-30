/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionUniversalityCriterion
import McKayConjecture.GroupTheory.UniversalCentralExtensionSourceEquiv
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoCardinality

/-!
# Exceptional and generic cover branches for PSL₂

The Schur-cover analysis for `PSL(2,q)` naturally separates the field
orders `q = 4` and `q = 9` from the generic branch.  This file records that
split without asserting either missing exceptional isomorphism.

It also packages the precise generic group-theoretic upgrade: if the
canonical special-linear cover is centrally closed, then its quotient map
is a universal central extension and the canonical comparison map from the
free-presentation cover is an isomorphism.

No centrally-closedness, exceptional isomorphism, or local
inductive-McKay datum is asserted here.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### Field order and the exhaustive parameter split -/

/-- The canonical finite field attached to a PSL₂ parameter. -/
abbrev projectiveSpecialLinearTwoField
    (a : ProjectiveSpecialLinearTwoSimpleParameter) : Type :=
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  GaloisField a.characteristic a.degree

/-- The order `q = r^n` of the canonical finite field. -/
def projectiveSpecialLinearTwoFieldOrder
    (a : ProjectiveSpecialLinearTwoSimpleParameter) : ℕ :=
  a.characteristic ^ a.degree

@[simp]
theorem natCard_projectiveSpecialLinearTwoField
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Nat.card (projectiveSpecialLinearTwoField a) =
      projectiveSpecialLinearTwoFieldOrder a :=
  natCard_galoisField_projectiveSpecialLinearTwoParameter a

/-- Every field order in the simple family is at least four. -/
theorem four_le_projectiveSpecialLinearTwoFieldOrder
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    4 ≤ projectiveSpecialLinearTwoFieldOrder a :=
  a.four_le_card

/-- The exceptional field-order-four branch. -/
def IsProjectiveSpecialLinearTwoOrderFourParameter
    (a : ProjectiveSpecialLinearTwoSimpleParameter) : Prop :=
  projectiveSpecialLinearTwoFieldOrder a = 4

/-- The exceptional field-order-nine branch. -/
def IsProjectiveSpecialLinearTwoOrderNineParameter
    (a : ProjectiveSpecialLinearTwoSimpleParameter) : Prop :=
  projectiveSpecialLinearTwoFieldOrder a = 9

/-- The generic branch, excluding exactly field orders four and nine. -/
def IsProjectiveSpecialLinearTwoGenericParameter
    (a : ProjectiveSpecialLinearTwoSimpleParameter) : Prop :=
  projectiveSpecialLinearTwoFieldOrder a ≠ 4 ∧
    projectiveSpecialLinearTwoFieldOrder a ≠ 9

/-- Parameters in the field-order-four exceptional branch. -/
abbrev ProjectiveSpecialLinearTwoOrderFourParameter :=
  {a : ProjectiveSpecialLinearTwoSimpleParameter //
    IsProjectiveSpecialLinearTwoOrderFourParameter a}

/-- Parameters in the field-order-nine exceptional branch. -/
abbrev ProjectiveSpecialLinearTwoOrderNineParameter :=
  {a : ProjectiveSpecialLinearTwoSimpleParameter //
    IsProjectiveSpecialLinearTwoOrderNineParameter a}

/-- Parameters in the generic field-order branch. -/
abbrev ProjectiveSpecialLinearTwoGenericParameter :=
  {a : ProjectiveSpecialLinearTwoSimpleParameter //
    IsProjectiveSpecialLinearTwoGenericParameter a}

/-- The three parameter branches are exhaustive. -/
theorem projectiveSpecialLinearTwoParameter_trichotomy
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    IsProjectiveSpecialLinearTwoOrderFourParameter a ∨
      IsProjectiveSpecialLinearTwoOrderNineParameter a ∨
        IsProjectiveSpecialLinearTwoGenericParameter a := by
  by_cases hFour :
      projectiveSpecialLinearTwoFieldOrder a = 4
  · exact Or.inl hFour
  by_cases hNine :
      projectiveSpecialLinearTwoFieldOrder a = 9
  · exact Or.inr (Or.inl hNine)
  exact Or.inr (Or.inr ⟨hFour, hNine⟩)

/-- The two exceptional branches are disjoint. -/
theorem projectiveSpecialLinearTwoOrderFour_not_orderNine
    {a : ProjectiveSpecialLinearTwoSimpleParameter}
    (hFour :
      IsProjectiveSpecialLinearTwoOrderFourParameter a) :
    ¬IsProjectiveSpecialLinearTwoOrderNineParameter a := by
  intro hNine
  unfold IsProjectiveSpecialLinearTwoOrderFourParameter at hFour
  unfold IsProjectiveSpecialLinearTwoOrderNineParameter at hNine
  omega

/-- The field-order-four and generic branches are disjoint. -/
theorem projectiveSpecialLinearTwoOrderFour_not_generic
    {a : ProjectiveSpecialLinearTwoSimpleParameter}
    (hFour :
      IsProjectiveSpecialLinearTwoOrderFourParameter a) :
    ¬IsProjectiveSpecialLinearTwoGenericParameter a :=
  fun hGeneric ↦ hGeneric.1 hFour

/-- The field-order-nine and generic branches are disjoint. -/
theorem projectiveSpecialLinearTwoOrderNine_not_generic
    {a : ProjectiveSpecialLinearTwoSimpleParameter}
    (hNine :
      IsProjectiveSpecialLinearTwoOrderNineParameter a) :
    ¬IsProjectiveSpecialLinearTwoGenericParameter a :=
  fun hGeneric ↦ hGeneric.2 hNine

/-- A field-order-four parameter is exactly characteristic two and degree
two. -/
theorem isProjectiveSpecialLinearTwoOrderFourParameter_iff
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    IsProjectiveSpecialLinearTwoOrderFourParameter a ↔
      a.characteristic = 2 ∧ a.degree = 2 := by
  constructor
  · intro hOrder
    have hpow :
        a.characteristic ^ a.degree = 2 ^ 2 := by
      simpa [IsProjectiveSpecialLinearTwoOrderFourParameter,
        projectiveSpecialLinearTwoFieldOrder] using hOrder
    have hdivPow :
        a.characteristic ∣ 2 ^ 2 := by
      rw [← hpow]
      exact
        dvd_pow_self
          a.characteristic a.degree_ne_zero
    have hdivTwo :
        a.characteristic ∣ 2 :=
      a.characteristic_prime.dvd_of_dvd_pow hdivPow
    have hcharacteristic :
        a.characteristic = 2 :=
      (Nat.prime_dvd_prime_iff_eq
        a.characteristic_prime Nat.prime_two).mp hdivTwo
    have hdegree :
        a.degree = 2 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      simpa [hcharacteristic] using hpow
    exact ⟨hcharacteristic, hdegree⟩
  · rintro ⟨hcharacteristic, hdegree⟩
    simp [IsProjectiveSpecialLinearTwoOrderFourParameter,
      projectiveSpecialLinearTwoFieldOrder,
      hcharacteristic, hdegree]

/-- A field-order-nine parameter is exactly characteristic three and degree
two. -/
theorem isProjectiveSpecialLinearTwoOrderNineParameter_iff
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    IsProjectiveSpecialLinearTwoOrderNineParameter a ↔
      a.characteristic = 3 ∧ a.degree = 2 := by
  constructor
  · intro hOrder
    have hpow :
        a.characteristic ^ a.degree = 3 ^ 2 := by
      simpa [IsProjectiveSpecialLinearTwoOrderNineParameter,
        projectiveSpecialLinearTwoFieldOrder] using hOrder
    have hdivPow :
        a.characteristic ∣ 3 ^ 2 := by
      rw [← hpow]
      exact
        dvd_pow_self
          a.characteristic a.degree_ne_zero
    have hdivThree :
        a.characteristic ∣ 3 :=
      a.characteristic_prime.dvd_of_dvd_pow hdivPow
    have hcharacteristic :
        a.characteristic = 3 :=
      (Nat.prime_dvd_prime_iff_eq
        a.characteristic_prime Nat.prime_three).mp hdivThree
    have hdegree :
        a.degree = 2 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      simpa [hcharacteristic] using hpow
    exact ⟨hcharacteristic, hdegree⟩
  · rintro ⟨hcharacteristic, hdegree⟩
    simp [IsProjectiveSpecialLinearTwoOrderNineParameter,
      projectiveSpecialLinearTwoFieldOrder,
      hcharacteristic, hdegree]

/-! ### Explicit exceptional and generic residual predicates -/

/-- The missing exceptional identification for the field-order-four branch.
This proposition is intentionally not asserted. -/
def ProjectiveSpecialLinearTwoOrderFourAlternatingFiveResidual : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoOrderFourParameter,
    Nonempty
      (projectiveSpecialLinearTwoRepresentative a.1 ≃*
        alternatingGroup (Fin 5))

/-- The missing exceptional identification for the field-order-nine branch.
This proposition is intentionally not asserted. -/
def ProjectiveSpecialLinearTwoOrderNineAlternatingSixResidual : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoOrderNineParameter,
    Nonempty
      (projectiveSpecialLinearTwoRepresentative a.1 ≃*
        alternatingGroup (Fin 6))

/-- The exact generic cover-theoretic residual: central closedness of the
canonical special-linear cover outside field orders four and nine. -/
def ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoGenericParameter,
    IsCentrallyClosed
      (projectiveSpecialLinearTwoSpecialLinearCover a.1)

/-! ### Conditional universality of the special-linear cover -/

/-- A centrally closed special-linear cover is a universal central
extension of its projective quotient. -/
def
    projectiveSpecialLinearTwoSpecialLinearUniversalCentralExtension_of_isCentrallyClosed
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (hclosed :
      IsCentrallyClosed
        (projectiveSpecialLinearTwoSpecialLinearCover a)) :
    UniversalCentralExtension
      (projectiveSpecialLinearTwoSpecialLinearCover a)
      (projectiveSpecialLinearTwoRepresentative a) :=
  universalCentralExtensionOfIsCentrallyClosed
    (projectiveSpecialLinearTwoSpecialLinearCentralExtension a)
    (projectiveSpecialLinearTwoSpecialLinearCover_isPerfect a)
    hclosed

/-- Under central closedness, uniqueness of universal central extensions
identifies the free-presentation cover with the special-linear cover. -/
def
    projectiveSpecialLinearTwoUniversalCoverEquivSpecialLinear_of_isCentrallyClosed
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (hclosed :
      IsCentrallyClosed
        (projectiveSpecialLinearTwoSpecialLinearCover a)) :
    projectiveSpecialLinearTwoUniversalCover a ≃*
      projectiveSpecialLinearTwoSpecialLinearCover a :=
  (projectiveSpecialLinearTwoUniversalCentralExtension a).sourceEquiv
    (projectiveSpecialLinearTwoSpecialLinearUniversalCentralExtension_of_isCentrallyClosed
      a hclosed)

/-- The equivalence above is exactly the canonical comparison map already
constructed from universality and perfectness. -/
@[simp]
theorem
    projectiveSpecialLinearTwoUniversalCoverEquivSpecialLinear_of_isCentrallyClosed_toMonoidHom
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (hclosed :
      IsCentrallyClosed
        (projectiveSpecialLinearTwoSpecialLinearCover a)) :
    (projectiveSpecialLinearTwoUniversalCoverEquivSpecialLinear_of_isCentrallyClosed
      a hclosed).toMonoidHom =
        (projectiveSpecialLinearTwoUniversalCoverToSpecialLinear
          a).projection :=
  rfl

/-- In particular, the canonical comparison map is bijective whenever the
special-linear cover is centrally closed. -/
theorem
    projectiveSpecialLinearTwoUniversalCoverToSpecialLinear_bijective_of_isCentrallyClosed
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (hclosed :
      IsCentrallyClosed
        (projectiveSpecialLinearTwoSpecialLinearCover a)) :
    Function.Bijective
      (projectiveSpecialLinearTwoUniversalCoverToSpecialLinear
        a).projection := by
  rw [←
    projectiveSpecialLinearTwoUniversalCoverEquivSpecialLinear_of_isCentrallyClosed_toMonoidHom
      a hclosed]
  exact
    (projectiveSpecialLinearTwoUniversalCoverEquivSpecialLinear_of_isCentrallyClosed
      a hclosed).bijective

/-- The source equivalence commutes with the two projections to
`PSL(2,q)`. -/
theorem
    projectiveSpecialLinearTwoUniversalCoverEquivSpecialLinear_of_isCentrallyClosed_commutes
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (hclosed :
      IsCentrallyClosed
        (projectiveSpecialLinearTwoSpecialLinearCover a)) :
    (projectiveSpecialLinearTwoSpecialLinearCentralExtension a).projection.comp
        (projectiveSpecialLinearTwoUniversalCoverEquivSpecialLinear_of_isCentrallyClosed
          a hclosed).toMonoidHom =
      (projectiveSpecialLinearTwoUniversalCentralExtension
        a).toCentralExtension.projection :=
  (projectiveSpecialLinearTwoUniversalCentralExtension
    a).sourceEquiv_commutes
      (projectiveSpecialLinearTwoSpecialLinearUniversalCentralExtension_of_isCentrallyClosed
        a hclosed)

namespace ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual

/-- The generic residual, once supplied, produces a concrete universal
special-linear cover for every generic parameter. -/
def universalCentralExtension
    (h : ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual)
    (a : ProjectiveSpecialLinearTwoGenericParameter) :
    UniversalCentralExtension
      (projectiveSpecialLinearTwoSpecialLinearCover a.1)
      (projectiveSpecialLinearTwoRepresentative a.1) :=
  projectiveSpecialLinearTwoSpecialLinearUniversalCentralExtension_of_isCentrallyClosed
    a.1 (h a)

/-- The generic residual likewise identifies the canonical
free-presentation and special-linear cover sources. -/
def universalCoverEquivSpecialLinear
    (h : ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual)
    (a : ProjectiveSpecialLinearTwoGenericParameter) :
    projectiveSpecialLinearTwoUniversalCover a.1 ≃*
      projectiveSpecialLinearTwoSpecialLinearCover a.1 :=
  projectiveSpecialLinearTwoUniversalCoverEquivSpecialLinear_of_isCentrallyClosed
    a.1 (h a)

end ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual

end InductiveMcKay
end McKayConjecture
