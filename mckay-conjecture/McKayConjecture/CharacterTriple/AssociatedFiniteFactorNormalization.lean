/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.OrderOfElement
import McKayConjecture.CharacterTriple.AssociatedRescale
import McKayConjecture.CharacterTriple.FiniteFactorNormalization

/-!
# Finite-factor normalization preserving association

Pointwise determinant normalization of a projective representation need not
preserve its exact restriction to the normal subgroup of a character triple.
Instead, this file rescales by a cochain on the quotient.  On every nonidentity
quotient coset, the cochain makes the determinant of one chosen representative
equal to one; on the identity coset it is exactly one, so association is
preserved.

If `n` is the representation dimension and `m` is the order of the normal
subgroup, every determinant of the resulting lift is an `m`th root of unity.
Taking determinants in the projective multiplication law then shows that the
factor set takes values in the `(n * m)`th roots of unity.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type u} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- The exponent controlling the finite factor set while preserving the
associated normal-subgroup restriction. -/
def associatedFactorExponent (T : CharacterTriple A) (V : Type)
    [AddCommGroup V] [Module ℂ V] : ℕ :=
  Module.finrank ℂ V * Nat.card T.normalSubgroup

theorem associatedFactorExponent_pos :
    0 < associatedFactorExponent T V :=
  Nat.mul_pos ProjectiveRepresentation.finrank_pos Nat.card_pos

instance associatedFactorExponent_neZero :
    NeZero (associatedFactorExponent T V) :=
  ⟨associatedFactorExponent_pos.ne'⟩

/-- A selected representative of a quotient coset, used only to choose its
determinant correction. -/
def determinantCosetRepresentative
    (q : A ⧸ T.normalSubgroup) : A :=
  Classical.choose
    (QuotientGroup.mk'_surjective T.normalSubgroup q)

@[simp]
theorem mk_determinantCosetRepresentative
    (q : A ⧸ T.normalSubgroup) :
    QuotientGroup.mk' T.normalSubgroup
        (determinantCosetRepresentative q) = q :=
  Classical.choose_spec
    (QuotientGroup.mk'_surjective T.normalSubgroup q)

/-- A determinant correction on the quotient.  It is deliberately set to
one on the identity coset, rather than applying an arbitrary root selector
there, so its pullback is trivial on the normal subgroup. -/
def determinantQuotientRescaling
    (_R : AssociatedProjectiveRepresentation T V P)
    (q : A ⧸ T.normalSubgroup) : ℂˣ := by
  classical
  exact
    if q = 1 then 1
    else
      unitNthRoot
        (LinearEquiv.det
          (P.operator (determinantCosetRepresentative q)))⁻¹
        (Module.finrank ℂ V)
        ProjectiveRepresentation.finrank_pos

@[simp]
theorem determinantQuotientRescaling_one
    (R : AssociatedProjectiveRepresentation T V P) :
    R.determinantQuotientRescaling 1 = 1 := by
  simp [determinantQuotientRescaling]

theorem determinantQuotientRescaling_pow
    (R : AssociatedProjectiveRepresentation T V P)
    (q : A ⧸ T.normalSubgroup) (hq : q ≠ 1) :
    R.determinantQuotientRescaling q ^ Module.finrank ℂ V =
      (LinearEquiv.det
        (P.operator (determinantCosetRepresentative q)))⁻¹ := by
  simp [determinantQuotientRescaling, hq]

/-- The projective representation obtained by the quotient-coset-constant
determinant correction. -/
def associatedFiniteFactorProjective
    (R : AssociatedProjectiveRepresentation T V P) :
    ProjectiveRepresentation ℂ A V :=
  P.rescale
    (quotientScalar R.determinantQuotientRescaling)

/-- The determinant correction preserves association, including the exact
normal-subgroup restriction. -/
def associatedFiniteFactorAssociated
    (R : AssociatedProjectiveRepresentation T V P) :
    AssociatedProjectiveRepresentation T V
      R.associatedFiniteFactorProjective :=
  R.rescaleByQuotientScalar
    R.determinantQuotientRescaling
    R.determinantQuotientRescaling_one

theorem associatedFiniteFactorProjective_isNormalized
    (R : AssociatedProjectiveRepresentation T V P) :
    R.associatedFiniteFactorProjective.IsNormalized :=
  R.associatedFiniteFactorAssociated.isNormalized

/-- Determinants of operators in the honest normal-subgroup restriction have
order dividing the cardinality of that subgroup. -/
theorem restriction_det_pow_card
    (R : AssociatedProjectiveRepresentation T V P)
    (x : T.normalSubgroup) :
    LinearEquiv.det (R.restriction x) ^
        Nat.card T.normalSubgroup = 1 := by
  let d : T.normalSubgroup →* ℂˣ :=
    (LinearEquiv.det :
      (V ≃ₗ[ℂ] V) →* ℂˣ).comp R.restriction
  change d x ^ Nat.card T.normalSubgroup = 1
  rw [← map_pow, pow_card_eq_one', map_one]

/-- The chosen operator on every nonidentity quotient representative has
determinant one after the quotient rescaling. -/
theorem associatedFiniteFactorProjective_representative_det
    (R : AssociatedProjectiveRepresentation T V P)
    (q : A ⧸ T.normalSubgroup) (hq : q ≠ 1) :
    LinearEquiv.det
      (R.associatedFiniteFactorProjective.operator
        (determinantCosetRepresentative q)) = 1 := by
  rw [associatedFiniteFactorProjective,
    ProjectiveRepresentation.rescale_operator,
    (LinearEquiv.det :
      (V ≃ₗ[ℂ] V) →* ℂˣ).map_mul,
    ProjectiveRepresentation.det_scalarLinearEquiv,
    quotientScalar_apply,
    mk_determinantCosetRepresentative,
    R.determinantQuotientRescaling_pow q hq]
  exact inv_mul_cancel _

/-- Every operator determinant in the association-preserving normalization is
an `|N|`th root of unity. -/
theorem associatedFiniteFactorProjective_operator_det_pow
    (R : AssociatedProjectiveRepresentation T V P)
    (a : A) :
    LinearEquiv.det
        (R.associatedFiniteFactorProjective.operator a) ^
      Nat.card T.normalSubgroup = 1 := by
  let q : A ⧸ T.normalSubgroup :=
    QuotientGroup.mk' T.normalSubgroup a
  by_cases hq : q = 1
  · have ha : a ∈ T.normalSubgroup :=
      (QuotientGroup.eq_one_iff a).mp hq
    let x : T.normalSubgroup := ⟨a, ha⟩
    rw [← R.associatedFiniteFactorAssociated.restriction_apply x]
    exact R.associatedFiniteFactorAssociated.restriction_det_pow_card x
  · let r : A := determinantCosetRepresentative q
    have hrq :
        QuotientGroup.mk' T.normalSubgroup r = q := by
      exact mk_determinantCosetRepresentative q
    have hra :
        QuotientGroup.mk' T.normalSubgroup r =
          QuotientGroup.mk' T.normalSubgroup a := by
      exact hrq.trans rfl
    obtain ⟨n, hn, hrn⟩ :=
      (QuotientGroup.mk'_eq_mk'
        (N := T.normalSubgroup)).mp hra
    let x : T.normalSubgroup := ⟨n, hn⟩
    have hmul :=
      R.associatedFiniteFactorAssociated.mul_normal r x
    have hdet_r :
        LinearEquiv.det
          (R.associatedFiniteFactorProjective.operator r) = 1 := by
      exact
        R.associatedFiniteFactorProjective_representative_det q hq
    rw [← hrn, hmul,
      (LinearEquiv.det :
        (V ≃ₗ[ℂ] V) →* ℂˣ).map_mul,
      hdet_r, one_mul,
      ← R.associatedFiniteFactorAssociated.restriction_apply x]
    exact R.associatedFiniteFactorAssociated.restriction_det_pow_card x

/-- The factor of the association-preserving normalization is an
`(dim V * |N|)`th root of unity. -/
theorem associatedFiniteFactorProjective_factor_pow
    (R : AssociatedProjectiveRepresentation T V P)
    (g h : A) :
    R.associatedFiniteFactorProjective.factor g h ^
        associatedFactorExponent T V = 1 := by
  have hdet :=
    congrArg
      (LinearEquiv.det :
        (V ≃ₗ[ℂ] V) →* ℂˣ)
      (R.associatedFiniteFactorProjective.map_mul g h)
  rw [
    (LinearEquiv.det :
      (V ≃ₗ[ℂ] V) →* ℂˣ).map_mul,
    (LinearEquiv.det :
      (V ≃ₗ[ℂ] V) →* ℂˣ).map_mul,
    ProjectiveRepresentation.det_scalarLinearEquiv] at hdet
  have hdetPow :=
    congrArg
      (fun z : ℂˣ ↦ z ^ Nat.card T.normalSubgroup)
      hdet
  rw [mul_pow, mul_pow,
    R.associatedFiniteFactorProjective_operator_det_pow,
    R.associatedFiniteFactorProjective_operator_det_pow,
    R.associatedFiniteFactorProjective_operator_det_pow,
    one_mul, mul_one] at hdetPow
  simpa [associatedFactorExponent, pow_mul] using hdetPow.symm

/-- The factor set of the association-preserving lift, bundled with values in
the finite group of roots of unity. -/
def associatedFiniteFactorSet
    (R : AssociatedProjectiveRepresentation T V P) :
    FactorSet A (rootsOfUnity (associatedFactorExponent T V) ℂ) where
  toFun g h :=
    ⟨R.associatedFiniteFactorProjective.factor g h,
      R.associatedFiniteFactorProjective_factor_pow g h⟩
  cocycle' g h k := by
    apply Subtype.ext
    exact R.associatedFiniteFactorProjective.factor_cocycle g h k

@[simp]
theorem associatedFiniteFactorSet_coe
    (R : AssociatedProjectiveRepresentation T V P)
    (g h : A) :
    ((R.associatedFiniteFactorSet g h :
        rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ) =
      R.associatedFiniteFactorProjective.factor g h :=
  rfl

theorem associatedFiniteFactorSet_isNormalized
    (R : AssociatedProjectiveRepresentation T V P) :
    R.associatedFiniteFactorSet.IsNormalized := by
  have hnormalized :
      R.associatedFiniteFactorProjective.factorSet.IsNormalized :=
    R.associatedFiniteFactorProjective.factorSet_isNormalized
      R.associatedFiniteFactorProjective_isNormalized
  constructor
  · intro g
    apply Subtype.ext
    exact hnormalized.1 g
  · intro g
    apply Subtype.ext
    exact hnormalized.2 g

/-- The complete association-preserving finite-factor normalization package. -/
structure AssociatedFiniteFactorNormalization
    (R : AssociatedProjectiveRepresentation T V P) where
  /-- The quotient-coset-rescaled projective representation. -/
  projective : ProjectiveRepresentation ℂ A V
  /-- The rescaled lift remains associated with the original triple. -/
  associated : AssociatedProjectiveRepresentation T V projective
  /-- The rescaled lift is normalized. -/
  isNormalized : projective.IsNormalized
  /-- Its factor set, valued in a finite roots-of-unity group. -/
  factorSet :
    FactorSet A (rootsOfUnity (associatedFactorExponent T V) ℂ)
  /-- Forgetting the roots-of-unity codomain recovers the exact projective
  factor, with no cohomological or propositional replacement. -/
  factorSet_coe :
    ∀ g h : A,
      ((factorSet g h :
          rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ) =
        projective.factor g h

/-- Bundle the normalized associated projective lift and its finite-valued
factor set. -/
def finiteFactorNormalization
    (R : AssociatedProjectiveRepresentation T V P) :
    AssociatedFiniteFactorNormalization R where
  projective := R.associatedFiniteFactorProjective
  associated := R.associatedFiniteFactorAssociated
  isNormalized := R.associatedFiniteFactorProjective_isNormalized
  factorSet := R.associatedFiniteFactorSet
  factorSet_coe := R.associatedFiniteFactorSet_coe

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
