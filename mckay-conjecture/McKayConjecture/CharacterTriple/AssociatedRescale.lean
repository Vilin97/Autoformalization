/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import McKayConjecture.CharacterTriple.CentralIsomorphism

/-!
# Coset-constant rescaling of associated projective representations

An associated projective lift may be rescaled without changing its exact
normal-subgroup restriction provided the scalar cochain is trivial on the
normal subgroup and constant on its left and right cosets.  In particular,
every normalized scalar cochain on the quotient gives such a rescaling.

This is the form needed when replacing the factor set by one with finite
root-of-unity image in the projective central-extension argument.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace CharacterTriple

variable {A : Type u} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

namespace AssociatedProjectiveRepresentation

/-- Every associated projective lift is normalized, because its identity
operator is the identity of the honest normal-subgroup restriction. -/
theorem isNormalized
    (R : AssociatedProjectiveRepresentation T V P) :
    P.IsNormalized := by
  rw [ProjectiveRepresentation.IsNormalized]
  calc
    P.operator 1 =
        R.restriction (1 : T.normalSubgroup) := by
          simpa using
            (R.restriction_apply
              (1 : T.normalSubgroup)).symm
    _ = 1 := map_one R.restriction

/-- Rescaling by a normal-trivial, two-sided coset-constant scalar cochain
preserves associatedness with the same exact normal restriction. -/
def rescaleOfNormalTrivialCosetConstant
    (R : AssociatedProjectiveRepresentation T V P)
    (c : A → ℂˣ)
    (hnormal :
      ∀ x : T.normalSubgroup, c (x : A) = 1)
    (hleft :
      ∀ (x : T.normalSubgroup) (a : A),
        c ((x : A) * a) = c a)
    (hright :
      ∀ (a : A) (x : T.normalSubgroup),
        c (a * (x : A)) = c a) :
    AssociatedProjectiveRepresentation T V (P.rescale c) where
  restriction := R.restriction
  restriction_apply x := by
    rw [ProjectiveRepresentation.rescale_operator,
      hnormal x, map_one, one_mul]
    exact R.restriction_apply x
  restriction_simple := R.restriction_simple
  restriction_character := R.restriction_character
  normal_mul x a := by
    rw [ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      hleft x a, hnormal x, map_one, one_mul, R.normal_mul]
    calc
      scalarLinearEquiv ℂ V (c a) *
          (P.operator (x : A) * P.operator a) =
        (scalarLinearEquiv ℂ V (c a) *
            P.operator (x : A)) *
          P.operator a := (mul_assoc _ _ _).symm
      _ =
        (P.operator (x : A) *
            scalarLinearEquiv ℂ V (c a)) *
          P.operator a := by
            rw [scalarLinearEquiv_comm]
      _ =
        P.operator (x : A) *
          (scalarLinearEquiv ℂ V (c a) *
            P.operator a) := mul_assoc _ _ _
  mul_normal a x := by
    rw [ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      hright a x, hnormal x, map_one, one_mul, R.mul_normal]
    exact (mul_assoc _ _ _).symm

/-- Pull a scalar cochain on the quotient back to the ambient group. -/
def quotientScalar
    (c : A ⧸ T.normalSubgroup → ℂˣ) :
    A → ℂˣ :=
  fun a ↦ c (QuotientGroup.mk' T.normalSubgroup a)

@[simp]
theorem quotientScalar_apply
    (c : A ⧸ T.normalSubgroup → ℂˣ) (a : A) :
    quotientScalar c a =
      c (QuotientGroup.mk' T.normalSubgroup a) :=
  rfl

/-- A normalized quotient cochain pulls back to one on the normal
subgroup. -/
theorem quotientScalar_normal
    (c : A ⧸ T.normalSubgroup → ℂˣ)
    (hc : c 1 = 1)
    (x : T.normalSubgroup) :
    quotientScalar c (x : A) = 1 := by
  have hx :
      QuotientGroup.mk' T.normalSubgroup (x : A) = 1 :=
    (QuotientGroup.eq_one_iff (x : A)).mpr x.property
  rw [quotientScalar_apply, hx, hc]

/-- A quotient scalar is constant on left normal cosets. -/
theorem quotientScalar_normal_mul
    (c : A ⧸ T.normalSubgroup → ℂˣ)
    (x : T.normalSubgroup) (a : A) :
    quotientScalar c ((x : A) * a) =
      quotientScalar c a := by
  have hx :
      QuotientGroup.mk' T.normalSubgroup (x : A) = 1 :=
    (QuotientGroup.eq_one_iff (x : A)).mpr x.property
  rw [quotientScalar_apply, quotientScalar_apply, map_mul, hx, one_mul]

/-- A quotient scalar is constant on right normal cosets. -/
theorem quotientScalar_mul_normal
    (c : A ⧸ T.normalSubgroup → ℂˣ)
    (a : A) (x : T.normalSubgroup) :
    quotientScalar c (a * (x : A)) =
      quotientScalar c a := by
  have hx :
      QuotientGroup.mk' T.normalSubgroup (x : A) = 1 :=
    (QuotientGroup.eq_one_iff (x : A)).mpr x.property
  rw [quotientScalar_apply, quotientScalar_apply, map_mul, hx, mul_one]

/-- Rescaling an associated projective lift by the pullback of a normalized
quotient cochain preserves associatedness. -/
def rescaleByQuotientScalar
    (R : AssociatedProjectiveRepresentation T V P)
    (c : A ⧸ T.normalSubgroup → ℂˣ)
    (hc : c 1 = 1) :
    AssociatedProjectiveRepresentation T V
      (P.rescale (quotientScalar c)) :=
  R.rescaleOfNormalTrivialCosetConstant
    (quotientScalar c)
    (quotientScalar_normal c hc)
    (quotientScalar_normal_mul c)
    (quotientScalar_mul_normal c)

end AssociatedProjectiveRepresentation

end CharacterTriple
end McKayConjecture
