/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveFactorDeterminantCoboundary
import McKayConjecture.CharacterTriple.ProjectiveObstructionClass

/-!
# Determinants and the outer projective obstruction

For an associated projective representation, the determinant coboundary on
the ambient group descends to the outer quotient exactly when the operator
determinant is constant on normal-subgroup cosets.  A sufficient condition is
that the determinant of the honest normal restriction is trivial.

Under that additional hypothesis, the representation degree annihilates the
outer factor class and hence the intrinsic projective obstruction.  Without
it the conclusion is false in general: the determinant character of the
normal constituent is precisely the obstruction to descending the cochain.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type} [Group A] [Finite A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- The determinant character of the honest normal restriction is trivial. -/
def NormalRestrictionDeterminantIsTrivial
    (R : AssociatedProjectiveRepresentation T V P) : Prop :=
  ∀ x : T.normalSubgroup,
    LinearEquiv.det (R.restriction x) = 1

/-- Triviality of the normal determinant makes ambient operator determinants
constant on quotient cosets. -/
theorem operator_det_eq_of_quotient_eq
    (R : AssociatedProjectiveRepresentation T V P)
    (hdet : R.NormalRestrictionDeterminantIsTrivial)
    {a b : A}
    (hab :
      QuotientGroup.mk' T.normalSubgroup a =
        QuotientGroup.mk' T.normalSubgroup b) :
    LinearEquiv.det (P.operator a) =
      LinearEquiv.det (P.operator b) := by
  obtain ⟨n, hn, han⟩ :=
    (QuotientGroup.mk'_eq_mk'
      (N := T.normalSubgroup)).mp hab
  let x : T.normalSubgroup := ⟨n, hn⟩
  rw [← han, R.mul_normal a x,
    (LinearEquiv.det :
      (V ≃ₗ[ℂ] V) →* ℂˣ).map_mul,
    ← R.restriction_apply x, hdet x, mul_one]

/-- The determinant cochain on the outer quotient, defined using the fixed
quotient representatives used by the factor-set descent. -/
def quotientOperatorDeterminant
    (_R : AssociatedProjectiveRepresentation T V P)
    (q : A ⧸ T.normalSubgroup) : ℂˣ :=
  LinearEquiv.det
    (P.operator
      (ProjectiveRepresentation.quotientRepresentative
        T.normalSubgroup q))

/-- If the normal determinant is trivial, the `degree`th power of the
descended factor set is an explicit two-coboundary on the outer quotient. -/
theorem quotientFactorSet_pow_finrank_isMulCoboundary₂
    (R : AssociatedProjectiveRepresentation T V P)
    (hdet : R.NormalRestrictionDeterminantIsTrivial) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    groupCohomology.IsMulCoboundary₂
      (fun x :
          (A ⧸ T.normalSubgroup) ×
            (A ⧸ T.normalSubgroup) ↦
        R.quotientFactorSet x.1 x.2 ^
          Module.finrank ℂ V) := by
  letI :=
    trivialMulDistribMulAction
      (A ⧸ T.normalSubgroup) ℂˣ
  refine ⟨R.quotientOperatorDeterminant, ?_⟩
  intro q r
  let a :=
    ProjectiveRepresentation.quotientRepresentative
      T.normalSubgroup q
  let b :=
    ProjectiveRepresentation.quotientRepresentative
      T.normalSubgroup r
  let c :=
    ProjectiveRepresentation.quotientRepresentative
      T.normalSubgroup (q * r)
  have habc :
      QuotientGroup.mk' T.normalSubgroup (a * b) =
        QuotientGroup.mk' T.normalSubgroup c := by
    calc
      QuotientGroup.mk' T.normalSubgroup (a * b) =
          QuotientGroup.mk' T.normalSubgroup a *
            QuotientGroup.mk' T.normalSubgroup b :=
        (QuotientGroup.mk' T.normalSubgroup).map_mul a b
      _ = q * r := by
        rw [ProjectiveRepresentation.mk_quotientRepresentative,
          ProjectiveRepresentation.mk_quotientRepresentative]
      _ = QuotientGroup.mk' T.normalSubgroup c :=
        (ProjectiveRepresentation.mk_quotientRepresentative
          T.normalSubgroup (q * r)).symm
  have hdetabc :
      LinearEquiv.det (P.operator (a * b)) =
        LinearEquiv.det (P.operator c) :=
    R.operator_det_eq_of_quotient_eq hdet habc
  change
    LinearEquiv.det (P.operator b) /
          LinearEquiv.det (P.operator c) *
        LinearEquiv.det (P.operator a) =
      P.factor a b ^ Module.finrank ℂ V
  rw [← hdetabc]
  exact P.determinant_coboundary_eq_factor_pow a b

/-- With trivial normal determinant, the representation dimension
annihilates the descended factor class in `H²` of the outer quotient. -/
theorem finrank_nsmul_quotientFactorSet_h2Class_eq_zero
    (R : AssociatedProjectiveRepresentation T V P)
    (hdet : R.NormalRestrictionDeterminantIsTrivial) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    Module.finrank ℂ V • R.quotientFactorSet.h2Class = 0 := by
  exact
    R.quotientFactorSet.nsmul_h2Class_eq_zero_of_pow_isMulCoboundary₂
      (Module.finrank ℂ V)
      (R.quotientFactorSet_pow_finrank_isMulCoboundary₂ hdet)

/-- With trivial normal determinant, the representation dimension
annihilates the intrinsic projective obstruction class. -/
theorem finrank_nsmul_projectiveObstructionClass_eq_zero
    (R : AssociatedProjectiveRepresentation T V P)
    (hdet : R.NormalRestrictionDeterminantIsTrivial) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    Module.finrank ℂ V • T.projectiveObstructionClass = 0 := by
  rw [← R.quotientFactorSet_h2Class_eq_projectiveObstructionClass]
  exact
    R.finrank_nsmul_quotientFactorSet_h2Class_eq_zero hdet

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
