/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorNormalization
import McKayConjecture.CharacterTriple.ProjectiveFactorDeterminantCoboundary
import McKayConjecture.CharacterTriple.ProjectiveObstructionClass

/-!
# An unconditional exponent bound for the outer projective obstruction

The determinant cochain of an associated projective representation need not
descend to the outer quotient.  Association-preserving determinant
normalization nevertheless gives an honest unconditional bound: if `d` is
the representation dimension and `N` the distinguished normal subgroup,
then `d * |N|` annihilates the outer factor class.

The factor `|N|` records exactly the possible nontrivial determinant
character of the normal restriction.
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

/-- The quotient factor set after association-preserving determinant
normalization is the gauge transform of the original quotient factor set by
the quotient determinant-rescaling cochain. -/
theorem associatedFiniteFactor_quotientFactorSet_eq_gauge
    (R : AssociatedProjectiveRepresentation T V P) :
    R.associatedFiniteFactorAssociated.quotientFactorSet =
      R.quotientFactorSet.gauge
        R.determinantQuotientRescaling := by
  apply FactorSet.ext
  intro q r
  let a :=
    ProjectiveRepresentation.quotientRepresentative
      T.normalSubgroup q
  let b :=
    ProjectiveRepresentation.quotientRepresentative
      T.normalSubgroup r
  have ha :
      (↑(ProjectiveRepresentation.quotientRepresentative
          T.normalSubgroup q) :
        A ⧸ T.normalSubgroup) = q := by
    exact
      ProjectiveRepresentation.mk_quotientRepresentative
        T.normalSubgroup q
  have hb :
      (↑(ProjectiveRepresentation.quotientRepresentative
          T.normalSubgroup r) :
        A ⧸ T.normalSubgroup) = r := by
    exact
      ProjectiveRepresentation.mk_quotientRepresentative
        T.normalSubgroup r
  change
    R.associatedFiniteFactorProjective.factor a b =
      R.determinantQuotientRescaling q *
          R.determinantQuotientRescaling r /
          R.determinantQuotientRescaling (q * r) *
        P.factor a b
  rw [associatedFiniteFactorProjective,
    ProjectiveRepresentation.rescale_factor]
  dsimp [a, b]
  rw [ha, hb]

/-- The `(dimension * |N|)`th power of the normalized quotient factor is
the constant-one two-coboundary. -/
theorem associatedFiniteFactor_quotientFactorSet_pow_exponent_isMulCoboundary₂
    (R : AssociatedProjectiveRepresentation T V P) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    groupCohomology.IsMulCoboundary₂
      (fun x :
          (A ⧸ T.normalSubgroup) ×
            (A ⧸ T.normalSubgroup) ↦
        R.associatedFiniteFactorAssociated.quotientFactorSet
            x.1 x.2 ^
          associatedFactorExponent T V) := by
  letI :=
    trivialMulDistribMulAction
      (A ⧸ T.normalSubgroup) ℂˣ
  refine ⟨fun _ ↦ 1, ?_⟩
  intro q r
  change
    (1 : ℂˣ) / 1 * 1 =
      R.associatedFiniteFactorAssociated.quotientFactorSet
          q r ^ associatedFactorExponent T V
  simp only [div_one, one_mul]
  let a :=
    ProjectiveRepresentation.quotientRepresentative
      T.normalSubgroup q
  let b :=
    ProjectiveRepresentation.quotientRepresentative
      T.normalSubgroup r
  change
    1 =
      R.associatedFiniteFactorProjective.factor a b ^
        associatedFactorExponent T V
  exact
    (R.associatedFiniteFactorProjective_factor_pow a b).symm

/-- The association-preserving exponent annihilates the normalized
quotient factor class. -/
theorem associatedFactorExponent_nsmul_normalizedQuotientFactor_h2Class_eq_zero
    (R : AssociatedProjectiveRepresentation T V P) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    associatedFactorExponent T V •
        R.associatedFiniteFactorAssociated.quotientFactorSet.h2Class =
      0 := by
  exact
    R.associatedFiniteFactorAssociated.quotientFactorSet
      |>.nsmul_h2Class_eq_zero_of_pow_isMulCoboundary₂
        (associatedFactorExponent T V)
        R.associatedFiniteFactor_quotientFactorSet_pow_exponent_isMulCoboundary₂

/-- Unconditionally, `dimension * |N|` annihilates the outer factor class of
an associated projective representation. -/
theorem associatedFactorExponent_nsmul_quotientFactorSet_h2Class_eq_zero
    (R : AssociatedProjectiveRepresentation T V P) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    associatedFactorExponent T V •
        R.quotientFactorSet.h2Class =
      0 := by
  have hclass :
      R.associatedFiniteFactorAssociated.quotientFactorSet.h2Class =
        R.quotientFactorSet.h2Class := by
    rw [R.associatedFiniteFactor_quotientFactorSet_eq_gauge,
      FactorSet.h2Class_gauge]
  calc
    associatedFactorExponent T V •
          R.quotientFactorSet.h2Class =
        associatedFactorExponent T V •
          R.associatedFiniteFactorAssociated.quotientFactorSet.h2Class := by
            rw [hclass]
    _ = 0 :=
      R.associatedFactorExponent_nsmul_normalizedQuotientFactor_h2Class_eq_zero

/-- Unconditionally, `dimension * |N|` annihilates the intrinsic projective
obstruction class. -/
theorem associatedFactorExponent_nsmul_projectiveObstructionClass_eq_zero
    (R : AssociatedProjectiveRepresentation T V P) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    associatedFactorExponent T V •
        T.projectiveObstructionClass =
      0 := by
  rw [← R.quotientFactorSet_h2Class_eq_projectiveObstructionClass]
  exact
    R.associatedFactorExponent_nsmul_quotientFactorSet_h2Class_eq_zero

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
