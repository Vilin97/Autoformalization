/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralProjectiveScalarCorrection
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveFactorCohomology
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveScalarMismatch

/-!
# Central projective comparisons from an extendible scalar mismatch

After quotient factor classes have been matched, the remaining scalar
discrepancy is a linear character of the projective-comparison centralizer.
It need not be trivial for the initially chosen lifts.  The natural DGN
condition is instead that it extend to the right inertia group, trivially
on the distinguished normal subgroup.  Rescaling by that extension changes
neither the factor set nor the normal restriction and kills the discrepancy.

This file packages that correction first for literally matched factors and
then for factor classes which agree in `H²`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

/-- Literally factor-matched associated lifts together with an ambient
linear character extending their scalar mismatch. -/
structure ScalarCorrectableFactorMatchedProjectiveComparisonData
    (T : CharacterTriple A) (U : CharacterTriple B)
    (e : B →* A)
    (g : CentralRestrictionGroupData T U e) where
  leftSpace : Type
  rightSpace : Type
  [leftAddCommGroup : AddCommGroup leftSpace]
  [leftModule : Module ℂ leftSpace]
  [leftModuleFinite : Module.Finite ℂ leftSpace]
  [leftNontrivial : Nontrivial leftSpace]
  [rightAddCommGroup : AddCommGroup rightSpace]
  [rightModule : Module ℂ rightSpace]
  [rightModuleFinite : Module.Finite ℂ rightSpace]
  [rightNontrivial : Nontrivial rightSpace]
  leftProjective :
    ProjectiveRepresentation ℂ A leftSpace
  leftAssociated :
    AssociatedProjectiveRepresentation
      T leftSpace leftProjective
  rightProjective :
    ProjectiveRepresentation ℂ B rightSpace
  rightAssociated :
    AssociatedProjectiveRepresentation
      U rightSpace rightProjective
  factor_agreement :
    ∀ b c : B,
      leftProjective.factor (e b) (e c) =
        rightProjective.factor b c
  scalarCorrection : B →* ℂˣ
  scalarCorrection_normal :
    ∀ x : U.normalSubgroup,
      scalarCorrection (x : B) = 1
  scalarCorrection_restrict :
    ∀ b : projectiveComparisonCentralizer T e,
      scalarCorrection b =
        leftAssociated.comparisonCentralScalarMismatch
          rightAssociated
          g.projectiveComparisonCentralizer_le_rightCentralizer
          factor_agreement b

namespace ScalarCorrectableFactorMatchedProjectiveComparisonData

/-- Applying the extending character to the right lift produces a complete
central projective comparison. -/
def toCompleteCentralProjectiveComparisonData
    (d :
      ScalarCorrectableFactorMatchedProjectiveComparisonData
        T U e g) :
    CompleteCentralProjectiveComparisonData T U e := by
  letI := d.leftAddCommGroup
  letI := d.leftModule
  letI := d.leftModuleFinite
  letI := d.leftNontrivial
  letI := d.rightAddCommGroup
  letI := d.rightModule
  letI := d.rightModuleFinite
  letI := d.rightNontrivial
  let correctedAssociated :=
    d.rightAssociated.rescaleByNormalTrivialCharacter
      d.scalarCorrection d.scalarCorrection_normal
  let correctedFactorAgreement :
      ∀ b c : B,
        d.leftProjective.factor (e b) (e c) =
          (d.rightProjective.rescale
            d.scalarCorrection).factor b c :=
    fun b c ↦ by
      simpa using d.factor_agreement b c
  exact
    CompleteCentralProjectiveComparisonData.ofAssociatedFactorAgreementMismatchTrivial
      d.leftAssociated correctedAssociated g
      correctedFactorAgreement
      (d.leftAssociated
        |>.comparisonCentralScalarMismatch_rescaleByNormalTrivialCharacter_eq_one
          d.rightAssociated
          g.projectiveComparisonCentralizer_le_rightCentralizer
          d.factor_agreement
          d.scalarCorrection
          d.scalarCorrection_normal
          d.scalarCorrection_restrict)

end ScalarCorrectableFactorMatchedProjectiveComparisonData

/-- `H²`-matched associated lifts whose post-gauge scalar mismatch extends
to the right ambient group, trivially on its normal subgroup. -/
structure H2ScalarCorrectableProjectiveComparisonData
    (T : CharacterTriple A) (U : CharacterTriple B)
    (e : B →* A)
    (g : CentralRestrictionGroupData T U e) where
  leftSpace : Type
  rightSpace : Type
  [leftAddCommGroup : AddCommGroup leftSpace]
  [leftModule : Module ℂ leftSpace]
  [leftModuleFinite : Module.Finite ℂ leftSpace]
  [leftNontrivial : Nontrivial leftSpace]
  [rightAddCommGroup : AddCommGroup rightSpace]
  [rightModule : Module ℂ rightSpace]
  [rightModuleFinite : Module.Finite ℂ rightSpace]
  [rightNontrivial : Nontrivial rightSpace]
  leftProjective :
    ProjectiveRepresentation ℂ A leftSpace
  leftAssociated :
    AssociatedProjectiveRepresentation
      T leftSpace leftProjective
  rightProjective :
    ProjectiveRepresentation ℂ B rightSpace
  rightAssociated :
    AssociatedProjectiveRepresentation
      U rightSpace rightProjective
  quotientFactorH2ClassAgreement :
    leftAssociated.QuotientFactorH2ClassAgreement
      rightAssociated g
  scalarCorrection : B →* ℂˣ
  scalarCorrection_normal :
    ∀ x : U.normalSubgroup,
      scalarCorrection (x : B) = 1
  scalarCorrection_restrict :
    let factorAgreement :=
      leftAssociated.quotientFactorCohomologyAgreement_of_h2Class
        rightAssociated g quotientFactorH2ClassAgreement
    let factorMatchedRight :=
      leftAssociated.factorMatchedRightAssociated
        rightAssociated g factorAgreement
    ∀ b : projectiveComparisonCentralizer T e,
      scalarCorrection b =
        leftAssociated.comparisonCentralScalarMismatch
          factorMatchedRight
          g.projectiveComparisonCentralizer_le_rightCentralizer
          (leftAssociated.factorMatchedRightAssociated_factor_agreement
            rightAssociated g factorAgreement) b

namespace H2ScalarCorrectableProjectiveComparisonData

/-- Convert `H²` agreement plus extendibility of the scalar mismatch into
the literal factor-matched correction package. -/
def toScalarCorrectableFactorMatchedProjectiveComparisonData
    (d :
      H2ScalarCorrectableProjectiveComparisonData
        T U e g) :
    ScalarCorrectableFactorMatchedProjectiveComparisonData
      T U e g := by
  letI := d.leftAddCommGroup
  letI := d.leftModule
  letI := d.leftModuleFinite
  letI := d.leftNontrivial
  letI := d.rightAddCommGroup
  letI := d.rightModule
  letI := d.rightModuleFinite
  letI := d.rightNontrivial
  let factorAgreement :=
    d.leftAssociated.quotientFactorCohomologyAgreement_of_h2Class
      d.rightAssociated g
      d.quotientFactorH2ClassAgreement
  exact
    { leftSpace := d.leftSpace
      rightSpace := d.rightSpace
      leftProjective := d.leftProjective
      leftAssociated := d.leftAssociated
      rightProjective :=
        d.rightProjective.rescale
          (AssociatedProjectiveRepresentation.quotientScalar
            (d.leftAssociated.factorMatchingQuotientScalar
              d.rightAssociated g factorAgreement))
      rightAssociated :=
        d.leftAssociated.factorMatchedRightAssociated
          d.rightAssociated g factorAgreement
      factor_agreement :=
        d.leftAssociated.factorMatchedRightAssociated_factor_agreement
          d.rightAssociated g factorAgreement
      scalarCorrection := d.scalarCorrection
      scalarCorrection_normal := d.scalarCorrection_normal
      scalarCorrection_restrict := d.scalarCorrection_restrict }

/-- The two correction steps—first matching factors, then extending and
removing the scalar mismatch—construct the complete comparison. -/
def toCompleteCentralProjectiveComparisonData
    (d :
      H2ScalarCorrectableProjectiveComparisonData
        T U e g) :
    CompleteCentralProjectiveComparisonData T U e :=
  d.toScalarCorrectableFactorMatchedProjectiveComparisonData
    |>.toCompleteCentralProjectiveComparisonData

end H2ScalarCorrectableProjectiveComparisonData

end InductiveMcKay
end McKayConjecture
