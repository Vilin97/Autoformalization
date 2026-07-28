/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveFactorCohomology
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveScalarMismatch

/-!
# Central-triple comparisons from two cohomological obstructions

For independently chosen associated projective lifts, literal factor
agreement need not hold.  The first obstruction is equality of their
factor-set classes on the identified outer quotients.  A quotient cochain
representing that equality canonically rescales the right lift and preserves
association.  The second obstruction is then the scalar-mismatch character
of the factor-matched lifts on the full matched centralizer.

This file packages precisely those two claims and proves that they imply the
complete projective comparison used by the central character-triple
reduction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

/-- Independently associated lifts together with exactly the two remaining
comparison claims:

* their quotient factor sets are cohomologous; and
* after the resulting quotient rescaling, their central scalar mismatch is
  trivial.
-/
structure CohomologyMismatchProjectiveComparisonData
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
  quotientFactorCohomologyAgreement :
    leftAssociated.QuotientFactorCohomologyAgreement
      rightAssociated g
  postRescalingMismatch_trivial :
    leftAssociated.comparisonCentralScalarMismatch
        (leftAssociated.factorMatchedRightAssociated
          rightAssociated g quotientFactorCohomologyAgreement)
        g.projectiveComparisonCentralizer_le_rightCentralizer
        (leftAssociated.factorMatchedRightAssociated_factor_agreement
          rightAssociated g quotientFactorCohomologyAgreement) =
      1

namespace CohomologyMismatchProjectiveComparisonData

/-- Quotient cohomology gives literal factor matching, and the second field
then supplies the standard factor-matched obstruction package. -/
def toFactorMatchedAssociatedProjectiveComparisonData
    (d :
      CohomologyMismatchProjectiveComparisonData
        T U e g) :
    FactorMatchedAssociatedProjectiveComparisonData
      T U e g := by
  letI := d.leftAddCommGroup
  letI := d.leftModule
  letI := d.leftModuleFinite
  letI := d.leftNontrivial
  letI := d.rightAddCommGroup
  letI := d.rightModule
  letI := d.rightModuleFinite
  letI := d.rightNontrivial
  exact
    { leftSpace := d.leftSpace
      rightSpace := d.rightSpace
      leftProjective := d.leftProjective
      leftAssociated := d.leftAssociated
      rightProjective :=
        d.rightProjective.rescale
          (AssociatedProjectiveRepresentation.quotientScalar
            (d.leftAssociated.factorMatchingQuotientScalar
              d.rightAssociated g
              d.quotientFactorCohomologyAgreement))
      rightAssociated :=
        d.leftAssociated.factorMatchedRightAssociated
          d.rightAssociated g
          d.quotientFactorCohomologyAgreement
      factor_agreement :=
        d.leftAssociated.factorMatchedRightAssociated_factor_agreement
          d.rightAssociated g
          d.quotientFactorCohomologyAgreement
      mismatch_trivial :=
        d.postRescalingMismatch_trivial }

/-- The two obstruction claims construct a complete central projective
comparison. -/
def toCompleteCentralProjectiveComparisonData
    (d :
      CohomologyMismatchProjectiveComparisonData
        T U e g) :
    CompleteCentralProjectiveComparisonData T U e :=
  d.toFactorMatchedAssociatedProjectiveComparisonData
    |>.toCompleteCentralProjectiveComparisonData

end CohomologyMismatchProjectiveComparisonData

end InductiveMcKay
end McKayConjecture
