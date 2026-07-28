/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveCohomologyMismatch

/-!
# Central-triple comparisons from equality in second cohomology

The factor obstruction for two associated projective lifts naturally lives
in `H²` of their common outer quotient.  This file replaces the explicit
gauge-cochain premise of `CohomologyMismatchProjectiveComparisonData` by
literal equality of the two classes in mathlib's `H²`.  The equivalence
between equality of classes and multiplicative gauge cohomology then
constructs the cochain used by the existing factor-matching API.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

/-- Independently associated projective lifts together with the two
intrinsic obstruction claims:

* equality of their quotient factor classes in `H²`; and
* triviality of the scalar mismatch after the factor-matching rescaling
  selected from that equality.
-/
structure H2MismatchProjectiveComparisonData
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
  postRescalingMismatch_trivial :
    let factorAgreement :=
      leftAssociated.quotientFactorCohomologyAgreement_of_h2Class
        rightAssociated g quotientFactorH2ClassAgreement
    leftAssociated.comparisonCentralScalarMismatch
        (leftAssociated.factorMatchedRightAssociated
          rightAssociated g factorAgreement)
        g.projectiveComparisonCentralizer_le_rightCentralizer
        (leftAssociated.factorMatchedRightAssociated_factor_agreement
          rightAssociated g factorAgreement) =
      1

namespace H2MismatchProjectiveComparisonData

/-- Equality of the `H²` classes produces the explicit quotient cochain and
therefore the cohomology-mismatch package. -/
def toCohomologyMismatchProjectiveComparisonData
    (d :
      H2MismatchProjectiveComparisonData
        T U e g) :
    CohomologyMismatchProjectiveComparisonData
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
      rightProjective := d.rightProjective
      rightAssociated := d.rightAssociated
      quotientFactorCohomologyAgreement :=
        d.leftAssociated.quotientFactorCohomologyAgreement_of_h2Class
          d.rightAssociated g
          d.quotientFactorH2ClassAgreement
      postRescalingMismatch_trivial :=
        d.postRescalingMismatch_trivial }

/-- The intrinsic `H²` and scalar claims construct a complete central
projective comparison. -/
def toCompleteCentralProjectiveComparisonData
    (d :
      H2MismatchProjectiveComparisonData
        T U e g) :
    CompleteCentralProjectiveComparisonData T U e :=
  d.toCohomologyMismatchProjectiveComparisonData
    |>.toCompleteCentralProjectiveComparisonData

end H2MismatchProjectiveComparisonData

end InductiveMcKay
end McKayConjecture
