/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveH2Mismatch
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveNormalCentralMismatch

/-!
# The residual projective obstruction after the matched normal center

For a central restriction, normalized equality of the distinguished normal
characters kills the scalar mismatch on the matched part of the normal
subgroup.  The mismatch therefore factors through a quotient.  This file
combines that reduction with equality of the quotient factor classes in
`H²`.

The two remaining intrinsic claims are:

* equality of the quotient factor classes in `H²`; and
* triviality of the residual quotient character.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

/-- Associated lifts whose factor classes agree in `H²`, whose normalized
normal-central values agree, and whose remaining quotient mismatch is
trivial. -/
structure H2NormalCentralMismatchProjectiveComparisonData
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
  normalizedNormalCentralValuesAgree :
    g.NormalizedNormalCentralValuesAgree
  residualMismatch_trivial :
    let factorAgreement :=
      leftAssociated.quotientFactorCohomologyAgreement_of_h2Class
        rightAssociated g quotientFactorH2ClassAgreement
    leftAssociated.postFactorMatchingScalarMismatchQuotient
        rightAssociated g factorAgreement
        normalizedNormalCentralValuesAgree =
      1

namespace H2NormalCentralMismatchProjectiveComparisonData

/-- Triviality of the quotient character is equivalent to triviality of
the full post-factor-matching mismatch, so this package supplies the simpler
`H²`-mismatch interface. -/
def toH2MismatchProjectiveComparisonData
    (d :
      H2NormalCentralMismatchProjectiveComparisonData
        T U e g) :
    H2MismatchProjectiveComparisonData T U e g := by
  letI := d.leftAddCommGroup
  letI := d.leftModule
  letI := d.leftModuleFinite
  letI := d.leftNontrivial
  letI := d.rightAddCommGroup
  letI := d.rightModule
  letI := d.rightModuleFinite
  letI := d.rightNontrivial
  let hcoh :=
    d.leftAssociated.quotientFactorCohomologyAgreement_of_h2Class
      d.rightAssociated g
      d.quotientFactorH2ClassAgreement
  exact
    { leftSpace := d.leftSpace
      rightSpace := d.rightSpace
      leftProjective := d.leftProjective
      leftAssociated := d.leftAssociated
      rightProjective := d.rightProjective
      rightAssociated := d.rightAssociated
      quotientFactorH2ClassAgreement :=
        d.quotientFactorH2ClassAgreement
      postRescalingMismatch_trivial :=
        (d.leftAssociated.postFactorMatchingScalarMismatchQuotient_eq_one_iff
          d.rightAssociated g hcoh
          d.normalizedNormalCentralValuesAgree).mp
            d.residualMismatch_trivial }

/-- The intrinsic `H²` equality and residual quotient claim construct the
complete central projective comparison. -/
def toCompleteCentralProjectiveComparisonData
    (d :
      H2NormalCentralMismatchProjectiveComparisonData
        T U e g) :
    CompleteCentralProjectiveComparisonData T U e :=
  d.toH2MismatchProjectiveComparisonData
    |>.toCompleteCentralProjectiveComparisonData

end H2NormalCentralMismatchProjectiveComparisonData

end InductiveMcKay
end McKayConjecture
