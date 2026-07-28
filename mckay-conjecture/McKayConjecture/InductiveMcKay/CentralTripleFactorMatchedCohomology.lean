/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleFactorMatchedCharacterEquiv
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveFactorCohomology

/-!
# Factor-matched character equivalences from quotient cohomology

Equality of the intrinsic projective obstruction classes supplies a
quotient cochain.  Rescaling the right associated projective
representation by that cochain makes the two factor sets agree literally.

The ordinary character correspondence needs no scalar comparison on a
centralizer.  This file therefore stops immediately after factor matching
and packages the resulting prime-to-`p` character equivalence.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Finite A] [Group A] [Finite B] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

/-- Quotient-factor cohomology agreement, with no scalar-mismatch
assumption, produces the complete projective data needed by the ordinary
factor-matched character correspondence. -/
def completeFactorMatchedProjectiveComparisonDataOfQuotientCohomology
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorCohomologyAgreement S g) :
    CompleteFactorMatchedProjectiveComparisonData T U e :=
  { leftSpace := V
    rightSpace := W
    leftProjective := P
    leftAssociated := R
    rightProjective :=
      Q.rescale
        (AssociatedProjectiveRepresentation.quotientScalar
          (R.factorMatchingQuotientScalar S g h))
    rightAssociated :=
      R.factorMatchedRightAssociated S g h
    factor_agreement :=
      R.factorMatchedRightAssociated_factor_agreement S g h }

/-- Add the ordinary subgroup conditions to the cohomologically
factor-matched projective lifts. -/
def completeFactorMatchedIsomorphismWitnessOfQuotientCohomology
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorCohomologyAgreement S g) :
    CompleteFactorMatchedIsomorphismWitness T U :=
  (completeFactorMatchedProjectiveComparisonDataOfQuotientCohomology
      R S g h
    ).toCompleteFactorMatchedIsomorphismWitness
      g.toFactorMatchedRestrictionGroupData

/-- The prime-to-`p` character equivalence obtained directly from
quotient-factor cohomology agreement. -/
def pPrimeIrreducibleCharactersOverEquivOfQuotientCohomology
    {p : ℕ} (hp : p.Prime)
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorCohomologyAgreement S g)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character ≃
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character :=
  (completeFactorMatchedIsomorphismWitnessOfQuotientCohomology
      R S g h
    ).pPrimeIrreducibleCharactersOverEquiv hp hT hU

end InductiveMcKay
end McKayConjecture
