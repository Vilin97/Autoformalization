/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.MagicLinearizationFromNormalizer
import McKayConjecture.CharacterTriple.ProjectiveInteriorNormalizer

/-!
# Magic linearization from covariant interior data

This file combines the two elementary sides of the Dade normalizer
argument.  Covariance puts every projective operator in the interior
normalizer; a Brauer-normalizer extension and a scalar identification of
the Brauer quotient then remove its factor set.

The remaining deep input is precisely the construction of the extension
and scalar identification for the relevant Dade algebra.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {K P G V : Type}
variable [Field K] [Group P] [Fintype P] [Group G]
variable [AddCommGroup V] [Module K V]

/-- A covariant normalized projective action is magic-linearized once
Dade's extension of the Brauer map and the scalar Brauer identification
have been supplied. -/
def magicLinearizationOfCovariantNormalizerData
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (φ : G →* MulAut P)
    (hcov : Q.IsCovariantWith ρ φ)
    (operator_one : Q.operator 1 = 1)
    (E :
      letI :=
        endomorphismConjugationMulSemiringAction ρ
      letI :=
        endomorphismConjugation_smulCommClass ρ
      BrauerNormalizerExtension (k := K)
        (interiorActionOfLinearAction ρ))
    (Z :
      letI :=
        endomorphismConjugationMulSemiringAction ρ
      letI :=
        endomorphismConjugation_smulCommClass ρ
      BrauerScalarIdentification
        (k := K) (P := P) (A := Module.End K V)) :
    MagicLinearization Q := by
  letI :=
    endomorphismConjugationMulSemiringAction ρ
  letI :=
    endomorphismConjugation_smulCommClass ρ
  let I := interiorActionOfLinearAction ρ
  exact
    magicLinearizationOfNormalizerData Q I
      (operatorUnit_mem_linearActionUnit_normalizer
        Q ρ φ hcov)
      operator_one E Z

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
