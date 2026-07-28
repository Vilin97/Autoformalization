/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerScalarIdentificationFinrankOne
import McKayConjecture.CharacterTriple.MagicLinearizationFromCovariance

/-!
# Magic linearization from a one-dimensional Brauer quotient

The scalar identification in the Dade normalizer argument need not be
supplied separately when the relevant algebra Brauer quotient is
one-dimensional: it is then the canonical scalar algebra.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {K P G V : Type}
variable [Field K] [Group P] [Fintype P] [Group G]
variable [AddCommGroup V] [Module K V]

/-- Direct normalizer-data form of the one-dimensional Brauer-quotient
criterion. -/
def magicLinearizationOfNormalizerDataOfFinrankOne
    [MulSemiringAction P (Module.End K V)]
    [SMulCommClass P K (Module.End K V)]
    (Q : ProjectiveRepresentation K G V)
    (I : InteriorAction (P := P) (A := Module.End K V))
    (operator_mem :
      ∀ g, operatorUnit (Q.operator g) ∈ I.unitNormalizer)
    (operator_one : Q.operator 1 = 1)
    (E : BrauerNormalizerExtension (k := K) I)
    (hfin :
      Module.finrank K
          (BrauerQuotientAlgebra
            (k := K) (P := P) (A := Module.End K V)) =
        1) :
    MagicLinearization Q :=
  magicLinearizationOfNormalizerData Q I
    operator_mem operator_one E
    (brauerScalarIdentificationOfFinrankOne hfin)

/-- Covariant projective operators admit a magic linearization from a
Brauer-normalizer extension as soon as the endomorphism-algebra Brauer
quotient has dimension one. -/
def magicLinearizationOfCovariantNormalizerDataOfFinrankOne
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
    (hfin :
      letI :=
        endomorphismConjugationMulSemiringAction ρ
      letI :=
        endomorphismConjugation_smulCommClass ρ
      Module.finrank K
          (BrauerQuotientAlgebra
            (k := K) (P := P) (A := Module.End K V)) =
        1) :
    MagicLinearization Q := by
  letI :=
    endomorphismConjugationMulSemiringAction ρ
  letI :=
    endomorphismConjugation_smulCommClass ρ
  exact
    magicLinearizationOfCovariantNormalizerData
      Q ρ φ hcov operator_one E
      (brauerScalarIdentificationOfFinrankOne hfin)

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
