/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupFactorNormalizerScalarFibre
import McKayConjecture.InductiveMcKay.NormalSubgroupRestrictedFactorFibre

/-!
# Restricted factor fibres from scalar-local induction

The fixed restriction of the canonical finite factor extension only needs
the scalar-preserving numerical correspondence in the lifted-Sylow
normalizer.  This file composes that weaker input with the concrete
normalizer-to-restricted-extension fibre equivalence.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupRestrictedFactorFibre

open CharacterTriple
open GroupTheory
open NormalSubgroupAssociatedFactorFibre
open NormalSubgroupFactorNormalizerFibre

variable {A : Type} [Finite A] [Group A]
variable {p : ℕ} [Fact p.Prime]

/-- Source characters over `T.character` correspond to the fixed restricted
factor fibre using only scalar-preserving local correspondences below a
central-index bound. -/
def restrictedPPrimeCharacterEquivOfCentralScalarLocalBound
    (bound : ℕ)
    (localData :
      CentralIndexBoundedCentralScalarLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    PPrimeCharactersOver T p ≃
      RestrictedPPrimeInverseCoefficientFibre T S :=
  (pPrimeCharacterEquivOfCentralScalarLocalBound
    bound localData T hT hExtensionBound S).trans
      (normalizerFibreEquivRestrictedInverseCoefficientFibre T S)

/-- Specialization of the restricted-factor equivalence to a scalar-local
central-index induction hypothesis at an ambient group `B`. -/
def restrictedPPrimeCharacterEquivOfCentralScalarLocalIH
    {B : Type} [Group B] [Finite B]
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex B →
          ∀ Q : Sylow p Y,
            Nonempty (CentralScalarLocalCorrespondence Q))
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionSmall :
      centralIndex (ExtensionGroup T) < centralIndex B)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    PPrimeCharactersOver T p ≃
      RestrictedPPrimeInverseCoefficientFibre T S :=
  (pPrimeCharacterEquivOfCentralScalarLocalIH
    ih T hT hExtensionSmall S).trans
      (normalizerFibreEquivRestrictedInverseCoefficientFibre T S)

/-- The scalar-local-IH restricted-factor output has the exact inverse
coefficient values in the fixed pulled-back extension. -/
theorem restrictedPPrimeCharacterEquivOfCentralScalarLocalIH_coefficient_value
    {B : Type} [Group B] [Finite B]
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex B →
          ∀ Q : Sylow p Y,
            Nonempty (CentralScalarLocalCorrespondence Q))
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionSmall :
      centralIndex (ExtensionGroup T) < centralIndex B)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p)
    (a : CanonicalCoefficientGroup T) :
    (restrictedPPrimeCharacterEquivOfCentralScalarLocalIH
      ih T hT hExtensionSmall S χ).1.1.values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          (RestrictedFactorSet T S)
          (RestrictedFactorSetIsNormalized T S) a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        ((restrictedPPrimeCharacterEquivOfCentralScalarLocalIH
          ih T hT hExtensionSmall S χ).1.1.degree : ℂ) :=
  (restrictedPPrimeCharacterEquivOfCentralScalarLocalIH
    ih T hT hExtensionSmall S χ).1.2 a

end NormalSubgroupRestrictedFactorFibre
end InductiveMcKay
end McKayConjecture
