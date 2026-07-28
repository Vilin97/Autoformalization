/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralScalarLocalCentralIndexInduction
import McKayConjecture.InductiveMcKay.NormalSubgroupFactorNormalizerFibre

/-!
# Factor-normalizer fibres from the scalar numerical induction hypothesis

The canonical factor-extension construction only needs preservation of the
inverse coefficient scalar.  This file restates the normalizer-fibre
equivalence using `CentralScalarLocalCorrespondence` on smaller
central-index groups, avoiding the unnecessarily strong requirement of full
inductive-McKay data.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupFactorNormalizerFibre

open CharacterTriple
open GroupTheory
open NormalSubgroupAssociatedFactorFibre

variable {A : Type} [Finite A] [Group A]
variable {p : ℕ} [Fact p.Prime]

/-- Scalar-preserving normalizer correspondence for the canonical factor
extension from a bounded scalar numerical provider. -/
def extensionNormalizerEquivOfCentralScalarLocalBound
    (bound : ℕ)
    (localData :
      CentralIndexBoundedCentralScalarLocalProvider p bound)
    (T : CharacterTriple A)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  centralScalarCorrespondenceOfCentralScalarLocalCentralIndexBound
    bound localData
    (ExtensionGroup T) hExtensionBound
    (LiftedSylow T S)
    (CoefficientSubgroup T)
    (coefficientSubgroup_le_center T)
    (InverseCoefficientScalar T)

/-- Prime-to-`p` characters over `T.character` correspond to the
inverse-coefficient scalar fibre in the exact lifted-Sylow normalizer,
assuming only the bounded scalar numerical condition. -/
def pPrimeCharacterEquivOfCentralScalarLocalBound
    (bound : ℕ)
    (localData :
      CentralIndexBoundedCentralScalarLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  (pPrimeCharacterEquiv Fact.out T hT).trans
    ((inverseCoefficientCentralScalarEquiv T).trans
      (extensionNormalizerEquivOfCentralScalarLocalBound
        bound localData T hExtensionBound S))

@[simp]
theorem pPrimeCharacterEquivOfCentralScalarLocalBound_apply_coe
    (bound : ℕ)
    (localData :
      CentralIndexBoundedCentralScalarLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquivOfCentralScalarLocalBound
      bound localData T hT hExtensionBound S χ).1 =
        (extensionNormalizerEquivOfCentralScalarLocalBound
          bound localData T hExtensionBound S
          (factorCentralScalarCharacter T hT χ)).1 :=
  rfl

/-- The output has the transported inverse-coefficient scalar. -/
theorem pPrimeCharacterEquivOfCentralScalarLocalBound_hasCentralScalar
    (bound : ℕ)
    (localData :
      CentralIndexBoundedCentralScalarLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquivOfCentralScalarLocalBound
      bound localData T hT hExtensionBound S χ).1.1.HasCentralScalar
        (centralSubgroupInSylowNormalizer
          (LiftedSylow T S) (CoefficientSubgroup T))
        (centralScalarInSylowNormalizer
          (LiftedSylow T S)
          (CoefficientSubgroup T)
          (coefficientSubgroup_le_center T)
          (InverseCoefficientScalar T)) :=
  (pPrimeCharacterEquivOfCentralScalarLocalBound
    bound localData T hT hExtensionBound S χ).2

/-- Exact inverse-coefficient value formula in the lifted-Sylow normalizer. -/
theorem pPrimeCharacterEquivOfCentralScalarLocalBound_coefficient_value
    (bound : ℕ)
    (localData :
      CentralIndexBoundedCentralScalarLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p)
    (a : CanonicalCoefficientGroup T) :
    (pPrimeCharacterEquivOfCentralScalarLocalBound
      bound localData T hT hExtensionBound S χ).1.1.values
        (normalizerCoefficientElement T S a :
          SylowNormalizer (LiftedSylow T S)) =
      ((((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        ((pPrimeCharacterEquivOfCentralScalarLocalBound
          bound localData T hT hExtensionBound S χ).1.1.degree : ℂ)) := by
  have h :=
    (pPrimeCharacterEquivOfCentralScalarLocalBound_hasCentralScalar
      bound localData T hT hExtensionBound S χ)
      (normalizerCoefficientElement T S a)
  rw [inverseScalar_normalizerCoefficientElement] at h
  exact h

/-- Specialization to a scalar numerical central-index induction
hypothesis at an ambient group `B`. -/
def pPrimeCharacterEquivOfCentralScalarLocalIH
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
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  pPrimeCharacterEquivOfCentralScalarLocalBound
    (centralIndex B)
    (fun Y _ _ hY Q ↦ Classical.choice (ih Y hY Q))
    T hT hExtensionSmall S

/-- Exact inverse-coefficient formula for the induction-hypothesis
specialization. -/
theorem pPrimeCharacterEquivOfCentralScalarLocalIH_coefficient_value
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
    (pPrimeCharacterEquivOfCentralScalarLocalIH
      ih T hT hExtensionSmall S χ).1.1.values
        (normalizerCoefficientElement T S a :
          SylowNormalizer (LiftedSylow T S)) =
      ((((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        ((pPrimeCharacterEquivOfCentralScalarLocalIH
          ih T hT hExtensionSmall S χ).1.1.degree : ℂ)) :=
  pPrimeCharacterEquivOfCentralScalarLocalBound_coefficient_value
    (centralIndex B)
    (fun Y _ _ hY Q ↦ Classical.choice (ih Y hY Q))
    T hT hExtensionSmall S χ a

end NormalSubgroupFactorNormalizerFibre
end InductiveMcKay
end McKayConjecture
