/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionSolvable
import McKayConjecture.InductiveMcKay.NormalSubgroupRestrictedFactorFibre
import McKayConjecture.InductiveMcKay.SolvableCentralScalarLocalCentralIndexInduction

/-!
# Factor fibres in a solvable central-index induction

The canonical factor extension of a character triple over a solvable group
is solvable: its base is a quotient of the ambient group and its kernel is
the abelian coefficient group.  Therefore the scalar normalizer recursion
for that extension only requires local correspondences for solvable groups.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

namespace NormalSubgroupFactorNormalizerFibre

open CharacterTriple
open GroupTheory
open NormalSubgroupAssociatedFactorFibre

variable {A : Type} [Finite A] [Group A] [Group.IsSolvable A]
variable {p : ℕ} [Fact p.Prime]

/-- Scalar-preserving normalizer correspondence for the canonical factor
extension, using only a bounded provider on solvable groups. -/
def extensionNormalizerEquivOfSolvableCentralScalarLocalBound
    (bound : ℕ)
    (localData :
      SolvableCentralIndexBoundedCentralScalarLocalProvider p bound)
    (T : CharacterTriple A)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  centralScalarCorrespondenceOfSolvableCentralScalarLocalCentralIndexBound
    bound localData
    (ExtensionGroup T) hExtensionBound
    (LiftedSylow T S)
    (CoefficientSubgroup T)
    (coefficientSubgroup_le_center T)
    (InverseCoefficientScalar T)

/-- Prime-to-`p` characters over a solvable character triple correspond to
the inverse-coefficient scalar fibre in the lifted-Sylow normalizer. -/
def pPrimeCharacterEquivOfSolvableCentralScalarLocalBound
    (bound : ℕ)
    (localData :
      SolvableCentralIndexBoundedCentralScalarLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  (pPrimeCharacterEquiv Fact.out T hT).trans
    ((inverseCoefficientCentralScalarEquiv T).trans
      (extensionNormalizerEquivOfSolvableCentralScalarLocalBound
        bound localData T hExtensionBound S))

/-- Specialization to the solvable scalar-local central-index induction
hypothesis at an ambient solvable group. -/
def pPrimeCharacterEquivOfSolvableCentralScalarLocalIH
    {B : Type} [Group B] [Finite B] [Group.IsSolvable B]
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y] [Group.IsSolvable Y],
        centralIndex Y < centralIndex B →
          ∀ Q : Sylow p Y,
            Nonempty (CentralScalarLocalCorrespondence Q))
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionSmall :
      centralIndex (ExtensionGroup T) < centralIndex B)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  pPrimeCharacterEquivOfSolvableCentralScalarLocalBound
    (centralIndex B)
    (fun Y _ _ _ hY Q ↦ Classical.choice (ih Y hY Q))
    T hT hExtensionSmall S

end NormalSubgroupFactorNormalizerFibre

namespace NormalSubgroupRestrictedFactorFibre

open CharacterTriple
open GroupTheory
open NormalSubgroupAssociatedFactorFibre
open NormalSubgroupFactorNormalizerFibre

variable {A : Type} [Finite A] [Group A] [Group.IsSolvable A]
variable {p : ℕ} [Fact p.Prime]

/-- Source characters over a solvable triple correspond to the fixed
restricted factor fibre using only scalar-local data on smaller solvable
groups. -/
def restrictedPPrimeCharacterEquivOfSolvableCentralScalarLocalIH
    {B : Type} [Group B] [Finite B] [Group.IsSolvable B]
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y] [Group.IsSolvable Y],
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
  (pPrimeCharacterEquivOfSolvableCentralScalarLocalIH
    ih T hT hExtensionSmall S).trans
      (normalizerFibreEquivRestrictedInverseCoefficientFibre T S)

end NormalSubgroupRestrictedFactorFibre
end InductiveMcKay
end McKayConjecture
