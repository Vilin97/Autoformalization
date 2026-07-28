/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorCharacterEquiv

/-!
# Canonical associated-factor character fibres

For an arbitrary finite character triple `T = (A, N, ζ)`, this file
specializes the finite-factor character equivalence to the canonical
associated projective representation supplied by
`AssociatedGeneralExistence`.

The resulting package identifies the `p'` irreducible characters of `A`
lying over `ζ` with the `p'` inverse-coefficient scalar fibre of the
canonical finite factor extension of `A / N`.  It is deliberately generic in
`T`, so it can be applied directly to the active-orbit inertia triples in the
normal-subgroup reduction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupAssociatedFactorFibre

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation

variable {A : Type} [Finite A] [Group A]

/-- The canonical projective representation attached to a character
triple. -/
abbrev CanonicalProjective (T : CharacterTriple A) :
    ProjectiveRepresentation ℂ A T.character.realization :=
  AssociatedGeneralExistence.projectiveRepresentation T

/-- The canonical associated-projective-representation witness. -/
abbrev CanonicalAssociated (T : CharacterTriple A) :
    AssociatedProjectiveRepresentation T T.character.realization
      (CanonicalProjective T) :=
  AssociatedGeneralExistence.associated T

/-- The canonical finite-normalized associated projective
representation. -/
abbrev CanonicalFiniteProjective (T : CharacterTriple A) :
    ProjectiveRepresentation ℂ A T.character.realization :=
  (CanonicalAssociated T).associatedFiniteFactorProjective

/-- The exponent used for the canonical finite roots-of-unity factor. -/
abbrev CanonicalFactorExponent (T : CharacterTriple A) : ℕ :=
  associatedFactorExponent T T.character.realization

/-- The coefficient group of the canonical finite factor extension. -/
abbrev CanonicalCoefficientGroup (T : CharacterTriple A) :=
  rootsOfUnity (CanonicalFactorExponent T) ℂ

/-- The canonical finite central extension of `A / T.normalSubgroup`. -/
abbrev ExtensionGroup (T : CharacterTriple A) :=
  FactorSet.CentralExtensionGroup
    (CanonicalAssociated T).associatedFiniteQuotientFactorSet
    (CanonicalAssociated T
      ).associatedFiniteQuotientFactorSet_isNormalized

/-- Irreducible ambient characters lying over the character of `T`. -/
abbrev CharactersOver (T : CharacterTriple A) :=
  (CanonicalAssociated T).AssociatedCharactersOver

/-- The inverse-coefficient scalar fibre in the canonical finite factor
extension. -/
abbrev InverseCoefficientFibre (T : CharacterTriple A) :=
  (CanonicalAssociated T).InverseCoefficientCharacters

/-- Prime-to-`p` ambient characters lying over the character of `T`. -/
abbrev PPrimeCharactersOver (T : CharacterTriple A) (p : ℕ) :=
  (CanonicalAssociated T).AssociatedPPrimeCharactersOver p

/-- The prime-to-`p` inverse-coefficient scalar fibre in the canonical
finite factor extension. -/
abbrev PPrimeInverseCoefficientFibre
    (T : CharacterTriple A) (p : ℕ) :=
  (CanonicalAssociated T).InverseCoefficientPPrimeCharacters p

/-- The canonical equivalence before restricting character degrees. -/
def characterEquiv (T : CharacterTriple A) :
    CharactersOver T ≃ InverseCoefficientFibre T :=
  (CanonicalAssociated T).associatedFiniteFactorCharacterEquiv

@[simp]
theorem characterEquiv_apply_character
    (T : CharacterTriple A) (χ : CharactersOver T) :
    ((characterEquiv T χ : InverseCoefficientFibre T).1) =
      (CanonicalAssociated T
        ).associatedFiniteMultiplicityExtensionCharacter χ.1 χ.2 :=
  rfl

@[simp]
theorem characterEquiv_symm_apply_character
    (T : CharacterTriple A) (ψ : InverseCoefficientFibre T) :
    (((characterEquiv T).symm ψ : CharactersOver T).1) =
      (CanonicalAssociated T
        ).inverseCoefficientTensorCharacter ψ.1 ψ.2 :=
  rfl

/-- Exact inverse-coefficient value law for the canonical forward
correspondence. -/
theorem characterEquiv_coefficient_value
    (T : CharacterTriple A) (χ : CharactersOver T)
    (a : CanonicalCoefficientGroup T) :
    (characterEquiv T χ).1.values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          (CanonicalAssociated T).associatedFiniteQuotientFactorSet
          (CanonicalAssociated T
            ).associatedFiniteQuotientFactorSet_isNormalized a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        ((characterEquiv T χ).1.degree : ℂ) :=
  (characterEquiv T χ).2 a

/-- Exact forward degree law. -/
theorem characterEquiv_degree_mul
    (T : CharacterTriple A) (χ : CharactersOver T) :
    (characterEquiv T χ).1.degree * T.character.degree =
      χ.1.degree :=
  (CanonicalAssociated T
    ).associatedFiniteMultiplicityExtensionCharacter_degree_mul
      χ.1 χ.2

/-- Exact inverse degree law. -/
theorem characterEquiv_symm_degree
    (T : CharacterTriple A) (ψ : InverseCoefficientFibre T) :
    ((characterEquiv T).symm ψ).1.degree =
      T.character.degree * ψ.1.degree :=
  (CanonicalAssociated T
    ).inverseCoefficientTensorCharacter_degree ψ.1 ψ.2

/-- Under the prime-to-`p` hypothesis on `T.character`, the canonical
forward construction preserves and reflects prime-to-`p` degree. -/
theorem characterEquiv_isPPrimeDegree_iff
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : CharactersOver T) :
    (characterEquiv T χ).1.IsPPrimeDegree p ↔
      χ.1.IsPPrimeDegree p :=
  (CanonicalAssociated T
    ).associatedFiniteMultiplicityExtensionCharacter_isPPrime_iff
      hp χ.1 χ.2 hT

/-- The canonical associated-factor equivalence on prime-to-`p`
characters. -/
def pPrimeCharacterEquiv
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p) :
    PPrimeCharactersOver T p ≃
      PPrimeInverseCoefficientFibre T p :=
  (CanonicalAssociated T
    ).associatedFiniteFactorPPrimeCharacterEquiv hp hT

/-- Version using the ambient `Fact p.Prime` instance customary in the
inductive McKay development. -/
def pPrimeCharacterEquivOfFact
    (p : ℕ) [Fact p.Prime]
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p) :
    PPrimeCharactersOver T p ≃
      PPrimeInverseCoefficientFibre T p :=
  pPrimeCharacterEquiv Fact.out T hT

@[simp]
theorem pPrimeCharacterEquiv_apply_fibre
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquiv hp T hT χ).1 =
      characterEquiv T χ.1 :=
  rfl

@[simp]
theorem pPrimeCharacterEquiv_apply_character
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquiv hp T hT χ).1.1 =
      (CanonicalAssociated T
        ).associatedFiniteMultiplicityExtensionCharacter
          χ.1.1 χ.1.2 :=
  rfl

@[simp]
theorem pPrimeCharacterEquiv_symm_apply_fibre
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (ψ : PPrimeInverseCoefficientFibre T p) :
    ((pPrimeCharacterEquiv hp T hT).symm ψ).1 =
      (characterEquiv T).symm ψ.1 :=
  rfl

@[simp]
theorem pPrimeCharacterEquiv_symm_apply_character
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (ψ : PPrimeInverseCoefficientFibre T p) :
    ((pPrimeCharacterEquiv hp T hT).symm ψ).1.1 =
      (CanonicalAssociated T
        ).inverseCoefficientTensorCharacter ψ.1.1 ψ.1.2 :=
  rfl

/-- Exact degree law on the forward prime-to-`p` fibre. -/
theorem pPrimeCharacterEquiv_degree_mul
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquiv hp T hT χ).1.1.degree *
        T.character.degree =
      χ.1.1.degree :=
  characterEquiv_degree_mul T χ.1

/-- Exact degree law on the inverse prime-to-`p` fibre. -/
theorem pPrimeCharacterEquiv_symm_degree
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (ψ : PPrimeInverseCoefficientFibre T p) :
    ((pPrimeCharacterEquiv hp T hT).symm ψ).1.1.degree =
      T.character.degree * ψ.1.1.degree :=
  characterEquiv_symm_degree T ψ.1

/-- The image of the prime-to-`p` equivalence carries the exact prescribed
inverse scalar on every coefficient element. -/
theorem pPrimeCharacterEquiv_coefficient_value
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : PPrimeCharactersOver T p)
    (a : CanonicalCoefficientGroup T) :
    (pPrimeCharacterEquiv hp T hT χ).1.1.values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          (CanonicalAssociated T).associatedFiniteQuotientFactorSet
          (CanonicalAssociated T
            ).associatedFiniteQuotientFactorSet_isNormalized a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        ((pPrimeCharacterEquiv hp T hT χ).1.1.degree : ℂ) :=
  characterEquiv_coefficient_value T χ.1 a

/-- The forward image is prime to `p`. -/
theorem pPrimeCharacterEquiv_apply_isPPrimeDegree
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquiv hp T hT χ).1.1.IsPPrimeDegree p :=
  (pPrimeCharacterEquiv hp T hT χ).2

/-- The inverse image is prime to `p`. -/
theorem pPrimeCharacterEquiv_symm_apply_isPPrimeDegree
    {p : ℕ} (hp : p.Prime)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (ψ : PPrimeInverseCoefficientFibre T p) :
    ((pPrimeCharacterEquiv hp T hT).symm ψ).1.1.IsPPrimeDegree p :=
  ((pPrimeCharacterEquiv hp T hT).symm ψ).2

end NormalSubgroupAssociatedFactorFibre
end InductiveMcKay
end McKayConjecture
