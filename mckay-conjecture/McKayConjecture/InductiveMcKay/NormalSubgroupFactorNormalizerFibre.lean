/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralScalarCentralIndexInduction
import McKayConjecture.InductiveMcKay.NormalSubgroupAssociatedFactorFibre
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer

/-!
# Normalizer fibres for canonical factor extensions

Let `T = (A, N, ζ)` be a finite character triple and let `S` be a Sylow
subgroup of `A / N`.  The canonical associated projective representation
defines a finite central extension `U` of `A / N`.  Its central extension
structure gives a canonical Sylow lift `Ŝ ≤ U`.

The associated-factor character equivalence first identifies the
prime-to-`p` irreducible characters of `A` lying over `ζ` with the
inverse-coefficient scalar fibre in `U`.  Scalar-preserving normalizer
induction then carries that fibre to the exact normalizer `N_U(Ŝ)`.
This file packages their composite.  It deliberately makes no identification
between `N_U(Ŝ)` and an inertia group downstairs; that separate group-theoretic
identification can be applied afterward.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupFactorNormalizerFibre

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open GroupTheory
open NormalSubgroupAssociatedFactorFibre

variable {A : Type} [Finite A] [Group A]
variable {p : ℕ} [Fact p.Prime]

/-! ## The canonical central data -/

/-- The normalized finite factor set defining the canonical extension. -/
abbrev CanonicalFactorSet (T : CharacterTriple A) :=
  (CanonicalAssociated T).associatedFiniteQuotientFactorSet

/-- The normalization witness for the canonical finite factor set. -/
abbrev CanonicalFactorSetIsNormalized (T : CharacterTriple A) :
    (CanonicalFactorSet T).IsNormalized :=
  (CanonicalAssociated T).associatedFiniteQuotientFactorSet_isNormalized

/-- The canonical central extension of the character-triple quotient. -/
abbrev CanonicalCentralExtension (T : CharacterTriple A) :
    CentralExtension (ExtensionGroup T) (A ⧸ T.normalSubgroup) :=
  FactorSet.CentralExtensionGroup.centralExtension
    (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T)

/-- The canonical central coefficient subgroup in the factor extension. -/
abbrev CoefficientSubgroup (T : CharacterTriple A) :
    Subgroup (ExtensionGroup T) :=
  FactorSet.CentralExtensionGroup.coefficientSubgroup
    (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T)

/-- The inverse scalar character on the canonical coefficient subgroup. -/
abbrev InverseCoefficientScalar (T : CharacterTriple A) :
    CoefficientSubgroup T →* ℂˣ :=
  FactorSet.CentralExtensionGroup.coefficientScalarCharacter
    (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T)
    (inverseRootsOfUnityCoefficientHom (CanonicalFactorExponent T))

/-- The coefficient subgroup is central in the canonical factor extension. -/
theorem coefficientSubgroup_le_center (T : CharacterTriple A) :
    CoefficientSubgroup T ≤ Subgroup.center (ExtensionGroup T) :=
  FactorSet.CentralExtensionGroup.coefficientSubgroup_le_center
    (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T)

/-- The exact Sylow subgroup of the factor extension lying over `S`. -/
abbrev LiftedSylow
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    Sylow p (ExtensionGroup T) :=
  (FactorSet.CentralExtensionGroup.centralExtension
    (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T)).sylowLift S

/-- The lifted Sylow maps onto the chosen quotient Sylow subgroup. -/
@[simp]
theorem liftedSylow_mapSurjective
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    (LiftedSylow T S).mapSurjective
        (CanonicalCentralExtension T).surjective =
      S :=
  (CanonicalCentralExtension T).sylowLift_mapSurjective S

/-- The inverse-coefficient scalar fibre in the exact normalizer of the
canonical Sylow lift. -/
abbrev NormalizerInverseCoefficientFibre
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  NormalizerCentralScalarCharacter
    (LiftedSylow T S)
    (CoefficientSubgroup T)
    (coefficientSubgroup_le_center T)
    (InverseCoefficientScalar T)

/-- A central-subgroup element, regarded in its canonical copy inside a
Sylow normalizer. -/
def centralElementInSylowNormalizer
    {G : Type} [Group G] {q : ℕ}
    (Q : Sylow q G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (z : Z) :
    centralSubgroupInSylowNormalizer Q Z :=
  ⟨⟨(z : G),
      central_le_sylowNormalizer Q Z hZcentral z.property⟩,
    z.property⟩

@[simp]
theorem centralScalarInSylowNormalizer_centralElement
    {G : Type} [Group G] {q : ℕ}
    (Q : Sylow q G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ)
    (z : Z) :
    centralScalarInSylowNormalizer
        Q Z hZcentral lambda
        (centralElementInSylowNormalizer Q Z hZcentral z) =
      lambda z :=
  rfl

/-- A coefficient element, regarded in the canonical copy of the
coefficient subgroup inside the exact lifted-Sylow normalizer. -/
def normalizerCoefficientElement
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (a : CanonicalCoefficientGroup T) :=
  centralElementInSylowNormalizer
    (LiftedSylow T S)
    (CoefficientSubgroup T)
    (coefficientSubgroup_le_center T)
    (FactorSet.CentralExtensionGroup.coefficientSubgroupElement
      (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) a)

@[simp]
theorem normalizerCoefficientElement_coe
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (a : CanonicalCoefficientGroup T) :
    (((normalizerCoefficientElement T S a :
        centralSubgroupInSylowNormalizer
          (LiftedSylow T S) (CoefficientSubgroup T)) :
      SylowNormalizer (LiftedSylow T S)) :
      ExtensionGroup T) =
        FactorSet.CentralExtensionGroup.coefficientEmbedding
          (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) a :=
  rfl

@[simp]
theorem inverseScalar_normalizerCoefficientElement
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (a : CanonicalCoefficientGroup T) :
    centralScalarInSylowNormalizer
        (LiftedSylow T S)
        (CoefficientSubgroup T)
        (coefficientSubgroup_le_center T)
        (InverseCoefficientScalar T)
        (normalizerCoefficientElement T S a) =
      (a : ℂˣ)⁻¹ := by
  rw [normalizerCoefficientElement,
    centralScalarInSylowNormalizer_centralElement]
  exact
    FactorSet.CentralExtensionGroup.coefficientScalarCharacter_coefficientSubgroupElement
      (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T)
      (inverseRootsOfUnityCoefficientHom (CanonicalFactorExponent T)) a

/-! ## Reordering the extension scalar fibre -/

/-- The pointwise inverse-coefficient condition is exactly the central
scalar condition on the named coefficient subgroup. -/
theorem hasInverseCoefficientCharacter_iff_hasCentralScalar
    (T : CharacterTriple A)
    (ψ : IrreducibleCharacter (ExtensionGroup T)) :
    (CanonicalAssociated T).HasInverseCoefficientCharacter ψ ↔
      ψ.HasCentralScalar
        (CoefficientSubgroup T)
        (InverseCoefficientScalar T) := by
  constructor
  · intro hψ z
    let a :=
      FactorSet.CentralExtensionGroup.coefficientEquiv
        (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) z
    change
      ψ.values (z : ExtensionGroup T) =
        ((((a : CanonicalCoefficientGroup T) : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
          (ψ.degree : ℂ)
    rw [← FactorSet.CentralExtensionGroup.coefficientEmbedding_coefficientEquiv
      (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) z]
    exact hψ a
  · intro hψ a
    let z :=
      FactorSet.CentralExtensionGroup.coefficientSubgroupElement
        (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) a
    have ha := hψ z
    change
      ψ.values
          (FactorSet.CentralExtensionGroup.coefficientEmbedding
            (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) a) =
        ((((a : CanonicalCoefficientGroup T) : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
          (ψ.degree : ℂ)
    simpa [z] using ha

/-- The factor-fibre and central-scalar APIs contain the same characters;
their nested subtype fields merely occur in the opposite order. -/
def inverseCoefficientCentralScalarEquiv
    (T : CharacterTriple A) :
    PPrimeInverseCoefficientFibre T p ≃
      PPrimeCentralScalarCharacter
        (ExtensionGroup T) p
        (CoefficientSubgroup T)
        (InverseCoefficientScalar T) where
  toFun ψ :=
    ⟨⟨ψ.1.1, ψ.2⟩,
      (hasInverseCoefficientCharacter_iff_hasCentralScalar T ψ.1.1).mp
        ψ.1.2⟩
  invFun ψ :=
    ⟨⟨ψ.1.1,
        (hasInverseCoefficientCharacter_iff_hasCentralScalar T ψ.1.1).mpr
          ψ.2⟩,
      ψ.1.2⟩
  left_inv ψ := by
    rfl
  right_inv ψ := by
    rfl

omit [Fact p.Prime] in
@[simp]
theorem inverseCoefficientCentralScalarEquiv_apply_character
    (T : CharacterTriple A)
    (ψ : PPrimeInverseCoefficientFibre T p) :
    (inverseCoefficientCentralScalarEquiv T ψ).1.1 = ψ.1.1 :=
  rfl

omit [Fact p.Prime] in
@[simp]
theorem inverseCoefficientCentralScalarEquiv_symm_apply_character
    (T : CharacterTriple A)
    (ψ :
      PPrimeCentralScalarCharacter
        (ExtensionGroup T) p
        (CoefficientSubgroup T)
        (InverseCoefficientScalar T)) :
    ((inverseCoefficientCentralScalarEquiv T).symm ψ).1.1 = ψ.1.1 :=
  rfl

/-! ## The extension character supplied by the factor correspondence -/

/-- The associated factor character, rearranged into the central-scalar
fibre expected by normalizer induction. -/
def factorCentralScalarCharacter
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : PPrimeCharactersOver T p) :
    PPrimeCentralScalarCharacter
      (ExtensionGroup T) p
      (CoefficientSubgroup T)
      (InverseCoefficientScalar T) :=
  inverseCoefficientCentralScalarEquiv T
    (pPrimeCharacterEquiv Fact.out T hT χ)

@[simp]
theorem factorCentralScalarCharacter_character
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : PPrimeCharactersOver T p) :
    (factorCentralScalarCharacter T hT χ).1.1 =
      (CanonicalAssociated T
        ).associatedFiniteMultiplicityExtensionCharacter
          χ.1.1 χ.1.2 :=
  rfl

/-- The exact degree relation before normalizer induction. -/
theorem factorCentralScalarCharacter_degree_mul
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : PPrimeCharactersOver T p) :
    (factorCentralScalarCharacter T hT χ).1.1.degree *
        T.character.degree =
      χ.1.1.degree :=
  pPrimeCharacterEquiv_degree_mul Fact.out T hT χ

/-- The extension character has the prescribed inverse scalar on the
coefficient subgroup. -/
theorem factorCentralScalarCharacter_hasCentralScalar
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (χ : PPrimeCharactersOver T p) :
    (factorCentralScalarCharacter T hT χ).1.1.HasCentralScalar
      (CoefficientSubgroup T)
      (InverseCoefficientScalar T) :=
  (factorCentralScalarCharacter T hT χ).2

/-! ## Bounded normalizer induction -/

/-- The scalar-preserving normalizer correspondence for the canonical
factor extension, assuming local data below `bound`. -/
def extensionNormalizerEquivOfCentralIndexBound
    (bound : ℕ)
    (localData : CentralIndexBoundedLocalProvider p bound)
    (T : CharacterTriple A)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  centralScalarCorrespondenceOfCentralIndexBound
    bound localData
    (ExtensionGroup T) hExtensionBound
    (LiftedSylow T S)
    (CoefficientSubgroup T)
    (coefficientSubgroup_le_center T)
    (InverseCoefficientScalar T)

/-- Prime-to-`p` ambient characters over `T.character` correspond to the
inverse-coefficient scalar fibre in the exact normalizer of the canonical
Sylow lift. -/
def pPrimeCharacterEquivOfCentralIndexBound
    (bound : ℕ)
    (localData : CentralIndexBoundedLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  (pPrimeCharacterEquiv Fact.out T hT).trans
    ((inverseCoefficientCentralScalarEquiv T).trans
      (extensionNormalizerEquivOfCentralIndexBound
        bound localData T hExtensionBound S))

@[simp]
theorem pPrimeCharacterEquivOfCentralIndexBound_apply_coe
    (bound : ℕ)
    (localData : CentralIndexBoundedLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquivOfCentralIndexBound
      bound localData T hT hExtensionBound S χ).1 =
        (extensionNormalizerEquivOfCentralIndexBound
          bound localData T hExtensionBound S
          (factorCentralScalarCharacter T hT χ)).1 :=
  rfl

/-- The normalizer output remains a prime-to-`p` irreducible character. -/
theorem pPrimeCharacterEquivOfCentralIndexBound_isPPrimeDegree
    (bound : ℕ)
    (localData : CentralIndexBoundedLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquivOfCentralIndexBound
      bound localData T hT hExtensionBound S χ).1.1.IsPPrimeDegree p :=
  (pPrimeCharacterEquivOfCentralIndexBound
    bound localData T hT hExtensionBound S χ).1.2

/-- The normalizer output has the transported inverse-coefficient scalar on
the canonical copy of the coefficient subgroup. -/
theorem pPrimeCharacterEquivOfCentralIndexBound_hasCentralScalar
    (bound : ℕ)
    (localData : CentralIndexBoundedLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquivOfCentralIndexBound
      bound localData T hT hExtensionBound S χ).1.1.HasCentralScalar
        (centralSubgroupInSylowNormalizer
          (LiftedSylow T S) (CoefficientSubgroup T))
        (centralScalarInSylowNormalizer
          (LiftedSylow T S)
          (CoefficientSubgroup T)
          (coefficientSubgroup_le_center T)
          (InverseCoefficientScalar T)) :=
  (pPrimeCharacterEquivOfCentralIndexBound
    bound localData T hT hExtensionBound S χ).2

/-- Exact inverse-coefficient value formula in the lifted-Sylow normalizer. -/
theorem pPrimeCharacterEquivOfCentralIndexBound_coefficient_value
    (bound : ℕ)
    (localData : CentralIndexBoundedLocalProvider p bound)
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionBound :
      centralIndex (ExtensionGroup T) < bound)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p)
    (a : CanonicalCoefficientGroup T) :
    (pPrimeCharacterEquivOfCentralIndexBound
      bound localData T hT hExtensionBound S χ).1.1.values
        (normalizerCoefficientElement T S a :
          SylowNormalizer (LiftedSylow T S)) =
      ((((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        ((pPrimeCharacterEquivOfCentralIndexBound
          bound localData T hT hExtensionBound S χ).1.1.degree : ℂ)) := by
  have h :=
    (pPrimeCharacterEquivOfCentralIndexBound_hasCentralScalar
      bound localData T hT hExtensionBound S χ)
      (normalizerCoefficientElement T S a)
  rw [inverseScalar_normalizerCoefficientElement] at h
  exact h

/-! ## Specialization to a central-index induction hypothesis -/

/-- The same normalizer-fibre equivalence obtained directly from a
central-index induction hypothesis at an ambient group `B`. -/
def pPrimeCharacterEquivOfCentralIndexIH
    {B : Type} [Group B] [Finite B]
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex B →
          ∀ Q : Sylow p Y,
            Nonempty (LocalInductiveMcKayData Q))
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionSmall :
      centralIndex (ExtensionGroup T) < centralIndex B)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  pPrimeCharacterEquivOfCentralIndexBound
    (centralIndex B)
    (fun Y _ _ hY Q ↦ Classical.choice (ih Y hY Q))
    T hT hExtensionSmall S

@[simp]
theorem pPrimeCharacterEquivOfCentralIndexIH_apply_coe
    {B : Type} [Group B] [Finite B]
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex B →
          ∀ Q : Sylow p Y,
            Nonempty (LocalInductiveMcKayData Q))
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionSmall :
      centralIndex (ExtensionGroup T) < centralIndex B)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p) :
    (pPrimeCharacterEquivOfCentralIndexIH
      ih T hT hExtensionSmall S χ).1 =
        (centralScalarCorrespondenceOfCentralIndexIH
          ih (ExtensionGroup T) hExtensionSmall
          (LiftedSylow T S)
          (CoefficientSubgroup T)
          (coefficientSubgroup_le_center T)
          (InverseCoefficientScalar T)
          (factorCentralScalarCharacter T hT χ)).1 :=
  rfl

/-- Exact inverse-coefficient value formula for the induction-hypothesis
specialization. -/
theorem pPrimeCharacterEquivOfCentralIndexIH_coefficient_value
    {B : Type} [Group B] [Finite B]
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex B →
          ∀ Q : Sylow p Y,
            Nonempty (LocalInductiveMcKayData Q))
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hExtensionSmall :
      centralIndex (ExtensionGroup T) < centralIndex B)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : PPrimeCharactersOver T p)
    (a : CanonicalCoefficientGroup T) :
    (pPrimeCharacterEquivOfCentralIndexIH
      ih T hT hExtensionSmall S χ).1.1.values
        (normalizerCoefficientElement T S a :
          SylowNormalizer (LiftedSylow T S)) =
      ((((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        ((pPrimeCharacterEquivOfCentralIndexIH
          ih T hT hExtensionSmall S χ).1.1.degree : ℂ)) :=
  pPrimeCharacterEquivOfCentralIndexBound_coefficient_value
    (centralIndex B)
    (fun Y _ _ hY Q ↦ Classical.choice (ih Y hY Q))
    T hT hExtensionSmall S χ a

/-- In the common case where `T.normalSubgroup` strictly contains the
ambient center, the canonical extension automatically lies below the
central index of `A`. -/
def pPrimeCharacterEquivOfAmbientCentralIndexIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex A →
          ∀ Q : Sylow p Y,
            Nonempty (LocalInductiveMcKayData Q))
    (T : CharacterTriple A)
    (hT : T.character.IsPPrimeDegree p)
    (hcenter : Subgroup.center A < T.normalSubgroup)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  pPrimeCharacterEquivOfCentralIndexIH
    ih T hT
    (canonicalFiniteFactorCentralExtension_centralIndex_lt T hcenter)
    S

end NormalSubgroupFactorNormalizerFibre
end InductiveMcKay
end McKayConjecture
