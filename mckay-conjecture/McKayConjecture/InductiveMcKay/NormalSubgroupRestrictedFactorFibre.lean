/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorNormalizerRestriction
import McKayConjecture.InductiveMcKay.NormalSubgroupFactorNormalizerFibre

/-!
# Restricted factor fibres after normalizer induction

For a finite character triple `T = (A, N, ζ)` and a Sylow subgroup `S` of
`A / N`, the canonical finite factor extension has a canonical Sylow lift.
The normalizer of that lift is concretely isomorphic to the factor extension
obtained by restricting the fixed normalized associated lift to the full
preimage of `N_{A/N}(S)`.

This file transports the inverse-coefficient scalar fibre through that
concrete equivalence.  The target deliberately uses the fixed pulled-back
factor set, rather than rerunning determinant normalization on the restricted
triple and making a second set of representative choices.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupRestrictedFactorFibre

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open GroupTheory
open NormalSubgroupAssociatedFactorFibre
open NormalSubgroupFactorNormalizerFibre

variable {A : Type} [Finite A] [Group A]
variable {p : ℕ} [Fact p.Prime]

/-! ## The restricted triple and its fixed finite factor extension -/

/-- The full preimage in `A` of the normalizer of `S` in `A / N`. -/
abbrev RestrictedAmbientGroup
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  quotientSylowNormalizerPreimage T S

/-- The restriction of `T` to the full quotient-normalizer preimage. -/
abbrev RestrictedTriple
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    CharacterTriple (RestrictedAmbientGroup T S) :=
  quotientSylowNormalizerRestrictionTriple T S

/-- The fixed finite-normalized associated lift, restricted literally to the
quotient-normalizer preimage. -/
abbrev RestrictedAssociated
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  (CanonicalAssociated T).associatedFiniteFactorNormalizerRestriction S

/-- The fixed finite factor set on the quotient of the restricted triple. -/
abbrev RestrictedFactorSet
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  FactorSet.CentralExtensionGroup.sylowNormalizerFactorSet
    (CanonicalFactorSet T) S
    (quotientSylowNormalizerEquiv T S)

/-- Normalization of the fixed restricted factor set. -/
abbrev RestrictedFactorSetIsNormalized
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    (RestrictedFactorSet T S).IsNormalized :=
  FactorSet.CentralExtensionGroup.sylowNormalizerFactorSet_isNormalized
    (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T)
    S (quotientSylowNormalizerEquiv T S)

/-- The concrete factor extension of the fixed restricted normalization. -/
abbrev RestrictedExtensionGroup
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  FactorSet.CentralExtensionGroup
    (RestrictedFactorSet T S)
    (RestrictedFactorSetIsNormalized T S)

/-- The Sylow lift in the source of the concrete restriction equivalence. -/
abbrev SourceLiftedSylow
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  LiftedSylow T S

/-- The concrete equivalence from the exact lifted-Sylow normalizer to the
fixed factor extension of the restricted triple. -/
def normalizerEquivRestrictedExtension
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    SylowNormalizer (LiftedSylow T S) ≃*
      RestrictedExtensionGroup T S where
  toFun x :=
    FactorSet.CentralExtensionGroup.mk
      (RestrictedFactorSet T S)
      (RestrictedFactorSetIsNormalized T S)
      ((quotientSylowNormalizerEquiv T S).symm
        ⟨FactorSet.CentralExtensionGroup.base
            (CanonicalFactorSet T)
            (CanonicalFactorSetIsNormalized T)
            (x : ExtensionGroup T),
          (CanonicalCentralExtension T
            ).projection_mem_sylowNormalizer S x⟩)
      (FactorSet.CentralExtensionGroup.coefficient
        (CanonicalFactorSet T)
        (CanonicalFactorSetIsNormalized T)
        (x : ExtensionGroup T))
  invFun y :=
    ⟨FactorSet.CentralExtensionGroup.mk
        (CanonicalFactorSet T)
        (CanonicalFactorSetIsNormalized T)
        (((quotientSylowNormalizerEquiv T S)
          (FactorSet.CentralExtensionGroup.base
            (RestrictedFactorSet T S)
            (RestrictedFactorSetIsNormalized T S) y) :
            Subgroup.normalizer
              (S : Set (A ⧸ T.normalSubgroup))) :
          A ⧸ T.normalSubgroup)
        (FactorSet.CentralExtensionGroup.coefficient
          (RestrictedFactorSet T S)
          (RestrictedFactorSetIsNormalized T S) y),
      by
        apply
          GroupTheory.Sylow.mem_normalizer_of_mapSurjective_mem_normalizer_of_ker_le_center
            (CanonicalCentralExtension T).surjective
            (CanonicalCentralExtension T).ker_le_center
            (LiftedSylow T S)
        rw [liftedSylow_mapSurjective T S]
        exact
          ((quotientSylowNormalizerEquiv T S)
            (FactorSet.CentralExtensionGroup.base
              (RestrictedFactorSet T S)
              (RestrictedFactorSetIsNormalized T S) y)).property⟩
  left_inv x := by
    apply Subtype.ext
    apply
      FactorSet.CentralExtensionGroup.ext
        (CanonicalFactorSet T)
        (CanonicalFactorSetIsNormalized T)
    · exact congrArg Subtype.val
        ((quotientSylowNormalizerEquiv T S).apply_symm_apply
          ⟨FactorSet.CentralExtensionGroup.base
              (CanonicalFactorSet T)
              (CanonicalFactorSetIsNormalized T)
              (x : ExtensionGroup T),
            (CanonicalCentralExtension T
              ).projection_mem_sylowNormalizer S x⟩)
    · rfl
  right_inv y := by
    apply FactorSet.CentralExtensionGroup.ext
    · exact
        (quotientSylowNormalizerEquiv T S).symm_apply_apply
          (FactorSet.CentralExtensionGroup.base
            (RestrictedFactorSet T S)
            (RestrictedFactorSetIsNormalized T S) y)
    · rfl
  map_mul' x y := by
    apply FactorSet.CentralExtensionGroup.ext
    · apply (quotientSylowNormalizerEquiv T S).injective
      simp only [FactorSet.CentralExtensionGroup.base_mk,
        FactorSet.CentralExtensionGroup.base_mul, map_mul,
        MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    · change
        (CanonicalFactorSet T)
              (FactorSet.CentralExtensionGroup.base
                (CanonicalFactorSet T)
                (CanonicalFactorSetIsNormalized T)
                (x : ExtensionGroup T))
              (FactorSet.CentralExtensionGroup.base
                (CanonicalFactorSet T)
                (CanonicalFactorSetIsNormalized T)
                (y : ExtensionGroup T)) *
              FactorSet.CentralExtensionGroup.coefficient
                (CanonicalFactorSet T)
                (CanonicalFactorSetIsNormalized T)
                (x : ExtensionGroup T) *
            FactorSet.CentralExtensionGroup.coefficient
              (CanonicalFactorSet T)
              (CanonicalFactorSetIsNormalized T)
              (y : ExtensionGroup T) =
          (CanonicalFactorSet T)
              ((quotientSylowNormalizerEquiv T S)
                ((quotientSylowNormalizerEquiv T S).symm
                  ⟨FactorSet.CentralExtensionGroup.base
                      (CanonicalFactorSet T)
                      (CanonicalFactorSetIsNormalized T)
                      (x : ExtensionGroup T),
                    (CanonicalCentralExtension T
                      ).projection_mem_sylowNormalizer S x⟩)).1
              ((quotientSylowNormalizerEquiv T S)
                ((quotientSylowNormalizerEquiv T S).symm
                  ⟨FactorSet.CentralExtensionGroup.base
                      (CanonicalFactorSet T)
                      (CanonicalFactorSetIsNormalized T)
                      (y : ExtensionGroup T),
                    (CanonicalCentralExtension T
                      ).projection_mem_sylowNormalizer S y⟩)).1 *
              FactorSet.CentralExtensionGroup.coefficient
                (CanonicalFactorSet T)
                (CanonicalFactorSetIsNormalized T)
                (x : ExtensionGroup T) *
            FactorSet.CentralExtensionGroup.coefficient
              (CanonicalFactorSet T)
              (CanonicalFactorSetIsNormalized T)
              (y : ExtensionGroup T)
      rw [(quotientSylowNormalizerEquiv T S).apply_symm_apply,
        (quotientSylowNormalizerEquiv T S).apply_symm_apply]

/-- The concrete normalizer equivalence fixes the coefficient coordinate. -/
@[simp]
theorem normalizerEquivRestrictedExtension_coefficientEmbedding
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (a : CanonicalCoefficientGroup T) :
    normalizerEquivRestrictedExtension T S
        ((normalizerCoefficientElement T S a :
            centralSubgroupInSylowNormalizer
              (LiftedSylow T S) (CoefficientSubgroup T)) :
          SylowNormalizer (LiftedSylow T S)) =
      FactorSet.CentralExtensionGroup.coefficientEmbedding
        (RestrictedFactorSet T S)
        (RestrictedFactorSetIsNormalized T S) a := by
  apply FactorSet.CentralExtensionGroup.ext
  · change
      (quotientSylowNormalizerEquiv T S).symm
          ⟨1, (CanonicalCentralExtension T
            ).projection_mem_sylowNormalizer S
              ((normalizerCoefficientElement T S a :
                  centralSubgroupInSylowNormalizer
                    (LiftedSylow T S) (CoefficientSubgroup T)) :
                SylowNormalizer (LiftedSylow T S))⟩ =
        1
    rw [← (quotientSylowNormalizerEquiv T S).symm.map_one]
    congr 1
  · rfl

/-- Character-level inverse-coefficient condition in the fixed restricted
factor extension. -/
def HasRestrictedInverseCoefficientCharacter
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (ψ : IrreducibleCharacter (RestrictedExtensionGroup T S)) :
    Prop :=
  ∀ a : CanonicalCoefficientGroup T,
    ψ.values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          (RestrictedFactorSet T S)
          (RestrictedFactorSetIsNormalized T S) a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) * (ψ.degree : ℂ)

/-- Inverse-coefficient irreducible characters of the fixed restricted
factor extension. -/
abbrev RestrictedInverseCoefficientCharacters
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  {ψ : IrreducibleCharacter (RestrictedExtensionGroup T S) //
    HasRestrictedInverseCoefficientCharacter T S ψ}

/-- The prime-to-`p` inverse-coefficient fibre of the fixed restricted
factor extension. -/
abbrev RestrictedPPrimeInverseCoefficientFibre
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  {ψ : RestrictedInverseCoefficientCharacters T S //
    ψ.1.IsPPrimeDegree p}

/-! ## Compatibility with the normalizer scalar fibre -/

/-- Transport prime-to-`p` characters from the exact normalizer to the
fixed restricted factor extension. -/
def normalizerPPrimeCharacterEquivRestrictedExtension
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    PPrimeIrreducibleCharacter
        (SylowNormalizer (LiftedSylow T S)) p ≃
      PPrimeIrreducibleCharacter
        (RestrictedExtensionGroup T S) p :=
  (IrreducibleCharacter.pPrimeComapEquiv p
    (normalizerEquivRestrictedExtension T S)).symm

/-- Transport a character in the normalizer scalar fibre to the
inverse-coefficient fibre of the fixed restricted extension. -/
def normalizerToRestrictedFibre
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : NormalizerInverseCoefficientFibre T S) :
    RestrictedPPrimeInverseCoefficientFibre T S := by
  let χ' :=
    normalizerPPrimeCharacterEquivRestrictedExtension T S χ.1
  refine ⟨⟨χ'.1, ?_⟩, χ'.2⟩
  intro a
  let z :=
    normalizerCoefficientElement T S a
  have ha := χ.2 z
  have hscalar :
      centralScalarInSylowNormalizer
          (LiftedSylow T S)
          (CoefficientSubgroup T)
          (coefficientSubgroup_le_center T)
          (InverseCoefficientScalar T) z =
        (a : ℂˣ)⁻¹ := by
    change
      (InverseCoefficientScalar T)
          (FactorSet.CentralExtensionGroup.coefficientSubgroupElement
            (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) a) =
        (a : ℂˣ)⁻¹
    exact
      FactorSet.CentralExtensionGroup.coefficientScalarCharacter_coefficientSubgroupElement
        (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T)
        (inverseRootsOfUnityCoefficientHom (CanonicalFactorExponent T)) a
  rw [hscalar] at ha
  change
    χ.1.1.values
        ((normalizerEquivRestrictedExtension T S).symm
          (FactorSet.CentralExtensionGroup.coefficientEmbedding
            (RestrictedFactorSet T S)
            (RestrictedFactorSetIsNormalized T S) a)) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) * (χ.1.1.degree : ℂ)
  rw [← normalizerEquivRestrictedExtension_coefficientEmbedding T S a,
    (normalizerEquivRestrictedExtension T S).symm_apply_apply]
  exact ha

/-- Transport an inverse-coefficient character of the fixed restricted
extension back to the normalizer scalar fibre. -/
def restrictedToNormalizerFibre
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (ψ : RestrictedPPrimeInverseCoefficientFibre T S) :
    NormalizerInverseCoefficientFibre T S := by
  let ψp :
      PPrimeIrreducibleCharacter (RestrictedExtensionGroup T S) p :=
    ⟨ψ.1.1, ψ.2⟩
  let χ :=
    (normalizerPPrimeCharacterEquivRestrictedExtension T S).symm ψp
  refine ⟨χ, ?_⟩
  intro z
  let zC : CoefficientSubgroup T :=
    ⟨(((z :
        centralSubgroupInSylowNormalizer
          (LiftedSylow T S) (CoefficientSubgroup T)) :
        SylowNormalizer (LiftedSylow T S)) :
        ExtensionGroup T), z.property⟩
  let a : CanonicalCoefficientGroup T :=
    FactorSet.CentralExtensionGroup.coefficientEquiv
      (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) zC
  have hz :
      (z : SylowNormalizer (LiftedSylow T S)) =
        ((normalizerCoefficientElement T S a :
            centralSubgroupInSylowNormalizer
              (LiftedSylow T S) (CoefficientSubgroup T)) :
          SylowNormalizer (LiftedSylow T S)) := by
    apply Subtype.ext
    change
      (zC : ExtensionGroup T) =
        FactorSet.CentralExtensionGroup.coefficientEmbedding
          (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) a
    exact
      (FactorSet.CentralExtensionGroup.coefficientEmbedding_coefficientEquiv
        (CanonicalFactorSet T) (CanonicalFactorSetIsNormalized T) zC).symm
  have ha := ψ.1.2 a
  change
    ψ.1.1.values
        (normalizerEquivRestrictedExtension T S
          (z : SylowNormalizer (LiftedSylow T S))) =
      (((centralScalarInSylowNormalizer
        (LiftedSylow T S)
        (CoefficientSubgroup T)
        (coefficientSubgroup_le_center T)
        (InverseCoefficientScalar T) z : ℂˣ) : ℂ)) *
        (ψ.1.1.degree : ℂ)
  rw [hz,
    normalizerEquivRestrictedExtension_coefficientEmbedding T S a]
  have hscalar :
      centralScalarInSylowNormalizer
          (LiftedSylow T S)
          (CoefficientSubgroup T)
          (coefficientSubgroup_le_center T)
          (InverseCoefficientScalar T) z =
        (a : ℂˣ)⁻¹ := by
    change (InverseCoefficientScalar T) zC = (a : ℂˣ)⁻¹
    rfl
  rw [hscalar]
  exact ha

/-- The inverse-coefficient scalar fibre in the exact lifted-Sylow
normalizer is canonically the inverse-coefficient fibre of the fixed
restricted factor extension. -/
def normalizerFibreEquivRestrictedInverseCoefficientFibre
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    NormalizerInverseCoefficientFibre T S ≃
      RestrictedPPrimeInverseCoefficientFibre T S where
  toFun := normalizerToRestrictedFibre T S
  invFun := restrictedToNormalizerFibre T S
  left_inv χ := by
    apply Subtype.ext
    exact
      (normalizerPPrimeCharacterEquivRestrictedExtension T S
        ).symm_apply_apply χ.1
  right_inv ψ := by
    apply Subtype.ext
    apply Subtype.ext
    change
      ((normalizerPPrimeCharacterEquivRestrictedExtension T S)
        ((normalizerPPrimeCharacterEquivRestrictedExtension T S).symm
          (⟨ψ.1.1, ψ.2⟩ :
            PPrimeIrreducibleCharacter
              (RestrictedExtensionGroup T S) p))).1 =
        ψ.1.1
    have h :=
      (normalizerPPrimeCharacterEquivRestrictedExtension T S
        ).apply_symm_apply
          (⟨ψ.1.1, ψ.2⟩ :
            PPrimeIrreducibleCharacter (RestrictedExtensionGroup T S) p)
    exact congrArg Subtype.val h

@[simp]
theorem normalizerFibreEquivRestricted_apply_character
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : NormalizerInverseCoefficientFibre T S) :
    (normalizerFibreEquivRestrictedInverseCoefficientFibre T S χ).1.1 =
      (normalizerPPrimeCharacterEquivRestrictedExtension T S χ.1).1 :=
  rfl

@[simp]
theorem normalizerFibreEquivRestricted_degree
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : NormalizerInverseCoefficientFibre T S) :
    (normalizerFibreEquivRestrictedInverseCoefficientFibre
      T S χ).1.1.degree =
        χ.1.1.degree :=
  rfl

/-- The transported restricted-extension character has the exact inverse
coefficient values. -/
theorem normalizerFibreEquivRestricted_coefficient_value
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (χ : NormalizerInverseCoefficientFibre T S)
    (a : CanonicalCoefficientGroup T) :
    (normalizerFibreEquivRestrictedInverseCoefficientFibre
      T S χ).1.1.values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          (RestrictedFactorSet T S)
          (RestrictedFactorSetIsNormalized T S) a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        ((normalizerFibreEquivRestrictedInverseCoefficientFibre
          T S χ).1.1.degree : ℂ) :=
  (normalizerFibreEquivRestrictedInverseCoefficientFibre T S χ).1.2 a

/-! ## Restricted fibres from the full central-index induction hypothesis -/

/-- The source character fibre of `T` corresponds to the fixed restricted
factor fibre, using full local inductive-McKay data below the central index
of an ambient group `B`. -/
def restrictedPPrimeCharacterEquivOfCentralIndexIH
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
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    PPrimeCharactersOver T p ≃
      RestrictedPPrimeInverseCoefficientFibre T S :=
  (pPrimeCharacterEquivOfCentralIndexIH
    ih T hT hExtensionSmall S).trans
      (normalizerFibreEquivRestrictedInverseCoefficientFibre T S)

/-- The full-IH restricted-factor output has the exact inverse coefficient
values in the fixed pulled-back extension. -/
theorem restrictedPPrimeCharacterEquivOfCentralIndexIH_coefficient_value
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
    (restrictedPPrimeCharacterEquivOfCentralIndexIH
      ih T hT hExtensionSmall S χ).1.1.values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          (RestrictedFactorSet T S)
          (RestrictedFactorSetIsNormalized T S) a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        ((restrictedPPrimeCharacterEquivOfCentralIndexIH
          ih T hT hExtensionSmall S χ).1.1.degree : ℂ) :=
  (restrictedPPrimeCharacterEquivOfCentralIndexIH
    ih T hT hExtensionSmall S χ).1.2 a

end NormalSubgroupRestrictedFactorFibre
end InductiveMcKay
end McKayConjecture
