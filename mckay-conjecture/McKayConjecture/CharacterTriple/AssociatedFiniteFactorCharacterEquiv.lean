/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorMultiplicityCharacter
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionCoefficient
import McKayConjecture.CharacterTriple.MultiplicityTensorRecovery

/-!
# Character equivalence for an associated finite factor extension

Fix a finite character triple `T = (A, N, ζ)` and a finite-normalized
associated projective representation `R`.  Its quotient factor set defines a
finite central extension `E` of `A / N`.

This file proves the explicit equivalence

* irreducible characters of `A` lying over `ζ`, and
* irreducible characters of `E` on which the canonical coefficient subgroup
  acts by the inverse roots-of-unity scalar.

The forward map is the multiplicity character constructed in
`AssociatedFiniteFactorMultiplicityCharacter`.  For the inverse map, the
chosen realization of an extension character supplies a projective action of
`A / N` through the base lifts `(q, 1)`.  Its factor is exactly the inverse of
the quotient factor.  Inflating this action to `A` and tensoring it with the
associated projective lift gives an irreducible ordinary representation
lying over `ζ`.

Both inverse laws are proved from the explicit representations and their
characters; no cardinality argument or assumed bijectivity is used.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra TensorProduct

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- Irreducible characters of the original group lying over the character
of the triple. -/
abbrev AssociatedCharactersOver
    (_R : AssociatedProjectiveRepresentation T V P) :=
  CliffordCorrespondence.IrreducibleCharactersOverAlong
    T.normalSubgroup.subtype T.character

/-- Character-level form of the required inverse scalar action on the
coefficient subgroup. -/
def HasInverseCoefficientCharacter
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup) : Prop :=
  ∀ a : rootsOfUnity (associatedFactorExponent T V) ℂ,
    ψ.values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.associatedFiniteQuotientFactorSet
          R.associatedFiniteQuotientFactorSet_isNormalized a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) * (ψ.degree : ℂ)

/-- The target of the finite-factor character correspondence. -/
abbrev InverseCoefficientCharacters
    (R : AssociatedProjectiveRepresentation T V P) :=
  {ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup //
    R.HasInverseCoefficientCharacter ψ}

/-- The character-value condition determines the exact scalar operator on
the chosen realization. -/
theorem realization_coefficientEmbedding
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (a : rootsOfUnity (associatedFactorExponent T V) ℂ) :
    ψ.realization.ρ
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.associatedFiniteQuotientFactorSet
          R.associatedFiniteQuotientFactorSet_isNormalized a) =
      (scalarLinearEquiv ℂ ψ.realization
        (inverseRootsOfUnityCoefficientHom
          (associatedFactorExponent T V) a) :
        ψ.realization →ₗ[ℂ] ψ.realization) := by
  let z :=
    FactorSet.CentralExtensionGroup.coefficientEmbedding
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized a
  have hz :
      z ∈ Subgroup.center
        R.AssociatedFiniteFactorCentralExtensionGroup := by
    exact
      FactorSet.CentralExtensionGroup.coefficientEmbedding_range_le_center
        R.associatedFiniteQuotientFactorSet
        R.associatedFiniteQuotientFactorSet_isNormalized
        ⟨a, rfl⟩
  obtain ⟨c, hc⟩ :=
    ψ.exists_realization_scalar_of_mem_center z hz
  have hdegree :
      c * (ψ.degree : ℂ) =
        (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) * (ψ.degree : ℂ) := by
    rw [← ψ.values_eq_scalar_mul_degree z c hc]
    exact hψ a
  have hc' : c = (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) :=
    mul_right_cancel₀
      (Nat.cast_ne_zero.mpr ψ.degree_ne_zero) hdegree
  rw [hc, hc']
  ext x
  rfl

/-- The forward multiplicity character satisfies the defining coefficient
condition exactly. -/
theorem associatedFiniteMultiplicityExtensionCharacter_hasInverseCoefficientCharacter
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    R.HasInverseCoefficientCharacter
      (R.associatedFiniteMultiplicityExtensionCharacter χ hχ) := by
  intro a
  exact
    R.associatedFiniteMultiplicityExtensionCharacter_values_coefficientEmbedding
      χ hχ a

/-- The explicit forward map into inverse-coefficient extension
characters. -/
def associatedFiniteFactorCharacterMap
    (R : AssociatedProjectiveRepresentation T V P) :
    R.AssociatedCharactersOver →
      R.InverseCoefficientCharacters :=
  fun χ ↦
    ⟨R.associatedFiniteMultiplicityExtensionCharacter χ.1 χ.2,
      R.associatedFiniteMultiplicityExtensionCharacter_hasInverseCoefficientCharacter
        χ.1 χ.2⟩

@[simp]
theorem associatedFiniteFactorCharacterMap_apply_value
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : R.AssociatedCharactersOver) :
    (R.associatedFiniteFactorCharacterMap χ).1 =
      R.associatedFiniteMultiplicityExtensionCharacter χ.1 χ.2 :=
  rfl

/-- The base lift of a quotient element. -/
def associatedFiniteFactorBaseLift
    (R : AssociatedProjectiveRepresentation T V P)
    (q : A ⧸ T.normalSubgroup) :
    R.AssociatedFiniteFactorCentralExtensionGroup :=
  FactorSet.CentralExtensionGroup.mk
    R.associatedFiniteQuotientFactorSet
    R.associatedFiniteQuotientFactorSet_isNormalized q 1

@[simp]
theorem associatedFiniteFactorBaseLift_base
    (R : AssociatedProjectiveRepresentation T V P)
    (q : A ⧸ T.normalSubgroup) :
    FactorSet.CentralExtensionGroup.base
        R.associatedFiniteQuotientFactorSet
        R.associatedFiniteQuotientFactorSet_isNormalized
        (R.associatedFiniteFactorBaseLift q) =
      q :=
  rfl

@[simp]
theorem associatedFiniteFactorBaseLift_coefficient
    (R : AssociatedProjectiveRepresentation T V P)
    (q : A ⧸ T.normalSubgroup) :
    FactorSet.CentralExtensionGroup.coefficient
        R.associatedFiniteQuotientFactorSet
        R.associatedFiniteQuotientFactorSet_isNormalized
        (R.associatedFiniteFactorBaseLift q) =
      1 :=
  rfl

/-- Multiplication of base lifts exposes precisely the quotient factor in
the coefficient subgroup. -/
theorem associatedFiniteFactorBaseLift_mul
    (R : AssociatedProjectiveRepresentation T V P)
    (q r : A ⧸ T.normalSubgroup) :
    R.associatedFiniteFactorBaseLift q *
        R.associatedFiniteFactorBaseLift r =
      FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.associatedFiniteQuotientFactorSet
          R.associatedFiniteQuotientFactorSet_isNormalized
          (R.associatedFiniteQuotientFactorSet q r) *
        R.associatedFiniteFactorBaseLift (q * r) := by
  apply FactorSet.CentralExtensionGroup.ext
  · simp [associatedFiniteFactorBaseLift]
  · simp [associatedFiniteFactorBaseLift,
      R.associatedFiniteQuotientFactorSet_isNormalized.1]

/-- Every extension element is its coefficient element times its base
lift. -/
theorem coefficientEmbedding_mul_associatedFiniteFactorBaseLift
    (R : AssociatedProjectiveRepresentation T V P)
    (x : R.AssociatedFiniteFactorCentralExtensionGroup) :
    FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.associatedFiniteQuotientFactorSet
          R.associatedFiniteQuotientFactorSet_isNormalized
          (FactorSet.CentralExtensionGroup.coefficient
            R.associatedFiniteQuotientFactorSet
            R.associatedFiniteQuotientFactorSet_isNormalized x) *
        R.associatedFiniteFactorBaseLift
          (FactorSet.CentralExtensionGroup.base
            R.associatedFiniteQuotientFactorSet
            R.associatedFiniteQuotientFactorSet_isNormalized x) =
      x := by
  apply FactorSet.CentralExtensionGroup.ext
  · simp [associatedFiniteFactorBaseLift]
  · simp [associatedFiniteFactorBaseLift,
      R.associatedFiniteQuotientFactorSet_isNormalized.1]

/-- An extension character with the prescribed coefficient scalar gives a
projective representation of the quotient through the base lifts. -/
def quotientProjectiveOfInverseCoefficientCharacter
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    ProjectiveRepresentation ℂ (A ⧸ T.normalSubgroup) ψ.realization where
  operator q :=
    LinearEquiv.ofBijective
      (ψ.realization.ρ (R.associatedFiniteFactorBaseLift q))
      (Representation.apply_bijective ψ.realization.ρ
        (R.associatedFiniteFactorBaseLift q))
  factor q r :=
    inverseRootsOfUnityCoefficientHom
      (associatedFactorExponent T V)
      (R.associatedFiniteQuotientFactorSet q r)
  map_mul q r := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro z
    change
      ψ.realization.ρ (R.associatedFiniteFactorBaseLift q)
          (ψ.realization.ρ (R.associatedFiniteFactorBaseLift r) z) =
        (inverseRootsOfUnityCoefficientHom
            (associatedFactorExponent T V)
            (R.associatedFiniteQuotientFactorSet q r) : ℂ) •
          ψ.realization.ρ
            (R.associatedFiniteFactorBaseLift (q * r)) z
    rw [← Module.End.mul_apply, ← map_mul,
      R.associatedFiniteFactorBaseLift_mul q r, map_mul,
      R.realization_coefficientEmbedding ψ hψ]
    rfl

@[simp]
theorem quotientProjectiveOfInverseCoefficientCharacter_operator
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (q : A ⧸ T.normalSubgroup) :
    (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
      ).operator q =
      LinearEquiv.ofBijective
        (ψ.realization.ρ (R.associatedFiniteFactorBaseLift q))
        (Representation.apply_bijective ψ.realization.ρ
          (R.associatedFiniteFactorBaseLift q)) :=
  rfl

@[simp]
theorem quotientProjectiveOfInverseCoefficientCharacter_factor
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (q r : A ⧸ T.normalSubgroup) :
    (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
      ).factor q r =
      inverseRootsOfUnityCoefficientHom
        (associatedFactorExponent T V)
      (R.associatedFiniteQuotientFactorSet q r) :=
  rfl

/-- Orientation of the exact factor identity used by central-extension
linearization. -/
theorem inverseCoefficientHom_quotientFactorSet_eq_projectiveFactor
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (q r : A ⧸ T.normalSubgroup) :
    inverseRootsOfUnityCoefficientHom
        (associatedFactorExponent T V)
        (R.associatedFiniteQuotientFactorSet q r) =
      (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
        ).factor q r :=
  (R.quotientProjectiveOfInverseCoefficientCharacter_factor
    ψ hψ q r).symm

/-- Linearizing the extracted quotient projective representation recovers
the chosen realization of the extension character exactly. -/
theorem quotientProjective_centralExtensionRepresentation_eq_realization
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
      ).centralExtensionRepresentation
        R.associatedFiniteQuotientFactorSet
        R.associatedFiniteQuotientFactorSet_isNormalized
        (inverseRootsOfUnityCoefficientHom
          (associatedFactorExponent T V))
        (R.inverseCoefficientHom_quotientFactorSet_eq_projectiveFactor
          ψ hψ) =
      ψ.realization.ρ := by
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro z
  let c :=
    FactorSet.CentralExtensionGroup.coefficient
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized x
  let q :=
    FactorSet.CentralExtensionGroup.base
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized x
  have hx :
      FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.associatedFiniteQuotientFactorSet
          R.associatedFiniteQuotientFactorSet_isNormalized c *
        R.associatedFiniteFactorBaseLift q =
      x :=
    R.coefficientEmbedding_mul_associatedFiniteFactorBaseLift x
  change
    (inverseRootsOfUnityCoefficientHom
        (associatedFactorExponent T V) c : ℂ) •
      ψ.realization.ρ
        (R.associatedFiniteFactorBaseLift q) z =
      ψ.realization.ρ x z
  rw [← hx, map_mul, R.realization_coefficientEmbedding ψ hψ]
  rfl

/-- The projective quotient action extracted from an irreducible extension
character is irreducible. -/
theorem quotientProjectiveOfInverseCoefficientCharacter_isIrreducible
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
      ).IsIrreducible := by
  let S :=
    R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
  let ρ :=
    S.centralExtensionRepresentation
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized
      (inverseRootsOfUnityCoefficientHom
        (associatedFactorExponent T V))
      (R.inverseCoefficientHom_quotientFactorSet_eq_projectiveFactor
        ψ hψ)
  have hρ : ρ.IsIrreducible := by
    rw [show ρ = ψ.realization.ρ by
      exact
        R.quotientProjective_centralExtensionRepresentation_eq_realization
          ψ hψ]
    exact
      CliffordRestriction.isIrreducible_of_simple
        ψ.realization
  refine ⟨inferInstance, ?_⟩
  intro U hU
  have hInvariant :
      ∀ (x : R.AssociatedFiniteFactorCentralExtensionGroup)
          ⦃z : ψ.realization⦄,
        z ∈ U → ρ x z ∈ U :=
    (S.centralExtensionRepresentation_invariant_iff_isStable
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized
      (inverseRootsOfUnityCoefficientHom
        (associatedFactorExponent T V))
      (R.inverseCoefficientHom_quotientFactorSet_eq_projectiveFactor
        ψ hψ) U).mpr hU
  let W : Subrepresentation ρ :=
    { toSubmodule := U
      apply_mem_toSubmodule := hInvariant }
  letI : ρ.IsIrreducible := hρ
  obtain hW | hW := IsSimpleOrder.eq_bot_or_eq_top W
  · left
    exact congrArg Subrepresentation.toSubmodule hW
  · right
    exact congrArg Subrepresentation.toSubmodule hW

/-- Inflate the extracted quotient projective action to the original
ambient group. -/
abbrev inflatedProjectiveOfInverseCoefficientCharacter
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    ProjectiveRepresentation ℂ A ψ.realization :=
  (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ).comap
    (QuotientGroup.mk' T.normalSubgroup)

/-- The inflated extracted action has factor exactly inverse to the
finite-normalized associated action. -/
theorem inflatedProjective_hasInverseFactorSet
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    R.associatedFiniteFactorProjective.HasInverseFactorSet
      (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ) := by
  intro a b
  change
    inverseRootsOfUnityCoefficientHom
        (associatedFactorExponent T V)
        (R.associatedFiniteQuotientFactorSet
          (QuotientGroup.mk' T.normalSubgroup a)
          (QuotientGroup.mk' T.normalSubgroup b)) =
      (R.associatedFiniteFactorProjective.factor a b)⁻¹
  rw [inverseRootsOfUnityCoefficientHom_apply,
    R.associatedFiniteQuotientFactorSet_mk_coe]

/-- The inflated extracted action is literally the identity on the normal
subgroup. -/
theorem inflatedProjective_isTrivialOnNormal
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ
      ).IsTrivialOnNormal T := by
  intro x
  apply LinearEquiv.toLinearMap_injective
  change
    ψ.realization.ρ
        (R.associatedFiniteFactorBaseLift
          (QuotientGroup.mk' T.normalSubgroup (x : A))) =
      (1 : ψ.realization ≃ₗ[ℂ] ψ.realization)
  have hx :
      QuotientGroup.mk' T.normalSubgroup (x : A) = 1 := by
    exact
      (QuotientGroup.eq_one_iff
        (N := T.normalSubgroup) (x : A)).mpr x.property
  rw [hx]
  change ψ.realization.ρ 1 = 1
  exact map_one ψ.realization.ρ

/-- Inflation along the quotient map preserves irreducibility of the
extracted projective action. -/
theorem inflatedProjectiveOfInverseCoefficientCharacter_isIrreducible
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ
      ).IsIrreducible := by
  let S :=
    R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
  have hcovered :
      S.OperatorsCoveredBy (QuotientGroup.mk' T.normalSubgroup) := by
    intro q
    obtain ⟨a, rfl⟩ :=
      QuotientGroup.mk'_surjective T.normalSubgroup q
    exact ⟨a, rfl⟩
  exact
    (S.isIrreducible_iff_comap
      (QuotientGroup.mk' T.normalSubgroup) hcovered).mp
      (R.quotientProjectiveOfInverseCoefficientCharacter_isIrreducible
        ψ hψ)

/-- The ordinary ambient representation obtained by cancelling the
finite-normalized associated factor against the inflated extracted factor. -/
def inverseCoefficientTensorRepresentation
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    Representation ℂ A (V ⊗[ℂ] ψ.realization) :=
  R.associatedFiniteFactorProjective.cancelTensorRepresentation
    (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ)
    (R.inflatedProjective_hasInverseFactorSet ψ hψ)

/-- The inverse cancelled tensor representation is irreducible. -/
theorem inverseCoefficientTensorRepresentation_isIrreducible
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.inverseCoefficientTensorRepresentation ψ hψ).IsIrreducible := by
  exact
    (R.associatedFiniteFactorAssociated.cancelTensorRepresentation_isIrreducible_iff
        (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ)
        (R.inflatedProjective_hasInverseFactorSet ψ hψ)
        (R.inflatedProjective_isTrivialOnNormal ψ hψ)).mpr
      (R.inflatedProjectiveOfInverseCoefficientCharacter_isIrreducible
        ψ hψ)

/-- The finite-dimensional representation underlying the inverse
construction. -/
abbrev inverseCoefficientTensorFDRep
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    FDRep ℂ A :=
  FDRep.of (R.inverseCoefficientTensorRepresentation ψ hψ)

/-- The inverse cancelled tensor is categorically simple. -/
theorem inverseCoefficientTensorFDRep_simple
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    Simple (R.inverseCoefficientTensorFDRep ψ hψ) := by
  letI : Representation.IsIrreducible
      (R.inverseCoefficientTensorRepresentation ψ hψ) :=
    R.inverseCoefficientTensorRepresentation_isIrreducible ψ hψ
  exact
    FDRep.simple_of_representation_isIrreducible
      (R.inverseCoefficientTensorRepresentation ψ hψ)

/-- The inverse irreducible character on the original ambient group. -/
def inverseCoefficientTensorCharacter
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    IrreducibleCharacter A := by
  letI : Simple (R.inverseCoefficientTensorFDRep ψ hψ) :=
    R.inverseCoefficientTensorFDRep_simple ψ hψ
  exact
    IrreducibleCharacter.ofSimple
      (R.inverseCoefficientTensorFDRep ψ hψ)

@[simp]
theorem inverseCoefficientTensorCharacter_values
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.inverseCoefficientTensorCharacter ψ hψ).values =
      (R.inverseCoefficientTensorFDRep ψ hψ).character := by
  letI : Simple (R.inverseCoefficientTensorFDRep ψ hψ) :=
    R.inverseCoefficientTensorFDRep_simple ψ hψ
  rfl

@[simp]
theorem inverseCoefficientTensorCharacter_degree
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.inverseCoefficientTensorCharacter ψ hψ).degree =
      T.character.degree * ψ.degree := by
  letI : Simple (R.inverseCoefficientTensorFDRep ψ hψ) :=
    R.inverseCoefficientTensorFDRep_simple ψ hψ
  change
    Module.finrank ℂ (V ⊗[ℂ] ψ.realization) =
      T.character.degree * ψ.degree
  rw [Module.finrank_tensorProduct,
    R.associatedFiniteFactorAssociated.finrank_eq_character_degree,
    ψ.realization_finrank]

/-- Fixing a vector of the extracted tensor factor embeds the associated
normal representation into the restriction of the inverse tensor. -/
def inverseCoefficientNormalTensorHom
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (z : ψ.realization) :
    R.associatedFiniteFactorAssociated.fdRestriction ⟶
      FDRep.res T.normalSubgroup.subtype
        (R.inverseCoefficientTensorFDRep ψ hψ) := by
  let L : V →ₗ[ℂ] V ⊗[ℂ] ψ.realization :=
    (TensorProduct.mk ℂ V ψ.realization).flip z
  refine
    { hom := FGModuleCat.ofHom L
      comm := ?_ }
  intro x
  apply FGModuleCat.hom_ext
  ext v
  change
    L (R.associatedFiniteFactorAssociated.restriction x v) =
      R.inverseCoefficientTensorRepresentation ψ hψ
        (x : A) (L v)
  rw [R.associatedFiniteFactorAssociated.restriction_apply]
  change
    R.associatedFiniteFactorProjective.operator (x : A) v ⊗ₜ[ℂ] z =
      TensorProduct.congr
        (R.associatedFiniteFactorProjective.operator (x : A))
        ((R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ
          ).operator (x : A)) (v ⊗ₜ[ℂ] z)
  rw [TensorProduct.congr_tmul,
    R.inflatedProjective_isTrivialOnNormal ψ hψ x]
  rfl

/-- The fixed-vector normal embedding is nonzero for a nonzero tensor
factor. -/
theorem inverseCoefficientNormalTensorHom_ne_zero
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    {z : ψ.realization} (hz : z ≠ 0) :
    R.inverseCoefficientNormalTensorHom ψ hψ z ≠ 0 := by
  obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ :=
    Module.Projective.exists_dual_eq_one ℂ hz
  intro hzero
  have hlinear :=
    congrArg
      (fun f :
        R.associatedFiniteFactorAssociated.fdRestriction ⟶
          FDRep.res T.normalSubgroup.subtype
            (R.inverseCoefficientTensorFDRep ψ hψ) ↦
        f.hom.hom)
      hzero
  have happ := ConcreteCategory.congr_hom hlinear v
  change v ⊗ₜ[ℂ] z = 0 at happ
  have hsliced :=
    congrArg
      (fun t : V ⊗[ℂ] ψ.realization ↦
        TensorProduct.rid ℂ V (φ.lTensor V t))
      happ
  simp only [map_zero, LinearMap.lTensor_tmul,
    TensorProduct.rid_tmul, hφ, one_smul] at hsliced
  exact hv hsliced

/-- The inverse tensor character lies over the character of the original
triple. -/
theorem inverseCoefficientTensorCharacter_liesOver
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character
      (R.inverseCoefficientTensorCharacter ψ hψ) := by
  letI : Simple (R.inverseCoefficientTensorFDRep ψ hψ) :=
    R.inverseCoefficientTensorFDRep_simple ψ hψ
  obtain ⟨z : ψ.realization, hz⟩ :=
    exists_ne (0 : ψ.realization)
  let i :
      R.associatedFiniteFactorAssociated.fdRestriction ≅
        T.character.realization :=
    MultiplicityProjective.restrictionIsoRealization
      R.associatedFiniteFactorAssociated
  let fD :
      T.character.realization ⟶
        FDRep.res T.normalSubgroup.subtype
          (R.inverseCoefficientTensorFDRep ψ hψ) :=
    i.inv ≫ R.inverseCoefficientNormalTensorHom ψ hψ z
  have hfD : fD ≠ 0 := by
    intro hfD
    apply R.inverseCoefficientNormalTensorHom_ne_zero ψ hψ hz
    have hzero := congrArg (fun q ↦ i.hom ≫ q) hfD
    simpa [fD, Category.assoc] using hzero
  let χ : IrreducibleCharacter A :=
    R.inverseCoefficientTensorCharacter ψ hψ
  have hcharacter :
      (R.inverseCoefficientTensorFDRep ψ hψ).character =
        χ.realization.character := by
    rw [χ.realization_character]
    exact (R.inverseCoefficientTensorCharacter_values ψ hψ).symm
  obtain ⟨j :
      R.inverseCoefficientTensorFDRep ψ hψ ≅ χ.realization⟩ :=
    FDRep.nonempty_iso_of_character_eq
      (R.inverseCoefficientTensorFDRep ψ hψ)
      χ.realization hcharacter
  let jRes :
      FDRep.res T.normalSubgroup.subtype
          (R.inverseCoefficientTensorFDRep ψ hψ) ⟶
        FDRep.res T.normalSubgroup.subtype χ.realization :=
    (FDRep.resFunctor T.normalSubgroup.subtype).map j.hom
  let f :
      T.character.realization ⟶
        FDRep.res T.normalSubgroup.subtype χ.realization :=
    fD ≫ jRes
  apply
    (CliffordCorrespondence.liesOverAlong_iff_exists_nonzero
      T.normalSubgroup.subtype T.character χ).mpr
  refine ⟨f, ?_⟩
  intro hf
  apply hfD
  have hzero :=
    congrArg
      (fun q ↦
        q ≫
          (FDRep.resFunctor T.normalSubgroup.subtype).map j.inv)
      hf
  simpa [f, jRes, Category.assoc] using hzero

/-- The explicit inverse map on coefficient-compatible extension
characters. -/
def inverseAssociatedFiniteFactorCharacterMap
    (R : AssociatedProjectiveRepresentation T V P) :
    R.InverseCoefficientCharacters →
      R.AssociatedCharactersOver :=
  fun ψ ↦
    ⟨R.inverseCoefficientTensorCharacter ψ.1 ψ.2,
      R.inverseCoefficientTensorCharacter_liesOver ψ.1 ψ.2⟩

@[simp]
theorem inverseAssociatedFiniteFactorCharacterMap_apply_value
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : R.InverseCoefficientCharacters) :
    (R.inverseAssociatedFiniteFactorCharacterMap ψ).1 =
      R.inverseCoefficientTensorCharacter ψ.1 ψ.2 :=
  rfl

/-- At a base lift, the forward extension character is the projective trace
of the descended multiplicity action. -/
theorem associatedFiniteMultiplicityExtensionCharacter_values_baseLift
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (q : A ⧸ T.normalSubgroup) :
    (R.associatedFiniteMultiplicityExtensionCharacter χ hχ).values
        (R.associatedFiniteFactorBaseLift q) =
      (R.associatedFiniteMultiplicityQuotientProjective χ hχ
        ).traceFunction q := by
  letI : Simple
      (R.associatedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.associatedFiniteMultiplicityExtensionFDRep_simple χ hχ
  change
    LinearMap.trace ℂ (R.AssociatedFiniteMultiplicitySpace χ)
        (R.associatedFiniteMultiplicityExtensionRepresentation χ hχ
          (R.associatedFiniteFactorBaseLift q)) =
      LinearMap.trace ℂ (R.AssociatedFiniteMultiplicitySpace χ)
        ((R.associatedFiniteMultiplicityQuotientProjective χ hχ
          ).operator q)
  rw [associatedFiniteMultiplicityExtensionRepresentation,
    ProjectiveRepresentation.centralExtensionRepresentation_apply]
  simp only [associatedFiniteFactorBaseLift,
    FactorSet.CentralExtensionGroup.coefficient_mk,
    FactorSet.CentralExtensionGroup.base_mk, map_one]
  apply congrArg
    (LinearMap.trace ℂ (R.AssociatedFiniteMultiplicitySpace χ))
  ext z
  rfl

/-- Character formula for the inverse cancelled tensor representation. -/
theorem inverseCoefficientTensorRepresentation_character_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (a : A) :
    (R.inverseCoefficientTensorRepresentation ψ hψ).character a =
      R.associatedFiniteFactorProjective.traceFunction a *
        ψ.values
          (R.associatedFiniteFactorBaseLift
            (QuotientGroup.mk' T.normalSubgroup a)) := by
  change
    LinearMap.trace ℂ (V ⊗[ℂ] ψ.realization)
        (TensorProduct.map
          (R.associatedFiniteFactorProjective.operator a :
            V →ₗ[ℂ] V)
          (ψ.realization.ρ
            (R.associatedFiniteFactorBaseLift
              (QuotientGroup.mk' T.normalSubgroup a)))) =
      R.associatedFiniteFactorProjective.traceFunction a *
        ψ.values
          (R.associatedFiniteFactorBaseLift
            (QuotientGroup.mk' T.normalSubgroup a))
  rw [LinearMap.trace_tensorProduct']
  change
    R.associatedFiniteFactorProjective.traceFunction a *
        ψ.realization.character
          (R.associatedFiniteFactorBaseLift
            (QuotientGroup.mk' T.normalSubgroup a)) =
      R.associatedFiniteFactorProjective.traceFunction a *
        ψ.values
          (R.associatedFiniteFactorBaseLift
            (QuotientGroup.mk' T.normalSubgroup a))
  rw [ψ.realization_character]

/-- Applying the inverse construction to the forward multiplicity character
recovers the original ambient character. -/
theorem inverseAssociatedFiniteFactorCharacterMap_associatedFiniteFactorCharacterMap
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : R.AssociatedCharactersOver) :
    R.inverseAssociatedFiniteFactorCharacterMap
        (R.associatedFiniteFactorCharacterMap χ) =
      χ := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext a
  let ψ :=
    R.associatedFiniteMultiplicityExtensionCharacter χ.1 χ.2
  let hψ :
      R.HasInverseCoefficientCharacter ψ :=
    R.associatedFiniteMultiplicityExtensionCharacter_hasInverseCoefficientCharacter
      χ.1 χ.2
  calc
    (R.inverseCoefficientTensorCharacter ψ hψ).values a =
        (R.inverseCoefficientTensorRepresentation ψ hψ).character a := by
      exact
        congrFun (R.inverseCoefficientTensorCharacter_values ψ hψ) a
    _ =
        R.associatedFiniteFactorProjective.traceFunction a *
          ψ.values
            (R.associatedFiniteFactorBaseLift
              (QuotientGroup.mk' T.normalSubgroup a)) :=
      R.inverseCoefficientTensorRepresentation_character_apply
        ψ hψ a
    _ =
        R.associatedFiniteFactorProjective.traceFunction a *
          (R.associatedFiniteMultiplicityProjective χ.1
            ).traceFunction a := by
      rw [R.associatedFiniteMultiplicityExtensionCharacter_values_baseLift
        χ.1 χ.2]
      apply congrArg
        (fun z : ℂ ↦
          R.associatedFiniteFactorProjective.traceFunction a * z)
      change
        LinearMap.trace ℂ (R.AssociatedFiniteMultiplicitySpace χ.1)
            ((R.associatedFiniteMultiplicityQuotientProjective χ.1 χ.2
              ).operator (QuotientGroup.mk' T.normalSubgroup a)) =
          LinearMap.trace ℂ (R.AssociatedFiniteMultiplicitySpace χ.1)
            ((R.associatedFiniteMultiplicityProjective χ.1).operator a)
      rw [associatedFiniteMultiplicityQuotientProjective,
        ProjectiveRepresentation.quotientDescent_operator_mk]
    _ =
        (MultiplicityProjective.tensorRepresentation
          R.associatedFiniteFactorAssociated
          χ.1.realization.ρ).character a := by
      exact
        (congrFun
          (R.associatedFiniteFactorProjective.cancelTensorLinearAction_character
              (R.associatedFiniteMultiplicityProjective χ.1)
              (R.associatedFiniteMultiplicity_hasInverseFactorSet χ.1))
          a).symm
    _ = χ.1.values a :=
      congrFun
        (MultiplicityProjective.tensorRepresentation_character_eq_of_liesOver
          R.associatedFiniteFactorAssociated χ.1 χ.2) a

/-- An isomorphism of finite-dimensional representation objects gives an
equivalence of their underlying representations. -/
private def representationEquivOfFDRepIso
    {G : Type} [Group G]
    {E F : FDRep ℂ G} (i : E ≅ F) :
    Representation.Equiv E.ρ F.ρ := by
  let e := FDRep.isoToLinearEquiv i
  apply Representation.Equiv.mk e
  intro g
  have hconj := FDRep.Iso.conj_ρ i g
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun hconj (e v)
  simpa [e, LinearEquiv.conj_apply] using hv.symm

/-- The inverse tensor representation is equivalent to the chosen
realization of the irreducible character it affords. -/
def inverseCoefficientTensorRepresentationEquivRealization
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    Representation.Equiv
      (R.inverseCoefficientTensorRepresentation ψ hψ)
      (R.inverseCoefficientTensorCharacter ψ hψ).realization.ρ := by
  letI : Simple (R.inverseCoefficientTensorFDRep ψ hψ) :=
    R.inverseCoefficientTensorFDRep_simple ψ hψ
  let χ := R.inverseCoefficientTensorCharacter ψ hψ
  have hcharacter :
      (R.inverseCoefficientTensorFDRep ψ hψ).character =
        χ.realization.character := by
    rw [χ.realization_character]
    exact (R.inverseCoefficientTensorCharacter_values ψ hψ).symm
  let i :
      R.inverseCoefficientTensorFDRep ψ hψ ≅ χ.realization :=
    Classical.choice (FDRep.nonempty_iso_of_character_eq
      (R.inverseCoefficientTensorFDRep ψ hψ)
      χ.realization hcharacter)
  exact representationEquivOfFDRepIso i

/-- Multiplicity recovery identifies the extracted extension realization
with the multiplicity space of the inverse ambient character. -/
def inverseCoefficientMultiplicityRecoveryEquiv
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    ψ.realization ≃ₗ[ℂ]
      R.AssociatedFiniteMultiplicitySpace
        (R.inverseCoefficientTensorCharacter ψ hψ) :=
  MultiplicityProjective.tensorFactorMultiplicityLinearEquiv
    R.associatedFiniteFactorAssociated
    (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ)
    (R.inflatedProjective_hasInverseFactorSet ψ hψ)
    (R.inflatedProjective_isTrivialOnNormal ψ hψ)
    (R.inverseCoefficientTensorCharacter ψ hψ).realization.ρ
    (R.inverseCoefficientTensorRepresentationEquivRealization ψ hψ)
    (R.inflatedProjectiveOfInverseCoefficientCharacter_isIrreducible
      ψ hψ)
    (R.associatedFiniteMultiplicityProjective_isIrreducible
      (R.inverseCoefficientTensorCharacter ψ hψ)
      (R.inverseCoefficientTensorCharacter_liesOver ψ hψ))

/-- Multiplicity recovery intertwines the inflated chosen projective
operators. -/
@[simp]
theorem inverseCoefficientMultiplicityRecoveryEquiv_intertwines
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (a : A) (z : ψ.realization) :
    R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ
        ((R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ
          ).operator a z) =
      (R.associatedFiniteMultiplicityProjective
        (R.inverseCoefficientTensorCharacter ψ hψ)).operator a
        (R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ z) := by
  exact
    MultiplicityProjective.tensorFactorMultiplicityLinearEquiv_intertwines
      R.associatedFiniteFactorAssociated
      (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ)
      (R.inflatedProjective_hasInverseFactorSet ψ hψ)
      (R.inflatedProjective_isTrivialOnNormal ψ hψ)
      (R.inverseCoefficientTensorCharacter ψ hψ).realization.ρ
      (R.inverseCoefficientTensorRepresentationEquivRealization ψ hψ)
      (R.inflatedProjectiveOfInverseCoefficientCharacter_isIrreducible
        ψ hψ)
      (R.associatedFiniteMultiplicityProjective_isIrreducible
        (R.inverseCoefficientTensorCharacter ψ hψ)
        (R.inverseCoefficientTensorCharacter_liesOver ψ hψ))
      a z

/-- The recovery equivalence also intertwines the quotient projective
operators exactly. -/
theorem inverseCoefficientMultiplicityRecoveryEquiv_intertwines_quotient
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (q : A ⧸ T.normalSubgroup) (z : ψ.realization) :
    R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ
        ((R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
          ).operator q z) =
      (R.associatedFiniteMultiplicityQuotientProjective
        (R.inverseCoefficientTensorCharacter ψ hψ)
        (R.inverseCoefficientTensorCharacter_liesOver ψ hψ)
        ).operator q
        (R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ z) := by
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective T.normalSubgroup q
  change
    R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ
        ((R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ
          ).operator a z) =
      (R.associatedFiniteMultiplicityQuotientProjective
        (R.inverseCoefficientTensorCharacter ψ hψ)
        (R.inverseCoefficientTensorCharacter_liesOver ψ hψ)
        ).operator (QuotientGroup.mk' T.normalSubgroup a)
        (R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ z)
  rw [associatedFiniteMultiplicityQuotientProjective,
    ProjectiveRepresentation.quotientDescent_operator_mk]
  exact
    R.inverseCoefficientMultiplicityRecoveryEquiv_intertwines
      ψ hψ a z

/-- Multiplicity recovery upgrades to an equivalence between the original
extension realization and the forward extension representation of the
inverse ambient character. -/
def inverseCoefficientRealizationEquivForwardExtension
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    Representation.Equiv ψ.realization.ρ
      (R.associatedFiniteMultiplicityExtensionRepresentation
        (R.inverseCoefficientTensorCharacter ψ hψ)
        (R.inverseCoefficientTensorCharacter_liesOver ψ hψ)) := by
  let e :=
    R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ
  apply Representation.Equiv.mk e
  intro x
  apply LinearMap.ext
  intro z
  rw [←
    R.quotientProjective_centralExtensionRepresentation_eq_realization
      ψ hψ]
  change
    e
        ((R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
          ).centralExtensionRepresentation
            R.associatedFiniteQuotientFactorSet
            R.associatedFiniteQuotientFactorSet_isNormalized
            (inverseRootsOfUnityCoefficientHom
              (associatedFactorExponent T V))
            (R.inverseCoefficientHom_quotientFactorSet_eq_projectiveFactor
              ψ hψ) x z) =
      (R.associatedFiniteMultiplicityExtensionRepresentation
        (R.inverseCoefficientTensorCharacter ψ hψ)
        (R.inverseCoefficientTensorCharacter_liesOver ψ hψ)) x (e z)
  rw [associatedFiniteMultiplicityExtensionRepresentation,
    ProjectiveRepresentation.centralExtensionRepresentation_apply_vector,
    ProjectiveRepresentation.centralExtensionRepresentation_apply_vector,
    map_smul]
  exact congrArg
    (fun y ↦
      (inverseRootsOfUnityCoefficientHom
        (associatedFactorExponent T V)
        (FactorSet.CentralExtensionGroup.coefficient
          R.associatedFiniteQuotientFactorSet
          R.associatedFiniteQuotientFactorSet_isNormalized x) : ℂ) • y)
    (R.inverseCoefficientMultiplicityRecoveryEquiv_intertwines_quotient
      ψ hψ
      (FactorSet.CentralExtensionGroup.base
        R.associatedFiniteQuotientFactorSet
        R.associatedFiniteQuotientFactorSet_isNormalized x) z)

/-- Applying the forward map to the inverse tensor character recovers the
original coefficient-compatible extension character. -/
theorem associatedFiniteFactorCharacterMap_inverseAssociatedFiniteFactorCharacterMap
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : R.InverseCoefficientCharacters) :
    R.associatedFiniteFactorCharacterMap
        (R.inverseAssociatedFiniteFactorCharacterMap ψ) =
      ψ := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  let χ :=
    R.inverseCoefficientTensorCharacter ψ.1 ψ.2
  let hχ :
      CliffordCorrespondence.LiesOverAlong
        T.normalSubgroup.subtype T.character χ :=
    R.inverseCoefficientTensorCharacter_liesOver ψ.1 ψ.2
  letI : Simple
      (R.associatedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.associatedFiniteMultiplicityExtensionFDRep_simple χ hχ
  change
    (R.associatedFiniteMultiplicityExtensionFDRep χ hχ).character x =
      ψ.1.values x
  calc
    (R.associatedFiniteMultiplicityExtensionFDRep χ hχ).character x =
        ψ.1.realization.character x := by
      exact
        (congrFun
          (Representation.char_iso
            (R.inverseCoefficientRealizationEquivForwardExtension
              ψ.1 ψ.2)) x).symm
    _ = ψ.1.values x :=
      congrFun ψ.1.realization_character x

/-- The explicit character equivalence between characters over the triple
character and inverse-coefficient characters of the finite factor
extension. -/
def associatedFiniteFactorCharacterEquiv
    (R : AssociatedProjectiveRepresentation T V P) :
    R.AssociatedCharactersOver ≃
      R.InverseCoefficientCharacters where
  toFun := R.associatedFiniteFactorCharacterMap
  invFun := R.inverseAssociatedFiniteFactorCharacterMap
  left_inv :=
    R.inverseAssociatedFiniteFactorCharacterMap_associatedFiniteFactorCharacterMap
  right_inv :=
    R.associatedFiniteFactorCharacterMap_inverseAssociatedFiniteFactorCharacterMap

@[simp]
theorem associatedFiniteFactorCharacterEquiv_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : R.AssociatedCharactersOver) :
    R.associatedFiniteFactorCharacterEquiv χ =
      R.associatedFiniteFactorCharacterMap χ :=
  rfl

@[simp]
theorem associatedFiniteFactorCharacterEquiv_symm_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : R.InverseCoefficientCharacters) :
    R.associatedFiniteFactorCharacterEquiv.symm ψ =
      R.inverseAssociatedFiniteFactorCharacterMap ψ :=
  rfl

/-- Prime-to-`p` characters in the source of the finite-factor
correspondence. -/
abbrev AssociatedPPrimeCharactersOver
    (R : AssociatedProjectiveRepresentation T V P) (p : ℕ) :=
  {χ : R.AssociatedCharactersOver // χ.1.IsPPrimeDegree p}

/-- Prime-to-`p` inverse-coefficient characters of the finite factor
extension. -/
abbrev InverseCoefficientPPrimeCharacters
    (R : AssociatedProjectiveRepresentation T V P) (p : ℕ) :=
  {ψ : R.InverseCoefficientCharacters // ψ.val.IsPPrimeDegree p}

/-- If the triple character has prime-to-`p` degree, the forward map
preserves and reflects prime-to-`p` degree. -/
theorem associatedFiniteMultiplicityExtensionCharacter_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (hT : T.character.IsPPrimeDegree p) :
    (R.associatedFiniteMultiplicityExtensionCharacter χ hχ
      ).IsPPrimeDegree p ↔
      χ.IsPPrimeDegree p := by
  have hT' : ¬p ∣ T.character.degree := hT
  rw [IrreducibleCharacter.IsPPrimeDegree,
    IrreducibleCharacter.IsPPrimeDegree,
    ← R.associatedFiniteMultiplicityExtensionCharacter_degree_mul χ hχ,
    hp.dvd_mul, not_or]
  simp [hT']

/-- The inverse tensor has prime-to-`p` degree exactly when its extension
character does, provided the triple character has prime-to-`p` degree. -/
theorem inverseCoefficientTensorCharacter_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (R : AssociatedProjectiveRepresentation T V P)
    (ψ : IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (hT : T.character.IsPPrimeDegree p) :
    (R.inverseCoefficientTensorCharacter ψ hψ).IsPPrimeDegree p ↔
      ψ.IsPPrimeDegree p := by
  have hT' : ¬p ∣ T.character.degree := hT
  rw [IrreducibleCharacter.IsPPrimeDegree,
    IrreducibleCharacter.IsPPrimeDegree,
    R.inverseCoefficientTensorCharacter_degree,
    hp.dvd_mul, not_or]
  simp [hT']

/-- The associated finite-factor character equivalence restricted to
prime-to-`p` characters. -/
def associatedFiniteFactorPPrimeCharacterEquiv
    {p : ℕ} (hp : p.Prime)
    (R : AssociatedProjectiveRepresentation T V P)
    (hT : T.character.IsPPrimeDegree p) :
    R.AssociatedPPrimeCharactersOver p ≃
      R.InverseCoefficientPPrimeCharacters p where
  toFun χ :=
    ⟨R.associatedFiniteFactorCharacterMap χ.1,
      (R.associatedFiniteMultiplicityExtensionCharacter_isPPrime_iff
        hp χ.1.1 χ.1.2 hT).mpr χ.2⟩
  invFun ψ :=
    ⟨R.inverseAssociatedFiniteFactorCharacterMap ψ.1,
      (R.inverseCoefficientTensorCharacter_isPPrime_iff
        hp ψ.1.1 ψ.1.2 hT).mpr ψ.2⟩
  left_inv χ := by
    apply Subtype.ext
    exact
      R.inverseAssociatedFiniteFactorCharacterMap_associatedFiniteFactorCharacterMap
        χ.1
  right_inv ψ := by
    apply Subtype.ext
    exact
      R.associatedFiniteFactorCharacterMap_inverseAssociatedFiniteFactorCharacterMap
        ψ.1

@[simp]
theorem associatedFiniteFactorPPrimeCharacterEquiv_apply_value
    {p : ℕ} (hp : p.Prime)
    (R : AssociatedProjectiveRepresentation T V P)
    (hT : T.character.IsPPrimeDegree p)
    (χ : R.AssociatedPPrimeCharactersOver p) :
    (R.associatedFiniteFactorPPrimeCharacterEquiv hp hT χ).1 =
      R.associatedFiniteFactorCharacterMap χ.1 :=
  rfl

@[simp]
theorem associatedFiniteFactorPPrimeCharacterEquiv_symm_apply_value
    {p : ℕ} (hp : p.Prime)
    (R : AssociatedProjectiveRepresentation T V P)
    (hT : T.character.IsPPrimeDegree p)
    (ψ : R.InverseCoefficientPPrimeCharacters p) :
    ((R.associatedFiniteFactorPPrimeCharacterEquiv hp hT).symm ψ).1 =
      R.inverseAssociatedFiniteFactorCharacterMap ψ.1 :=
  rfl

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
