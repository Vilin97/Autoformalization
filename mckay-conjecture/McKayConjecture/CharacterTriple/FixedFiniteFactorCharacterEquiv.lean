/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.CharacterTriple.FixedFiniteFactorMultiplicityCharacter
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
`FixedFiniteFactorMultiplicityCharacter`.  For the inverse map, the
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
namespace FixedFiniteFactorData

variable {A : Type} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- Irreducible characters of the original group lying over the character
of the triple. -/
abbrev AssociatedCharactersOver
    (_R : FixedFiniteFactorData T V) :=
  CliffordCorrespondence.IrreducibleCharactersOverAlong
    T.normalSubgroup.subtype T.character

/-- Character-level form of the required inverse scalar action on the
coefficient subgroup. -/
def HasInverseCoefficientCharacter
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup) : Prop :=
  ∀ a : rootsOfUnity (R.exponent) ℂ,
    ψ.values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.fixedFiniteQuotientFactorSet
          R.fixedFiniteQuotientFactorSet_isNormalized a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) * (ψ.degree : ℂ)

/-- The target of the finite-factor character correspondence. -/
abbrev InverseCoefficientCharacters
    (R : FixedFiniteFactorData T V) :=
  {ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup //
    R.HasInverseCoefficientCharacter ψ}

/-- The character-value condition determines the exact scalar operator on
the chosen realization. -/
theorem realization_coefficientEmbedding
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (a : rootsOfUnity (R.exponent) ℂ) :
    ψ.realization.ρ
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.fixedFiniteQuotientFactorSet
          R.fixedFiniteQuotientFactorSet_isNormalized a) =
      (scalarLinearEquiv ℂ ψ.realization
        (inverseRootsOfUnityCoefficientHom
          (R.exponent) a) :
        ψ.realization →ₗ[ℂ] ψ.realization) := by
  let z :=
    FactorSet.CentralExtensionGroup.coefficientEmbedding
      R.fixedFiniteQuotientFactorSet
      R.fixedFiniteQuotientFactorSet_isNormalized a
  have hz :
      z ∈ Subgroup.center
        R.FixedFiniteFactorCentralExtensionGroup := by
    exact
      FactorSet.CentralExtensionGroup.coefficientEmbedding_range_le_center
        R.fixedFiniteQuotientFactorSet
        R.fixedFiniteQuotientFactorSet_isNormalized
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
theorem fixedFiniteMultiplicityExtensionCharacter_hasInverseCoefficientCharacter
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    R.HasInverseCoefficientCharacter
      (R.fixedFiniteMultiplicityExtensionCharacter χ hχ) := by
  intro a
  exact
    R.fixedFiniteMultiplicityExtensionCharacter_values_coefficientEmbedding
      χ hχ a

/-- The explicit forward map into inverse-coefficient extension
characters. -/
def fixedFiniteFactorCharacterMap
    (R : FixedFiniteFactorData T V) :
    R.AssociatedCharactersOver →
      R.InverseCoefficientCharacters :=
  fun χ ↦
    ⟨R.fixedFiniteMultiplicityExtensionCharacter χ.1 χ.2,
      R.fixedFiniteMultiplicityExtensionCharacter_hasInverseCoefficientCharacter
        χ.1 χ.2⟩

@[simp]
theorem fixedFiniteFactorCharacterMap_apply_value
    (R : FixedFiniteFactorData T V)
    (χ : R.AssociatedCharactersOver) :
    (R.fixedFiniteFactorCharacterMap χ).1 =
      R.fixedFiniteMultiplicityExtensionCharacter χ.1 χ.2 :=
  rfl

/-- The base lift of a quotient element. -/
def fixedFiniteFactorBaseLift
    (R : FixedFiniteFactorData T V)
    (q : A ⧸ T.normalSubgroup) :
    R.FixedFiniteFactorCentralExtensionGroup :=
  FactorSet.CentralExtensionGroup.mk
    R.fixedFiniteQuotientFactorSet
    R.fixedFiniteQuotientFactorSet_isNormalized q 1

@[simp]
theorem fixedFiniteFactorBaseLift_base
    (R : FixedFiniteFactorData T V)
    (q : A ⧸ T.normalSubgroup) :
    FactorSet.CentralExtensionGroup.base
        R.fixedFiniteQuotientFactorSet
        R.fixedFiniteQuotientFactorSet_isNormalized
        (R.fixedFiniteFactorBaseLift q) =
      q :=
  rfl

@[simp]
theorem fixedFiniteFactorBaseLift_coefficient
    (R : FixedFiniteFactorData T V)
    (q : A ⧸ T.normalSubgroup) :
    FactorSet.CentralExtensionGroup.coefficient
        R.fixedFiniteQuotientFactorSet
        R.fixedFiniteQuotientFactorSet_isNormalized
        (R.fixedFiniteFactorBaseLift q) =
      1 :=
  rfl

/-- Multiplication of base lifts exposes precisely the quotient factor in
the coefficient subgroup. -/
theorem fixedFiniteFactorBaseLift_mul
    (R : FixedFiniteFactorData T V)
    (q r : A ⧸ T.normalSubgroup) :
    R.fixedFiniteFactorBaseLift q *
        R.fixedFiniteFactorBaseLift r =
      FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.fixedFiniteQuotientFactorSet
          R.fixedFiniteQuotientFactorSet_isNormalized
          (R.fixedFiniteQuotientFactorSet q r) *
        R.fixedFiniteFactorBaseLift (q * r) := by
  apply FactorSet.CentralExtensionGroup.ext
  · simp [fixedFiniteFactorBaseLift]
  · simp [fixedFiniteFactorBaseLift,
      R.fixedFiniteQuotientFactorSet_isNormalized.1]

/-- Every extension element is its coefficient element times its base
lift. -/
theorem coefficientEmbedding_mul_fixedFiniteFactorBaseLift
    (R : FixedFiniteFactorData T V)
    (x : R.FixedFiniteFactorCentralExtensionGroup) :
    FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.fixedFiniteQuotientFactorSet
          R.fixedFiniteQuotientFactorSet_isNormalized
          (FactorSet.CentralExtensionGroup.coefficient
            R.fixedFiniteQuotientFactorSet
            R.fixedFiniteQuotientFactorSet_isNormalized x) *
        R.fixedFiniteFactorBaseLift
          (FactorSet.CentralExtensionGroup.base
            R.fixedFiniteQuotientFactorSet
            R.fixedFiniteQuotientFactorSet_isNormalized x) =
      x := by
  apply FactorSet.CentralExtensionGroup.ext
  · simp [fixedFiniteFactorBaseLift]
  · simp [fixedFiniteFactorBaseLift,
      R.fixedFiniteQuotientFactorSet_isNormalized.1]

/-- An extension character with the prescribed coefficient scalar gives a
projective representation of the quotient through the base lifts. -/
def quotientProjectiveOfInverseCoefficientCharacter
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    ProjectiveRepresentation ℂ (A ⧸ T.normalSubgroup) ψ.realization where
  operator q :=
    LinearEquiv.ofBijective
      (ψ.realization.ρ (R.fixedFiniteFactorBaseLift q))
      (Representation.apply_bijective ψ.realization.ρ
        (R.fixedFiniteFactorBaseLift q))
  factor q r :=
    inverseRootsOfUnityCoefficientHom
      (R.exponent)
      (R.fixedFiniteQuotientFactorSet q r)
  map_mul q r := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro z
    change
      ψ.realization.ρ (R.fixedFiniteFactorBaseLift q)
          (ψ.realization.ρ (R.fixedFiniteFactorBaseLift r) z) =
        (inverseRootsOfUnityCoefficientHom
            (R.exponent)
            (R.fixedFiniteQuotientFactorSet q r) : ℂ) •
          ψ.realization.ρ
            (R.fixedFiniteFactorBaseLift (q * r)) z
    rw [← Module.End.mul_apply, ← map_mul,
      R.fixedFiniteFactorBaseLift_mul q r, map_mul,
      R.realization_coefficientEmbedding ψ hψ]
    rfl

@[simp]
theorem quotientProjectiveOfInverseCoefficientCharacter_operator
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (q : A ⧸ T.normalSubgroup) :
    (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
      ).operator q =
      LinearEquiv.ofBijective
        (ψ.realization.ρ (R.fixedFiniteFactorBaseLift q))
        (Representation.apply_bijective ψ.realization.ρ
          (R.fixedFiniteFactorBaseLift q)) :=
  rfl

@[simp]
theorem quotientProjectiveOfInverseCoefficientCharacter_factor
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (q r : A ⧸ T.normalSubgroup) :
    (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
      ).factor q r =
      inverseRootsOfUnityCoefficientHom
        (R.exponent)
      (R.fixedFiniteQuotientFactorSet q r) :=
  rfl

/-- Orientation of the exact factor identity used by central-extension
linearization. -/
theorem inverseCoefficientHom_quotientFactorSet_eq_projectiveFactor
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (q r : A ⧸ T.normalSubgroup) :
    inverseRootsOfUnityCoefficientHom
        (R.exponent)
        (R.fixedFiniteQuotientFactorSet q r) =
      (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
        ).factor q r :=
  (R.quotientProjectiveOfInverseCoefficientCharacter_factor
    ψ hψ q r).symm

/-- Linearizing the extracted quotient projective representation recovers
the chosen realization of the extension character exactly. -/
theorem quotientProjective_centralExtensionRepresentation_eq_realization
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
      ).centralExtensionRepresentation
        R.fixedFiniteQuotientFactorSet
        R.fixedFiniteQuotientFactorSet_isNormalized
        (inverseRootsOfUnityCoefficientHom
          (R.exponent))
        (R.inverseCoefficientHom_quotientFactorSet_eq_projectiveFactor
          ψ hψ) =
      ψ.realization.ρ := by
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro z
  let c :=
    FactorSet.CentralExtensionGroup.coefficient
      R.fixedFiniteQuotientFactorSet
      R.fixedFiniteQuotientFactorSet_isNormalized x
  let q :=
    FactorSet.CentralExtensionGroup.base
      R.fixedFiniteQuotientFactorSet
      R.fixedFiniteQuotientFactorSet_isNormalized x
  have hx :
      FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.fixedFiniteQuotientFactorSet
          R.fixedFiniteQuotientFactorSet_isNormalized c *
        R.fixedFiniteFactorBaseLift q =
      x :=
    R.coefficientEmbedding_mul_fixedFiniteFactorBaseLift x
  change
    (inverseRootsOfUnityCoefficientHom
        (R.exponent) c : ℂ) •
      ψ.realization.ρ
        (R.fixedFiniteFactorBaseLift q) z =
      ψ.realization.ρ x z
  rw [← hx, map_mul, R.realization_coefficientEmbedding ψ hψ]
  rfl

/-- The projective quotient action extracted from an irreducible extension
character is irreducible. -/
theorem quotientProjectiveOfInverseCoefficientCharacter_isIrreducible
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
      ).IsIrreducible := by
  let S :=
    R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
  let ρ :=
    S.centralExtensionRepresentation
      R.fixedFiniteQuotientFactorSet
      R.fixedFiniteQuotientFactorSet_isNormalized
      (inverseRootsOfUnityCoefficientHom
        (R.exponent))
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
      ∀ (x : R.FixedFiniteFactorCentralExtensionGroup)
          ⦃z : ψ.realization⦄,
        z ∈ U → ρ x z ∈ U :=
    (S.centralExtensionRepresentation_invariant_iff_isStable
      R.fixedFiniteQuotientFactorSet
      R.fixedFiniteQuotientFactorSet_isNormalized
      (inverseRootsOfUnityCoefficientHom
        (R.exponent))
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
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    ProjectiveRepresentation ℂ A ψ.realization :=
  (R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ).comap
    (QuotientGroup.mk' T.normalSubgroup)

/-- The inflated extracted action has factor exactly inverse to the
finite-normalized associated action. -/
theorem inflatedProjective_hasInverseFactorSet
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    R.fixedFiniteFactorProjective.HasInverseFactorSet
      (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ) := by
  intro a b
  change
    inverseRootsOfUnityCoefficientHom
        (R.exponent)
        (R.fixedFiniteQuotientFactorSet
          (QuotientGroup.mk' T.normalSubgroup a)
          (QuotientGroup.mk' T.normalSubgroup b)) =
      (R.fixedFiniteFactorProjective.factor a b)⁻¹
  rw [inverseRootsOfUnityCoefficientHom_apply,
    R.fixedFiniteQuotientFactorSet_mk_coe]

/-- The inflated extracted action is literally the identity on the normal
subgroup. -/
theorem inflatedProjective_isTrivialOnNormal
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ
      ).IsTrivialOnNormal T := by
  intro x
  apply LinearEquiv.toLinearMap_injective
  change
    ψ.realization.ρ
        (R.fixedFiniteFactorBaseLift
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
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
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
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    Representation ℂ A (V ⊗[ℂ] ψ.realization) :=
  R.fixedFiniteFactorProjective.cancelTensorRepresentation
    (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ)
    (R.inflatedProjective_hasInverseFactorSet ψ hψ)

/-- The inverse cancelled tensor representation is irreducible. -/
theorem inverseCoefficientTensorRepresentation_isIrreducible
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.inverseCoefficientTensorRepresentation ψ hψ).IsIrreducible := by
  exact
    (R.fixedFiniteFactorAssociated.cancelTensorRepresentation_isIrreducible_iff
        (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ)
        (R.inflatedProjective_hasInverseFactorSet ψ hψ)
        (R.inflatedProjective_isTrivialOnNormal ψ hψ)).mpr
      (R.inflatedProjectiveOfInverseCoefficientCharacter_isIrreducible
        ψ hψ)

/-- The finite-dimensional representation underlying the inverse
construction. -/
abbrev inverseCoefficientTensorFDRep
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    FDRep ℂ A :=
  FDRep.of (R.inverseCoefficientTensorRepresentation ψ hψ)

/-- The inverse cancelled tensor is categorically simple. -/
theorem inverseCoefficientTensorFDRep_simple
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
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
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    IrreducibleCharacter A := by
  letI : Simple (R.inverseCoefficientTensorFDRep ψ hψ) :=
    R.inverseCoefficientTensorFDRep_simple ψ hψ
  exact
    IrreducibleCharacter.ofSimple
      (R.inverseCoefficientTensorFDRep ψ hψ)

@[simp]
theorem inverseCoefficientTensorCharacter_values
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.inverseCoefficientTensorCharacter ψ hψ).values =
      (R.inverseCoefficientTensorFDRep ψ hψ).character := by
  letI : Simple (R.inverseCoefficientTensorFDRep ψ hψ) :=
    R.inverseCoefficientTensorFDRep_simple ψ hψ
  rfl

@[simp]
theorem inverseCoefficientTensorCharacter_degree
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    (R.inverseCoefficientTensorCharacter ψ hψ).degree =
      T.character.degree * ψ.degree := by
  letI : Simple (R.inverseCoefficientTensorFDRep ψ hψ) :=
    R.inverseCoefficientTensorFDRep_simple ψ hψ
  change
    Module.finrank ℂ (V ⊗[ℂ] ψ.realization) =
      T.character.degree * ψ.degree
  rw [Module.finrank_tensorProduct,
    R.fixedFiniteFactorAssociated.finrank_eq_character_degree,
    ψ.realization_finrank]

/-- Fixing a vector of the extracted tensor factor embeds the associated
normal representation into the restriction of the inverse tensor. -/
def inverseCoefficientNormalTensorHom
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (z : ψ.realization) :
    R.fixedFiniteFactorAssociated.fdRestriction ⟶
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
    L (R.fixedFiniteFactorAssociated.restriction x v) =
      R.inverseCoefficientTensorRepresentation ψ hψ
        (x : A) (L v)
  rw [R.fixedFiniteFactorAssociated.restriction_apply]
  change
    R.fixedFiniteFactorProjective.operator (x : A) v ⊗ₜ[ℂ] z =
      TensorProduct.congr
        (R.fixedFiniteFactorProjective.operator (x : A))
        ((R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ
          ).operator (x : A)) (v ⊗ₜ[ℂ] z)
  rw [TensorProduct.congr_tmul,
    R.inflatedProjective_isTrivialOnNormal ψ hψ x]
  rfl

/-- The fixed-vector normal embedding is nonzero for a nonzero tensor
factor. -/
theorem inverseCoefficientNormalTensorHom_ne_zero
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
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
        R.fixedFiniteFactorAssociated.fdRestriction ⟶
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
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character
      (R.inverseCoefficientTensorCharacter ψ hψ) := by
  letI : Simple (R.inverseCoefficientTensorFDRep ψ hψ) :=
    R.inverseCoefficientTensorFDRep_simple ψ hψ
  obtain ⟨z : ψ.realization, hz⟩ :=
    exists_ne (0 : ψ.realization)
  let i :
      R.fixedFiniteFactorAssociated.fdRestriction ≅
        T.character.realization :=
    MultiplicityProjective.restrictionIsoRealization
      R.fixedFiniteFactorAssociated
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
def inverseFixedFiniteFactorCharacterMap
    (R : FixedFiniteFactorData T V) :
    R.InverseCoefficientCharacters →
      R.AssociatedCharactersOver :=
  fun ψ ↦
    ⟨R.inverseCoefficientTensorCharacter ψ.1 ψ.2,
      R.inverseCoefficientTensorCharacter_liesOver ψ.1 ψ.2⟩

@[simp]
theorem inverseFixedFiniteFactorCharacterMap_apply_value
    (R : FixedFiniteFactorData T V)
    (ψ : R.InverseCoefficientCharacters) :
    (R.inverseFixedFiniteFactorCharacterMap ψ).1 =
      R.inverseCoefficientTensorCharacter ψ.1 ψ.2 :=
  rfl

/-- At a base lift, the forward extension character is the projective trace
of the descended multiplicity action. -/
theorem fixedFiniteMultiplicityExtensionCharacter_values_baseLift
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (q : A ⧸ T.normalSubgroup) :
    (R.fixedFiniteMultiplicityExtensionCharacter χ hχ).values
        (R.fixedFiniteFactorBaseLift q) =
      (R.fixedFiniteMultiplicityQuotientProjective χ hχ
        ).traceFunction q := by
  letI : Simple
      (R.fixedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.fixedFiniteMultiplicityExtensionFDRep_simple χ hχ
  change
    LinearMap.trace ℂ (R.FixedFiniteMultiplicitySpace χ)
        (R.fixedFiniteMultiplicityExtensionRepresentation χ hχ
          (R.fixedFiniteFactorBaseLift q)) =
      LinearMap.trace ℂ (R.FixedFiniteMultiplicitySpace χ)
        ((R.fixedFiniteMultiplicityQuotientProjective χ hχ
          ).operator q)
  rw [fixedFiniteMultiplicityExtensionRepresentation,
    ProjectiveRepresentation.centralExtensionRepresentation_apply]
  simp only [fixedFiniteFactorBaseLift,
    FactorSet.CentralExtensionGroup.coefficient_mk,
    FactorSet.CentralExtensionGroup.base_mk, map_one]
  apply congrArg
    (LinearMap.trace ℂ (R.FixedFiniteMultiplicitySpace χ))
  ext z
  rfl

/-- Character formula for the inverse cancelled tensor representation. -/
theorem inverseCoefficientTensorRepresentation_character_apply
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (a : A) :
    (R.inverseCoefficientTensorRepresentation ψ hψ).character a =
      R.fixedFiniteFactorProjective.traceFunction a *
        ψ.values
          (R.fixedFiniteFactorBaseLift
            (QuotientGroup.mk' T.normalSubgroup a)) := by
  change
    LinearMap.trace ℂ (V ⊗[ℂ] ψ.realization)
        (TensorProduct.map
          (R.fixedFiniteFactorProjective.operator a :
            V →ₗ[ℂ] V)
          (ψ.realization.ρ
            (R.fixedFiniteFactorBaseLift
              (QuotientGroup.mk' T.normalSubgroup a)))) =
      R.fixedFiniteFactorProjective.traceFunction a *
        ψ.values
          (R.fixedFiniteFactorBaseLift
            (QuotientGroup.mk' T.normalSubgroup a))
  rw [LinearMap.trace_tensorProduct']
  change
    R.fixedFiniteFactorProjective.traceFunction a *
        ψ.realization.character
          (R.fixedFiniteFactorBaseLift
            (QuotientGroup.mk' T.normalSubgroup a)) =
      R.fixedFiniteFactorProjective.traceFunction a *
        ψ.values
          (R.fixedFiniteFactorBaseLift
            (QuotientGroup.mk' T.normalSubgroup a))
  rw [ψ.realization_character]

/-- Applying the inverse construction to the forward multiplicity character
recovers the original ambient character. -/
theorem inverseFixedFiniteFactorCharacterMap_fixedFiniteFactorCharacterMap
    (R : FixedFiniteFactorData T V)
    (χ : R.AssociatedCharactersOver) :
    R.inverseFixedFiniteFactorCharacterMap
        (R.fixedFiniteFactorCharacterMap χ) =
      χ := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext a
  let ψ :=
    R.fixedFiniteMultiplicityExtensionCharacter χ.1 χ.2
  let hψ :
      R.HasInverseCoefficientCharacter ψ :=
    R.fixedFiniteMultiplicityExtensionCharacter_hasInverseCoefficientCharacter
      χ.1 χ.2
  calc
    (R.inverseCoefficientTensorCharacter ψ hψ).values a =
        (R.inverseCoefficientTensorRepresentation ψ hψ).character a := by
      exact
        congrFun (R.inverseCoefficientTensorCharacter_values ψ hψ) a
    _ =
        R.fixedFiniteFactorProjective.traceFunction a *
          ψ.values
            (R.fixedFiniteFactorBaseLift
              (QuotientGroup.mk' T.normalSubgroup a)) :=
      R.inverseCoefficientTensorRepresentation_character_apply
        ψ hψ a
    _ =
        R.fixedFiniteFactorProjective.traceFunction a *
          (R.fixedFiniteMultiplicityProjective χ.1
            ).traceFunction a := by
      rw [R.fixedFiniteMultiplicityExtensionCharacter_values_baseLift
        χ.1 χ.2]
      apply congrArg
        (fun z : ℂ ↦
          R.fixedFiniteFactorProjective.traceFunction a * z)
      change
        LinearMap.trace ℂ (R.FixedFiniteMultiplicitySpace χ.1)
            ((R.fixedFiniteMultiplicityQuotientProjective χ.1 χ.2
              ).operator (QuotientGroup.mk' T.normalSubgroup a)) =
          LinearMap.trace ℂ (R.FixedFiniteMultiplicitySpace χ.1)
            ((R.fixedFiniteMultiplicityProjective χ.1).operator a)
      rw [fixedFiniteMultiplicityQuotientProjective,
        ProjectiveRepresentation.quotientDescent_operator_mk]
    _ =
        (MultiplicityProjective.tensorRepresentation
          R.fixedFiniteFactorAssociated
          χ.1.realization.ρ).character a := by
      exact
        (congrFun
          (R.fixedFiniteFactorProjective.cancelTensorLinearAction_character
              (R.fixedFiniteMultiplicityProjective χ.1)
              (R.fixedFiniteMultiplicity_hasInverseFactorSet χ.1))
          a).symm
    _ = χ.1.values a :=
      congrFun
        (MultiplicityProjective.tensorRepresentation_character_eq_of_liesOver
          R.fixedFiniteFactorAssociated χ.1 χ.2) a

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
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
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
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    ψ.realization ≃ₗ[ℂ]
      R.FixedFiniteMultiplicitySpace
        (R.inverseCoefficientTensorCharacter ψ hψ) :=
  MultiplicityProjective.tensorFactorMultiplicityLinearEquiv
    R.fixedFiniteFactorAssociated
    (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ)
    (R.inflatedProjective_hasInverseFactorSet ψ hψ)
    (R.inflatedProjective_isTrivialOnNormal ψ hψ)
    (R.inverseCoefficientTensorCharacter ψ hψ).realization.ρ
    (R.inverseCoefficientTensorRepresentationEquivRealization ψ hψ)
    (R.inflatedProjectiveOfInverseCoefficientCharacter_isIrreducible
      ψ hψ)
    (R.fixedFiniteMultiplicityProjective_isIrreducible
      (R.inverseCoefficientTensorCharacter ψ hψ)
      (R.inverseCoefficientTensorCharacter_liesOver ψ hψ))

/-- Multiplicity recovery intertwines the inflated chosen projective
operators. -/
@[simp]
theorem inverseCoefficientMultiplicityRecoveryEquiv_intertwines
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (a : A) (z : ψ.realization) :
    R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ
        ((R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ
          ).operator a z) =
      (R.fixedFiniteMultiplicityProjective
        (R.inverseCoefficientTensorCharacter ψ hψ)).operator a
        (R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ z) := by
  exact
    MultiplicityProjective.tensorFactorMultiplicityLinearEquiv_intertwines
      R.fixedFiniteFactorAssociated
      (R.inflatedProjectiveOfInverseCoefficientCharacter ψ hψ)
      (R.inflatedProjective_hasInverseFactorSet ψ hψ)
      (R.inflatedProjective_isTrivialOnNormal ψ hψ)
      (R.inverseCoefficientTensorCharacter ψ hψ).realization.ρ
      (R.inverseCoefficientTensorRepresentationEquivRealization ψ hψ)
      (R.inflatedProjectiveOfInverseCoefficientCharacter_isIrreducible
        ψ hψ)
      (R.fixedFiniteMultiplicityProjective_isIrreducible
        (R.inverseCoefficientTensorCharacter ψ hψ)
        (R.inverseCoefficientTensorCharacter_liesOver ψ hψ))
      a z

/-- The recovery equivalence also intertwines the quotient projective
operators exactly. -/
theorem inverseCoefficientMultiplicityRecoveryEquiv_intertwines_quotient
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ)
    (q : A ⧸ T.normalSubgroup) (z : ψ.realization) :
    R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ
        ((R.quotientProjectiveOfInverseCoefficientCharacter ψ hψ
          ).operator q z) =
      (R.fixedFiniteMultiplicityQuotientProjective
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
      (R.fixedFiniteMultiplicityQuotientProjective
        (R.inverseCoefficientTensorCharacter ψ hψ)
        (R.inverseCoefficientTensorCharacter_liesOver ψ hψ)
        ).operator (QuotientGroup.mk' T.normalSubgroup a)
        (R.inverseCoefficientMultiplicityRecoveryEquiv ψ hψ z)
  rw [fixedFiniteMultiplicityQuotientProjective,
    ProjectiveRepresentation.quotientDescent_operator_mk]
  exact
    R.inverseCoefficientMultiplicityRecoveryEquiv_intertwines
      ψ hψ a z

/-- Multiplicity recovery upgrades to an equivalence between the original
extension realization and the forward extension representation of the
inverse ambient character. -/
def inverseCoefficientRealizationEquivForwardExtension
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
    (hψ : R.HasInverseCoefficientCharacter ψ) :
    Representation.Equiv ψ.realization.ρ
      (R.fixedFiniteMultiplicityExtensionRepresentation
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
            R.fixedFiniteQuotientFactorSet
            R.fixedFiniteQuotientFactorSet_isNormalized
            (inverseRootsOfUnityCoefficientHom
              (R.exponent))
            (R.inverseCoefficientHom_quotientFactorSet_eq_projectiveFactor
              ψ hψ) x z) =
      (R.fixedFiniteMultiplicityExtensionRepresentation
        (R.inverseCoefficientTensorCharacter ψ hψ)
        (R.inverseCoefficientTensorCharacter_liesOver ψ hψ)) x (e z)
  rw [fixedFiniteMultiplicityExtensionRepresentation,
    ProjectiveRepresentation.centralExtensionRepresentation_apply_vector,
    ProjectiveRepresentation.centralExtensionRepresentation_apply_vector,
    map_smul]
  exact congrArg
    (fun y ↦
      (inverseRootsOfUnityCoefficientHom
        (R.exponent)
        (FactorSet.CentralExtensionGroup.coefficient
          R.fixedFiniteQuotientFactorSet
          R.fixedFiniteQuotientFactorSet_isNormalized x) : ℂ) • y)
    (R.inverseCoefficientMultiplicityRecoveryEquiv_intertwines_quotient
      ψ hψ
      (FactorSet.CentralExtensionGroup.base
        R.fixedFiniteQuotientFactorSet
        R.fixedFiniteQuotientFactorSet_isNormalized x) z)

/-- Applying the forward map to the inverse tensor character recovers the
original coefficient-compatible extension character. -/
theorem fixedFiniteFactorCharacterMap_inverseFixedFiniteFactorCharacterMap
    (R : FixedFiniteFactorData T V)
    (ψ : R.InverseCoefficientCharacters) :
    R.fixedFiniteFactorCharacterMap
        (R.inverseFixedFiniteFactorCharacterMap ψ) =
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
      (R.fixedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.fixedFiniteMultiplicityExtensionFDRep_simple χ hχ
  change
    (R.fixedFiniteMultiplicityExtensionFDRep χ hχ).character x =
      ψ.1.values x
  calc
    (R.fixedFiniteMultiplicityExtensionFDRep χ hχ).character x =
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
def fixedFiniteFactorCharacterEquiv
    (R : FixedFiniteFactorData T V) :
    R.AssociatedCharactersOver ≃
      R.InverseCoefficientCharacters where
  toFun := R.fixedFiniteFactorCharacterMap
  invFun := R.inverseFixedFiniteFactorCharacterMap
  left_inv :=
    R.inverseFixedFiniteFactorCharacterMap_fixedFiniteFactorCharacterMap
  right_inv :=
    R.fixedFiniteFactorCharacterMap_inverseFixedFiniteFactorCharacterMap

@[simp]
theorem fixedFiniteFactorCharacterEquiv_apply
    (R : FixedFiniteFactorData T V)
    (χ : R.AssociatedCharactersOver) :
    R.fixedFiniteFactorCharacterEquiv χ =
      R.fixedFiniteFactorCharacterMap χ :=
  rfl

@[simp]
theorem fixedFiniteFactorCharacterEquiv_symm_apply
    (R : FixedFiniteFactorData T V)
    (ψ : R.InverseCoefficientCharacters) :
    R.fixedFiniteFactorCharacterEquiv.symm ψ =
      R.inverseFixedFiniteFactorCharacterMap ψ :=
  rfl

/-- Prime-to-`p` characters in the source of the finite-factor
correspondence. -/
abbrev AssociatedPPrimeCharactersOver
    (R : FixedFiniteFactorData T V) (p : ℕ) :=
  {χ : R.AssociatedCharactersOver // χ.1.IsPPrimeDegree p}

/-- Prime-to-`p` inverse-coefficient characters of the finite factor
extension. -/
abbrev InverseCoefficientPPrimeCharacters
    (R : FixedFiniteFactorData T V) (p : ℕ) :=
  {ψ : R.InverseCoefficientCharacters // ψ.val.IsPPrimeDegree p}

/-- If the triple character has prime-to-`p` degree, the forward map
preserves and reflects prime-to-`p` degree. -/
theorem fixedFiniteMultiplicityExtensionCharacter_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (hT : T.character.IsPPrimeDegree p) :
    (R.fixedFiniteMultiplicityExtensionCharacter χ hχ
      ).IsPPrimeDegree p ↔
      χ.IsPPrimeDegree p := by
  have hT' : ¬p ∣ T.character.degree := hT
  rw [IrreducibleCharacter.IsPPrimeDegree,
    IrreducibleCharacter.IsPPrimeDegree,
    ← R.fixedFiniteMultiplicityExtensionCharacter_degree_mul χ hχ,
    hp.dvd_mul, not_or]
  simp [hT']

/-- The inverse tensor has prime-to-`p` degree exactly when its extension
character does, provided the triple character has prime-to-`p` degree. -/
theorem inverseCoefficientTensorCharacter_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (R : FixedFiniteFactorData T V)
    (ψ : IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup)
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
def fixedFiniteFactorPPrimeCharacterEquiv
    {p : ℕ} (hp : p.Prime)
    (R : FixedFiniteFactorData T V)
    (hT : T.character.IsPPrimeDegree p) :
    R.AssociatedPPrimeCharactersOver p ≃
      R.InverseCoefficientPPrimeCharacters p where
  toFun χ :=
    ⟨R.fixedFiniteFactorCharacterMap χ.1,
      (R.fixedFiniteMultiplicityExtensionCharacter_isPPrime_iff
        hp χ.1.1 χ.1.2 hT).mpr χ.2⟩
  invFun ψ :=
    ⟨R.inverseFixedFiniteFactorCharacterMap ψ.1,
      (R.inverseCoefficientTensorCharacter_isPPrime_iff
        hp ψ.1.1 ψ.1.2 hT).mpr ψ.2⟩
  left_inv χ := by
    apply Subtype.ext
    exact
      R.inverseFixedFiniteFactorCharacterMap_fixedFiniteFactorCharacterMap
        χ.1
  right_inv ψ := by
    apply Subtype.ext
    exact
      R.fixedFiniteFactorCharacterMap_inverseFixedFiniteFactorCharacterMap
        ψ.1

@[simp]
theorem fixedFiniteFactorPPrimeCharacterEquiv_apply_value
    {p : ℕ} (hp : p.Prime)
    (R : FixedFiniteFactorData T V)
    (hT : T.character.IsPPrimeDegree p)
    (χ : R.AssociatedPPrimeCharactersOver p) :
    (R.fixedFiniteFactorPPrimeCharacterEquiv hp hT χ).1 =
      R.fixedFiniteFactorCharacterMap χ.1 :=
  rfl

@[simp]
theorem fixedFiniteFactorPPrimeCharacterEquiv_symm_apply_value
    {p : ℕ} (hp : p.Prime)
    (R : FixedFiniteFactorData T V)
    (hT : T.character.IsPPrimeDegree p)
    (ψ : R.InverseCoefficientPPrimeCharacters p) :
    ((R.fixedFiniteFactorPPrimeCharacterEquiv hp hT).symm ψ).1 =
      R.inverseFixedFiniteFactorCharacterMap ψ.1 :=
  rfl

end FixedFiniteFactorData
end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
