/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorQuotient
import McKayConjecture.CharacterTriple.AssociatedTensorIrreducible
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionCharacter
import McKayConjecture.CharacterTriple.MultiplicityReconstruction

/-!
# Multiplicity characters on associated finite factor extensions

Let `R` be an associated projective representation for a character triple
`T = (A, N, ζ)`, after the canonical finite-factor normalization.  For an
irreducible character `χ` of `A` lying over `ζ`, its multiplicity space
carries a projective representation whose factor is the inverse of the
factor of `R`.

The multiplicity action is exactly trivial on `N`, so it descends to `A / N`.
The descended inverse factor is linearized on the finite central extension
attached to the factor of `R`: the coefficient group acts through the
inverse of its canonical embedding in `ℂˣ`.  This file packages the resulting
irreducible character and records its degree and coefficient-subgroup
character formulas.

Only the forward construction is made here; no bijectivity claim is needed.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

universe u v w

namespace McKayConjecture
namespace CharacterTriple

namespace ProjectiveRepresentation

variable {K : Type u} {G : Type v} {Z : Type w}
variable [Field K] [Group G]
variable [AddCommGroup Z] [Module K Z] [Nontrivial Z]
variable {N : Subgroup G} [N.Normal]

/-- Exact quotient descent preserves projective irreducibility. -/
theorem quotientDescent_isIrreducible_iff
    (Q : ProjectiveRepresentation K G Z)
    (hQ : Q.IsQuotientCompatible N) :
    (Q.quotientDescent N hQ).IsIrreducible ↔ Q.IsIrreducible := by
  let Qbar := Q.quotientDescent N hQ
  have hcovered :
      Qbar.OperatorsCoveredBy (QuotientGroup.mk' N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    exact ⟨g, rfl⟩
  rw [Qbar.isIrreducible_iff_comap
    (QuotientGroup.mk' N) hcovered]
  exact iff_of_eq
    (congrArg IsIrreducible (Q.quotientDescent_comap hQ))

end ProjectiveRepresentation

namespace AssociatedProjectiveRepresentation

variable {A : Type} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- The multiplicity space of `χ` relative to the finite-normalized
associated lift. -/
abbrev AssociatedFiniteMultiplicitySpace
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A) :=
  MultiplicityProjective.Space
    R.associatedFiniteFactorAssociated χ.realization.ρ

/-- The inverse-factor projective action on the finite-normalized
multiplicity space. -/
abbrev associatedFiniteMultiplicityProjective
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A) :
    ProjectiveRepresentation ℂ A
      (R.AssociatedFiniteMultiplicitySpace χ) :=
  MultiplicityProjective.projective
    R.associatedFiniteFactorAssociated χ.realization.ρ

/-- Lying over the character of the triple makes the finite-normalized
multiplicity space nonzero. -/
theorem associatedFiniteMultiplicitySpace_nontrivial
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Nontrivial (R.AssociatedFiniteMultiplicitySpace χ) :=
  MultiplicityProjective.space_nontrivial_of_liesOver
    R.associatedFiniteFactorAssociated χ hχ

/-- The multiplicity action has factor inverse to the finite-normalized
associated action. -/
theorem associatedFiniteMultiplicity_hasInverseFactorSet
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A) :
    R.associatedFiniteFactorProjective.HasInverseFactorSet
      (R.associatedFiniteMultiplicityProjective χ) :=
  MultiplicityProjective.hasInverseFactorSet
    R.associatedFiniteFactorAssociated χ.realization.ρ

/-- The chosen multiplicity operators are the identity on the normal
subgroup. -/
theorem associatedFiniteMultiplicity_isTrivialOnNormal
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A) :
    (R.associatedFiniteMultiplicityProjective χ).IsTrivialOnNormal T :=
  MultiplicityProjective.projective_operator_normal
    R.associatedFiniteFactorAssociated χ.realization.ρ

/-- The inverse-factor multiplicity action, including its chosen operators,
is compatible with descent to `A / N`. -/
theorem associatedFiniteMultiplicity_isQuotientCompatible
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A) :
    (R.associatedFiniteMultiplicityProjective χ).IsQuotientCompatible
      T.normalSubgroup where
  factor_normal_left x a := by
    rw [MultiplicityProjective.projective_factor,
      R.associatedFiniteFactorAssociated.factor_normal_left]
    exact inv_one
  factor_normal_right a x := by
    rw [MultiplicityProjective.projective_factor,
      R.associatedFiniteFactorAssociated.factor_normal_right]
    exact inv_one
  operator_normal :=
    R.associatedFiniteMultiplicity_isTrivialOnNormal χ

/-- The exact multiplicity projective representation descended to `A / N`.
The lying-over witness is retained explicitly because it supplies the
nonzero carrier needed by the subsequent character construction. -/
def associatedFiniteMultiplicityQuotientProjective
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (_hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    ProjectiveRepresentation ℂ (A ⧸ T.normalSubgroup)
      (R.AssociatedFiniteMultiplicitySpace χ) :=
  (R.associatedFiniteMultiplicityProjective χ).quotientDescent
    T.normalSubgroup
    (R.associatedFiniteMultiplicity_isQuotientCompatible χ)

/-- Inversion after the canonical roots-of-unity embedding. -/
def inverseRootsOfUnityCoefficientHom (n : ℕ) :
    rootsOfUnity n ℂ →* ℂˣ :=
  (invMonoidHom : ℂˣ →* ℂˣ).comp
    (rootsOfUnity n ℂ).subtype

@[simp]
theorem inverseRootsOfUnityCoefficientHom_apply
    (n : ℕ) (a : rootsOfUnity n ℂ) :
    inverseRootsOfUnityCoefficientHom n a = (a : ℂˣ)⁻¹ :=
  rfl

/-- The descended multiplicity factor is exactly the inverse image of the
finite quotient factor under the roots-of-unity embedding. -/
theorem associatedFiniteMultiplicityQuotient_factor
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (q r : A ⧸ T.normalSubgroup) :
    inverseRootsOfUnityCoefficientHom (associatedFactorExponent T V)
        (R.associatedFiniteQuotientFactorSet q r) =
      (R.associatedFiniteMultiplicityQuotientProjective χ hχ).factor
        q r := by
  letI : Nontrivial (R.AssociatedFiniteMultiplicitySpace χ) :=
    R.associatedFiniteMultiplicitySpace_nontrivial χ hχ
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective T.normalSubgroup q
  obtain ⟨b, rfl⟩ :=
    QuotientGroup.mk'_surjective T.normalSubgroup r
  rw [inverseRootsOfUnityCoefficientHom_apply,
    R.associatedFiniteQuotientFactorSet_mk_coe,
    associatedFiniteMultiplicityQuotientProjective,
    ProjectiveRepresentation.quotientDescent_factor_mk,
    MultiplicityProjective.projective_factor]

/-- Irreducibility transports across an equivalence of complex
representations.  This local universe-polymorphic form avoids imposing any
extra restriction on the carrier spaces used below. -/
private theorem representationIsIrreducibleOfEquiv
    {G : Type u} {X : Type v} {Y : Type w} [Group G]
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (hρ : ρ.IsIrreducible) (e : ρ.Equiv σ) :
    σ.IsIrreducible := by
  have hsimple :
      IsSimpleModule ℂ[G] ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  let L : ρ.asModule ≃ₗ[ℂ[G]] σ.asModule :=
    LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule
        ρ σ e.toIntertwiningMap)
      e.toLinearEquiv.bijective
  exact IsSimpleModule.congr L.symm

/-- The finite-normalized multiplicity projective representation is
irreducible. -/
theorem associatedFiniteMultiplicityProjective_isIrreducible
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.associatedFiniteMultiplicityProjective χ).IsIrreducible := by
  letI : Nontrivial (R.AssociatedFiniteMultiplicitySpace χ) :=
    R.associatedFiniteMultiplicitySpace_nontrivial χ hχ
  have htensor :
      (R.associatedFiniteFactorProjective.cancelTensorRepresentation
        (R.associatedFiniteMultiplicityProjective χ)
        (R.associatedFiniteMultiplicity_hasInverseFactorSet χ)
        ).IsIrreducible :=
    representationIsIrreducibleOfEquiv
      (CliffordRestriction.isIrreducible_of_simple
        χ.realization)
      (MultiplicityProjective.evaluationRepresentationEquivOfLiesOver
        R.associatedFiniteFactorAssociated χ hχ).symm
  exact
    (R.associatedFiniteFactorAssociated.cancelTensorRepresentation_isIrreducible_iff
        (R.associatedFiniteMultiplicityProjective χ)
        (R.associatedFiniteMultiplicity_hasInverseFactorSet χ)
        (R.associatedFiniteMultiplicity_isTrivialOnNormal χ)).mp
      htensor

/-- The exact quotient descent of the multiplicity action remains
irreducible. -/
theorem associatedFiniteMultiplicityQuotientProjective_isIrreducible
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.associatedFiniteMultiplicityQuotientProjective χ hχ
      ).IsIrreducible := by
  letI : Nontrivial (R.AssociatedFiniteMultiplicitySpace χ) :=
    R.associatedFiniteMultiplicitySpace_nontrivial χ hχ
  exact
    ((R.associatedFiniteMultiplicityProjective χ
      ).quotientDescent_isIrreducible_iff
        (R.associatedFiniteMultiplicity_isQuotientCompatible χ)).mpr
      (R.associatedFiniteMultiplicityProjective_isIrreducible χ hχ)

/-- The honest representation of the finite quotient-factor extension
afforded by the descended multiplicity action.  The coefficient subgroup
acts through inverse roots of unity. -/
def associatedFiniteMultiplicityExtensionRepresentation
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation ℂ R.AssociatedFiniteFactorCentralExtensionGroup
      (R.AssociatedFiniteMultiplicitySpace χ) :=
  (R.associatedFiniteMultiplicityQuotientProjective χ hχ
    ).centralExtensionRepresentation
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized
      (inverseRootsOfUnityCoefficientHom
        (associatedFactorExponent T V))
      (R.associatedFiniteMultiplicityQuotient_factor χ hχ)

/-- The honest extension representation obtained from multiplicity is
irreducible. -/
theorem associatedFiniteMultiplicityExtensionRepresentation_isIrreducible
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation.IsIrreducible
      (R.associatedFiniteMultiplicityExtensionRepresentation χ hχ) := by
  letI : Nontrivial (R.AssociatedFiniteMultiplicitySpace χ) :=
    R.associatedFiniteMultiplicitySpace_nontrivial χ hχ
  exact
    (R.associatedFiniteMultiplicityQuotientProjective χ hχ
      ).centralExtensionRepresentation_isIrreducible
        R.associatedFiniteQuotientFactorSet
        R.associatedFiniteQuotientFactorSet_isNormalized
        (inverseRootsOfUnityCoefficientHom
          (associatedFactorExponent T V))
        (R.associatedFiniteMultiplicityQuotient_factor χ hχ)
        (R.associatedFiniteMultiplicityQuotientProjective_isIrreducible
          χ hχ)

/-- The finite-dimensional representation underlying the multiplicity
extension character. -/
abbrev associatedFiniteMultiplicityExtensionFDRep
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    FDRep ℂ R.AssociatedFiniteFactorCentralExtensionGroup :=
  FDRep.of
    (R.associatedFiniteMultiplicityExtensionRepresentation χ hχ)

/-- The finite-dimensional multiplicity extension representation is
categorically simple. -/
theorem associatedFiniteMultiplicityExtensionFDRep_simple
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Simple (R.associatedFiniteMultiplicityExtensionFDRep χ hχ) := by
  letI : Representation.IsIrreducible
      (R.associatedFiniteMultiplicityExtensionRepresentation χ hχ) :=
    R.associatedFiniteMultiplicityExtensionRepresentation_isIrreducible
      χ hχ
  exact
    FDRep.simple_of_representation_isIrreducible
      (R.associatedFiniteMultiplicityExtensionRepresentation χ hχ)

/-- The irreducible character of the associated finite factor extension
obtained from `χ` by the multiplicity-space construction. -/
def associatedFiniteMultiplicityExtensionCharacter
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    IrreducibleCharacter
      R.AssociatedFiniteFactorCentralExtensionGroup := by
  letI : Simple
      (R.associatedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.associatedFiniteMultiplicityExtensionFDRep_simple χ hχ
  exact
    IrreducibleCharacter.ofSimple
      (R.associatedFiniteMultiplicityExtensionFDRep χ hχ)

/-- The degree of the extension character is the dimension of the
multiplicity space. -/
@[simp]
theorem associatedFiniteMultiplicityExtensionCharacter_degree
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.associatedFiniteMultiplicityExtensionCharacter χ hχ).degree =
      Module.finrank ℂ (R.AssociatedFiniteMultiplicitySpace χ) := by
  letI : Simple
      (R.associatedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.associatedFiniteMultiplicityExtensionFDRep_simple χ hχ
  rfl

/-- The extension-character degree times the degree of the triple character
is the degree of the original ambient character. -/
theorem associatedFiniteMultiplicityExtensionCharacter_degree_mul
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.associatedFiniteMultiplicityExtensionCharacter χ hχ).degree *
        T.character.degree =
      χ.degree := by
  have hnonzero :
      ∃ f : T.character.realization ⟶
        FDRep.res T.normalSubgroup.subtype χ.realization,
        f ≠ 0 :=
    (CliffordCorrespondence.liesOverAlong_iff_exists_nonzero
      T.normalSubgroup.subtype T.character χ).mp hχ
  simpa only [
      R.associatedFiniteMultiplicityExtensionCharacter_degree χ hχ,
      R.associatedFiniteFactorAssociated.finrank_eq_character_degree,
      χ.realization_finrank] using
    (MultiplicityProjective.finrank_space_mul_finrank_eq
      R.associatedFiniteFactorAssociated χ.realization hnonzero)

/-- Quotient form of the multiplicity degree formula. -/
theorem associatedFiniteMultiplicityExtensionCharacter_degree_eq_div
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.associatedFiniteMultiplicityExtensionCharacter χ hχ).degree =
      χ.degree / T.character.degree :=
  Nat.eq_div_of_mul_eq_left T.character.degree_ne_zero
    (R.associatedFiniteMultiplicityExtensionCharacter_degree_mul χ hχ)

/-- Restriction to the canonical coefficient subgroup has the inverse
scalar character. -/
theorem associatedFiniteMultiplicityExtensionFDRep_restrictCoefficient_character
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (FDRep.res
      (FactorSet.CentralExtensionGroup.coefficientEmbedding
        R.associatedFiniteQuotientFactorSet
        R.associatedFiniteQuotientFactorSet_isNormalized)
      (R.associatedFiniteMultiplicityExtensionFDRep χ hχ)).character =
        fun a :
            rootsOfUnity (associatedFactorExponent T V) ℂ ↦
          (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
            (Module.finrank ℂ
              (R.AssociatedFiniteMultiplicitySpace χ) : ℂ) := by
  funext a
  change
    LinearMap.trace ℂ (R.AssociatedFiniteMultiplicitySpace χ)
        (R.associatedFiniteMultiplicityExtensionRepresentation χ hχ
          (FactorSet.CentralExtensionGroup.coefficientEmbedding
            R.associatedFiniteQuotientFactorSet
            R.associatedFiniteQuotientFactorSet_isNormalized a)) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        (Module.finrank ℂ
          (R.AssociatedFiniteMultiplicitySpace χ) : ℂ)
  rw [associatedFiniteMultiplicityExtensionRepresentation,
    ProjectiveRepresentation.centralExtensionRepresentation_apply_coefficientEmbedding]
  have hscalar :
      ((scalarLinearEquiv ℂ
          (R.AssociatedFiniteMultiplicitySpace χ)
          (inverseRootsOfUnityCoefficientHom
            (associatedFactorExponent T V) a) :
            R.AssociatedFiniteMultiplicitySpace χ ≃ₗ[ℂ]
              R.AssociatedFiniteMultiplicitySpace χ) :
          R.AssociatedFiniteMultiplicitySpace χ →ₗ[ℂ]
            R.AssociatedFiniteMultiplicitySpace χ) =
        (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) •
          (LinearMap.id :
            Module.End ℂ
              (R.AssociatedFiniteMultiplicitySpace χ)) := by
    ext z x
    rfl
  rw [hscalar, map_smul, LinearMap.trace_id]
  rfl

/-- On the coefficient subgroup, the multiplicity extension character is
the inverse defining scalar times its degree. -/
@[simp]
theorem associatedFiniteMultiplicityExtensionCharacter_values_coefficientEmbedding
    (R : AssociatedProjectiveRepresentation T V P)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (a : rootsOfUnity (associatedFactorExponent T V) ℂ) :
    (R.associatedFiniteMultiplicityExtensionCharacter χ hχ).values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.associatedFiniteQuotientFactorSet
          R.associatedFiniteQuotientFactorSet_isNormalized a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        (R.associatedFiniteMultiplicityExtensionCharacter χ hχ).degree := by
  letI : Simple
      (R.associatedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.associatedFiniteMultiplicityExtensionFDRep_simple χ hχ
  change
    (R.associatedFiniteMultiplicityExtensionFDRep χ hχ).character
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.associatedFiniteQuotientFactorSet
          R.associatedFiniteQuotientFactorSet_isNormalized a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        Module.finrank ℂ (R.AssociatedFiniteMultiplicitySpace χ)
  exact congrFun
    (R.associatedFiniteMultiplicityExtensionFDRep_restrictCoefficient_character
      χ hχ) a

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
