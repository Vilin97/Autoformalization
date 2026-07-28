/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FixedFiniteFactorData
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
namespace FixedFiniteFactorData

variable {A : Type} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- The multiplicity space of `χ` relative to the finite-normalized
associated lift. -/
abbrev FixedFiniteMultiplicitySpace
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A) :=
  MultiplicityProjective.Space
    R.fixedFiniteFactorAssociated χ.realization.ρ

/-- The inverse-factor projective action on the finite-normalized
multiplicity space. -/
abbrev fixedFiniteMultiplicityProjective
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A) :
    ProjectiveRepresentation ℂ A
      (R.FixedFiniteMultiplicitySpace χ) :=
  MultiplicityProjective.projective
    R.fixedFiniteFactorAssociated χ.realization.ρ

/-- Lying over the character of the triple makes the finite-normalized
multiplicity space nonzero. -/
theorem fixedFiniteMultiplicitySpace_nontrivial
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Nontrivial (R.FixedFiniteMultiplicitySpace χ) :=
  MultiplicityProjective.space_nontrivial_of_liesOver
    R.fixedFiniteFactorAssociated χ hχ

/-- The multiplicity action has factor inverse to the finite-normalized
associated action. -/
theorem fixedFiniteMultiplicity_hasInverseFactorSet
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A) :
    R.fixedFiniteFactorProjective.HasInverseFactorSet
      (R.fixedFiniteMultiplicityProjective χ) :=
  MultiplicityProjective.hasInverseFactorSet
    R.fixedFiniteFactorAssociated χ.realization.ρ

/-- The chosen multiplicity operators are the identity on the normal
subgroup. -/
theorem fixedFiniteMultiplicity_isTrivialOnNormal
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A) :
    (R.fixedFiniteMultiplicityProjective χ).IsTrivialOnNormal T :=
  MultiplicityProjective.projective_operator_normal
    R.fixedFiniteFactorAssociated χ.realization.ρ

/-- The inverse-factor multiplicity action, including its chosen operators,
is compatible with descent to `A / N`. -/
theorem fixedFiniteMultiplicity_isQuotientCompatible
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A) :
    (R.fixedFiniteMultiplicityProjective χ).IsQuotientCompatible
      T.normalSubgroup where
  factor_normal_left x a := by
    rw [MultiplicityProjective.projective_factor,
      R.fixedFiniteFactorAssociated.factor_normal_left]
    exact inv_one
  factor_normal_right a x := by
    rw [MultiplicityProjective.projective_factor,
      R.fixedFiniteFactorAssociated.factor_normal_right]
    exact inv_one
  operator_normal :=
    R.fixedFiniteMultiplicity_isTrivialOnNormal χ

/-- The exact multiplicity projective representation descended to `A / N`.
The lying-over witness is retained explicitly because it supplies the
nonzero carrier needed by the subsequent character construction. -/
def fixedFiniteMultiplicityQuotientProjective
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (_hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    ProjectiveRepresentation ℂ (A ⧸ T.normalSubgroup)
      (R.FixedFiniteMultiplicitySpace χ) :=
  (R.fixedFiniteMultiplicityProjective χ).quotientDescent
    T.normalSubgroup
    (R.fixedFiniteMultiplicity_isQuotientCompatible χ)

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
theorem fixedFiniteMultiplicityQuotient_factor
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (q r : A ⧸ T.normalSubgroup) :
    inverseRootsOfUnityCoefficientHom (R.exponent)
        (R.fixedFiniteQuotientFactorSet q r) =
      (R.fixedFiniteMultiplicityQuotientProjective χ hχ).factor
        q r := by
  letI : Nontrivial (R.FixedFiniteMultiplicitySpace χ) :=
    R.fixedFiniteMultiplicitySpace_nontrivial χ hχ
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective T.normalSubgroup q
  obtain ⟨b, rfl⟩ :=
    QuotientGroup.mk'_surjective T.normalSubgroup r
  rw [inverseRootsOfUnityCoefficientHom_apply,
    R.fixedFiniteQuotientFactorSet_mk_coe,
    fixedFiniteMultiplicityQuotientProjective,
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
theorem fixedFiniteMultiplicityProjective_isIrreducible
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.fixedFiniteMultiplicityProjective χ).IsIrreducible := by
  letI : Nontrivial (R.FixedFiniteMultiplicitySpace χ) :=
    R.fixedFiniteMultiplicitySpace_nontrivial χ hχ
  have htensor :
      (R.fixedFiniteFactorProjective.cancelTensorRepresentation
        (R.fixedFiniteMultiplicityProjective χ)
        (R.fixedFiniteMultiplicity_hasInverseFactorSet χ)
        ).IsIrreducible :=
    representationIsIrreducibleOfEquiv
      (CliffordRestriction.isIrreducible_of_simple
        χ.realization)
      (MultiplicityProjective.evaluationRepresentationEquivOfLiesOver
        R.fixedFiniteFactorAssociated χ hχ).symm
  exact
    (R.fixedFiniteFactorAssociated.cancelTensorRepresentation_isIrreducible_iff
        (R.fixedFiniteMultiplicityProjective χ)
        (R.fixedFiniteMultiplicity_hasInverseFactorSet χ)
        (R.fixedFiniteMultiplicity_isTrivialOnNormal χ)).mp
      htensor

/-- The exact quotient descent of the multiplicity action remains
irreducible. -/
theorem fixedFiniteMultiplicityQuotientProjective_isIrreducible
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.fixedFiniteMultiplicityQuotientProjective χ hχ
      ).IsIrreducible := by
  letI : Nontrivial (R.FixedFiniteMultiplicitySpace χ) :=
    R.fixedFiniteMultiplicitySpace_nontrivial χ hχ
  exact
    ((R.fixedFiniteMultiplicityProjective χ
      ).quotientDescent_isIrreducible_iff
        (R.fixedFiniteMultiplicity_isQuotientCompatible χ)).mpr
      (R.fixedFiniteMultiplicityProjective_isIrreducible χ hχ)

/-- The honest representation of the finite quotient-factor extension
afforded by the descended multiplicity action.  The coefficient subgroup
acts through inverse roots of unity. -/
def fixedFiniteMultiplicityExtensionRepresentation
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation ℂ R.FixedFiniteFactorCentralExtensionGroup
      (R.FixedFiniteMultiplicitySpace χ) :=
  (R.fixedFiniteMultiplicityQuotientProjective χ hχ
    ).centralExtensionRepresentation
      R.fixedFiniteQuotientFactorSet
      R.fixedFiniteQuotientFactorSet_isNormalized
      (inverseRootsOfUnityCoefficientHom
        (R.exponent))
      (R.fixedFiniteMultiplicityQuotient_factor χ hχ)

/-- The honest extension representation obtained from multiplicity is
irreducible. -/
theorem fixedFiniteMultiplicityExtensionRepresentation_isIrreducible
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation.IsIrreducible
      (R.fixedFiniteMultiplicityExtensionRepresentation χ hχ) := by
  letI : Nontrivial (R.FixedFiniteMultiplicitySpace χ) :=
    R.fixedFiniteMultiplicitySpace_nontrivial χ hχ
  exact
    (R.fixedFiniteMultiplicityQuotientProjective χ hχ
      ).centralExtensionRepresentation_isIrreducible
        R.fixedFiniteQuotientFactorSet
        R.fixedFiniteQuotientFactorSet_isNormalized
        (inverseRootsOfUnityCoefficientHom
          (R.exponent))
        (R.fixedFiniteMultiplicityQuotient_factor χ hχ)
        (R.fixedFiniteMultiplicityQuotientProjective_isIrreducible
          χ hχ)

/-- The finite-dimensional representation underlying the multiplicity
extension character. -/
abbrev fixedFiniteMultiplicityExtensionFDRep
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    FDRep ℂ R.FixedFiniteFactorCentralExtensionGroup :=
  FDRep.of
    (R.fixedFiniteMultiplicityExtensionRepresentation χ hχ)

/-- The finite-dimensional multiplicity extension representation is
categorically simple. -/
theorem fixedFiniteMultiplicityExtensionFDRep_simple
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Simple (R.fixedFiniteMultiplicityExtensionFDRep χ hχ) := by
  letI : Representation.IsIrreducible
      (R.fixedFiniteMultiplicityExtensionRepresentation χ hχ) :=
    R.fixedFiniteMultiplicityExtensionRepresentation_isIrreducible
      χ hχ
  exact
    FDRep.simple_of_representation_isIrreducible
      (R.fixedFiniteMultiplicityExtensionRepresentation χ hχ)

/-- The irreducible character of the associated finite factor extension
obtained from `χ` by the multiplicity-space construction. -/
def fixedFiniteMultiplicityExtensionCharacter
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    IrreducibleCharacter
      R.FixedFiniteFactorCentralExtensionGroup := by
  letI : Simple
      (R.fixedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.fixedFiniteMultiplicityExtensionFDRep_simple χ hχ
  exact
    IrreducibleCharacter.ofSimple
      (R.fixedFiniteMultiplicityExtensionFDRep χ hχ)

/-- The degree of the extension character is the dimension of the
multiplicity space. -/
@[simp]
theorem fixedFiniteMultiplicityExtensionCharacter_degree
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.fixedFiniteMultiplicityExtensionCharacter χ hχ).degree =
      Module.finrank ℂ (R.FixedFiniteMultiplicitySpace χ) := by
  letI : Simple
      (R.fixedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.fixedFiniteMultiplicityExtensionFDRep_simple χ hχ
  rfl

/-- The extension-character degree times the degree of the triple character
is the degree of the original ambient character. -/
theorem fixedFiniteMultiplicityExtensionCharacter_degree_mul
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.fixedFiniteMultiplicityExtensionCharacter χ hχ).degree *
        T.character.degree =
      χ.degree := by
  have hnonzero :
      ∃ f : T.character.realization ⟶
        FDRep.res T.normalSubgroup.subtype χ.realization,
        f ≠ 0 :=
    (CliffordCorrespondence.liesOverAlong_iff_exists_nonzero
      T.normalSubgroup.subtype T.character χ).mp hχ
  simpa only [
      R.fixedFiniteMultiplicityExtensionCharacter_degree χ hχ,
      R.fixedFiniteFactorAssociated.finrank_eq_character_degree,
      χ.realization_finrank] using
    (MultiplicityProjective.finrank_space_mul_finrank_eq
      R.fixedFiniteFactorAssociated χ.realization hnonzero)

/-- Quotient form of the multiplicity degree formula. -/
theorem fixedFiniteMultiplicityExtensionCharacter_degree_eq_div
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (R.fixedFiniteMultiplicityExtensionCharacter χ hχ).degree =
      χ.degree / T.character.degree :=
  Nat.eq_div_of_mul_eq_left T.character.degree_ne_zero
    (R.fixedFiniteMultiplicityExtensionCharacter_degree_mul χ hχ)

/-- Restriction to the canonical coefficient subgroup has the inverse
scalar character. -/
theorem fixedFiniteMultiplicityExtensionFDRep_restrictCoefficient_character
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (FDRep.res
      (FactorSet.CentralExtensionGroup.coefficientEmbedding
        R.fixedFiniteQuotientFactorSet
        R.fixedFiniteQuotientFactorSet_isNormalized)
      (R.fixedFiniteMultiplicityExtensionFDRep χ hχ)).character =
        fun a :
            rootsOfUnity (R.exponent) ℂ ↦
          (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
            (Module.finrank ℂ
              (R.FixedFiniteMultiplicitySpace χ) : ℂ) := by
  funext a
  change
    LinearMap.trace ℂ (R.FixedFiniteMultiplicitySpace χ)
        (R.fixedFiniteMultiplicityExtensionRepresentation χ hχ
          (FactorSet.CentralExtensionGroup.coefficientEmbedding
            R.fixedFiniteQuotientFactorSet
            R.fixedFiniteQuotientFactorSet_isNormalized a)) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        (Module.finrank ℂ
          (R.FixedFiniteMultiplicitySpace χ) : ℂ)
  rw [fixedFiniteMultiplicityExtensionRepresentation,
    ProjectiveRepresentation.centralExtensionRepresentation_apply_coefficientEmbedding]
  have hscalar :
      ((scalarLinearEquiv ℂ
          (R.FixedFiniteMultiplicitySpace χ)
          (inverseRootsOfUnityCoefficientHom
            (R.exponent) a) :
            R.FixedFiniteMultiplicitySpace χ ≃ₗ[ℂ]
              R.FixedFiniteMultiplicitySpace χ) :
          R.FixedFiniteMultiplicitySpace χ →ₗ[ℂ]
            R.FixedFiniteMultiplicitySpace χ) =
        (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) •
          (LinearMap.id :
            Module.End ℂ
              (R.FixedFiniteMultiplicitySpace χ)) := by
    ext z x
    rfl
  rw [hscalar, map_smul, LinearMap.trace_id]
  rfl

/-- On the coefficient subgroup, the multiplicity extension character is
the inverse defining scalar times its degree. -/
@[simp]
theorem fixedFiniteMultiplicityExtensionCharacter_values_coefficientEmbedding
    (R : FixedFiniteFactorData T V)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (a : rootsOfUnity (R.exponent) ℂ) :
    (R.fixedFiniteMultiplicityExtensionCharacter χ hχ).values
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.fixedFiniteQuotientFactorSet
          R.fixedFiniteQuotientFactorSet_isNormalized a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        (R.fixedFiniteMultiplicityExtensionCharacter χ hχ).degree := by
  letI : Simple
      (R.fixedFiniteMultiplicityExtensionFDRep χ hχ) :=
    R.fixedFiniteMultiplicityExtensionFDRep_simple χ hχ
  change
    (R.fixedFiniteMultiplicityExtensionFDRep χ hχ).character
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          R.fixedFiniteQuotientFactorSet
          R.fixedFiniteQuotientFactorSet_isNormalized a) =
      (((a : ℂˣ)⁻¹ : ℂˣ) : ℂ) *
        Module.finrank ℂ (R.FixedFiniteMultiplicitySpace χ)
  exact congrFun
    (R.fixedFiniteMultiplicityExtensionFDRep_restrictCoefficient_character
      χ hχ) a

end FixedFiniteFactorData
end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
