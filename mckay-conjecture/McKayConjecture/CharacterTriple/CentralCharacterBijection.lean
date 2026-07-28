/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCharacterCorrespondence
import McKayConjecture.CharacterTriple.CentralProjectiveIntertwiner
import McKayConjecture.CharacterTriple.CentralProjectiveLift
import McKayConjecture.CharacterTriple.MultiplicityTensorRecovery

/-!
# The character bijection of a central character-triple isomorphism

The forward character map is constructed in
`CentralCharacterCorrespondence`.  This file constructs its reverse.  For a
right irreducible character, its projective multiplicity action is lifted
exactly across the quotient isomorphism and tensored with the associated left
projective representation.

The final section identifies the two multiplicity constructions and packages
the mutually inverse maps as equivalences, including their prime-to-`p`
restrictions.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra TensorProduct

namespace McKayConjecture
namespace CharacterTriple

namespace CentralCharacterCorrespondence

variable {G : Type} [Group G]

/-- An isomorphism in `FDRep` gives an equivalence of the underlying
representations. -/
def representationEquivOfFDRepIso
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

end CentralCharacterCorrespondence

namespace FactorMatchedIsomorphismWitness

local notation "CentralIsomorphismWitness" =>
  FactorMatchedIsomorphismWitness

variable {A B : Type}
variable [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]

/-- The multiplicity space of a right irreducible character relative to the
associated right projective representation. -/
abbrev rightMultiplicitySpace
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B) :=
  MultiplicityProjective.Space
    C.rightAssociated ψ.realization.ρ

/-- The inverse-factor projective action on the right multiplicity space. -/
abbrev rightMultiplicityProjective
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B) :
    ProjectiveRepresentation ℂ B
      (C.rightMultiplicitySpace ψ) :=
  MultiplicityProjective.projective
    C.rightAssociated ψ.realization.ρ

theorem rightMultiplicity_hasInverseFactorSet
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B) :
    C.rightProjective.HasInverseFactorSet
      (C.rightMultiplicityProjective ψ) :=
  MultiplicityProjective.hasInverseFactorSet
    C.rightAssociated ψ.realization.ρ

theorem rightMultiplicity_isTrivialOnNormal
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B) :
    (C.rightMultiplicityProjective ψ).IsTrivialOnNormal U :=
  MultiplicityProjective.projective_operator_normal
    C.rightAssociated ψ.realization.ρ

theorem rightMultiplicitySpace_nontrivial
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    Nontrivial (C.rightMultiplicitySpace ψ) :=
  MultiplicityProjective.space_nontrivial_of_liesOver
    C.rightAssociated ψ hψ

/-- Evaluation reconstructs a right character from its right multiplicity
space. -/
def rightMultiplicityEvaluationEquiv
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    Representation.Equiv
      (C.rightProjective.cancelTensorRepresentation
        (C.rightMultiplicityProjective ψ)
        (C.rightMultiplicity_hasInverseFactorSet ψ))
      ψ.realization.ρ := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  exact
    MultiplicityProjective.evaluationRepresentationEquivOfLiesOver
      C.rightAssociated ψ hψ

/-- The right multiplicity projective representation is irreducible. -/
theorem rightMultiplicityProjective_isIrreducible
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    (C.rightMultiplicityProjective ψ).IsIrreducible := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  have htensor :
      (C.rightProjective.cancelTensorRepresentation
        (C.rightMultiplicityProjective ψ)
        (C.rightMultiplicity_hasInverseFactorSet ψ)).IsIrreducible :=
    CentralCharacterCorrespondence.isIrreducibleOfEquiv
      (CliffordRestriction.isIrreducible_of_simple
        ψ.realization)
      (C.rightMultiplicityEvaluationEquiv ψ hψ).symm
  exact
    (C.rightAssociated.cancelTensorRepresentation_isIrreducible_iff
      (C.rightMultiplicityProjective ψ)
      (C.rightMultiplicity_hasInverseFactorSet ψ)
      (C.rightMultiplicity_isTrivialOnNormal ψ)).mp
      htensor

/-- Lift the right multiplicity projective action to the left ambient
group. -/
def liftedRightMultiplicityProjective
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (_hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    ProjectiveRepresentation ℂ A
      (C.rightMultiplicitySpace ψ) := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ _hψ
  exact
    C.liftRightProjective
      (C.rightMultiplicityProjective ψ)
      (C.rightMultiplicity_hasInverseFactorSet ψ)
      (C.rightMultiplicity_isTrivialOnNormal ψ)

theorem liftedRightMultiplicity_hasInverseFactorSet
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    C.leftProjective.HasInverseFactorSet
      (C.liftedRightMultiplicityProjective ψ hψ) := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  exact
    C.liftRightProjective_hasInverseFactorSet
      (C.rightMultiplicityProjective ψ)
      (C.rightMultiplicity_hasInverseFactorSet ψ)
      (C.rightMultiplicity_isTrivialOnNormal ψ)

theorem liftedRightMultiplicity_isTrivialOnNormal
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    (C.liftedRightMultiplicityProjective ψ hψ).IsTrivialOnNormal T := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  exact
    C.liftRightProjective_isTrivialOnNormal
      (C.rightMultiplicityProjective ψ)
      (C.rightMultiplicity_hasInverseFactorSet ψ)
      (C.rightMultiplicity_isTrivialOnNormal ψ)

theorem liftedRightMultiplicity_comap
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    (C.liftedRightMultiplicityProjective ψ hψ).comap
        C.embedding =
      C.rightMultiplicityProjective ψ := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  exact
    C.liftRightProjective_comap
      (C.rightMultiplicityProjective ψ)
      (C.rightMultiplicity_hasInverseFactorSet ψ)
      (C.rightMultiplicity_isTrivialOnNormal ψ)

/-- The lifted right multiplicity projective representation remains
irreducible on `A`. -/
theorem liftedRightMultiplicity_isIrreducible
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    (C.liftedRightMultiplicityProjective ψ hψ).IsIrreducible := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  apply
    (C.multiplicity_isIrreducible_iff_comap
      (C.liftedRightMultiplicityProjective ψ hψ)
      (C.liftedRightMultiplicity_hasInverseFactorSet ψ hψ)
      (C.liftedRightMultiplicity_isTrivialOnNormal ψ hψ)).mpr
  rw [C.liftedRightMultiplicity_comap ψ hψ]
  exact C.rightMultiplicityProjective_isIrreducible ψ hψ

/-- The left tensor representation built from a right multiplicity space. -/
def leftMultiplicityFDRep
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    FDRep ℂ A := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  exact
    FDRep.of
      (C.leftProjective.cancelTensorRepresentation
        (C.liftedRightMultiplicityProjective ψ hψ)
        (C.liftedRightMultiplicity_hasInverseFactorSet ψ hψ))

theorem leftMultiplicityFDRep_isIrreducible
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    Representation.IsIrreducible
      (C.leftMultiplicityFDRep ψ hψ).ρ := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  exact
    (C.leftAssociated.cancelTensorRepresentation_isIrreducible_iff
      (C.liftedRightMultiplicityProjective ψ hψ)
      (C.liftedRightMultiplicity_hasInverseFactorSet ψ hψ)
      (C.liftedRightMultiplicity_isTrivialOnNormal ψ hψ)).mpr
      (C.liftedRightMultiplicity_isIrreducible ψ hψ)

theorem leftMultiplicityFDRep_simple
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    Simple (C.leftMultiplicityFDRep ψ hψ) := by
  letI :
      Representation.IsIrreducible
        (C.leftMultiplicityFDRep ψ hψ).ρ :=
    C.leftMultiplicityFDRep_isIrreducible ψ hψ
  exact
    CentralCharacterCorrespondence.simpleFDRepOfIsIrreducible
      (C.leftMultiplicityFDRep ψ hψ).ρ

/-- The irreducible character transported from right to left. -/
def leftMultiplicityCharacter
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    IrreducibleCharacter A := by
  letI : Simple (C.leftMultiplicityFDRep ψ hψ) :=
    C.leftMultiplicityFDRep_simple ψ hψ
  exact IrreducibleCharacter.ofSimple
    (C.leftMultiplicityFDRep ψ hψ)

@[simp]
theorem leftMultiplicityCharacter_values
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    (C.leftMultiplicityCharacter ψ hψ).values =
      (C.leftMultiplicityFDRep ψ hψ).character := by
  letI : Simple (C.leftMultiplicityFDRep ψ hψ) :=
    C.leftMultiplicityFDRep_simple ψ hψ
  rfl

@[simp]
theorem leftMultiplicityCharacter_degree
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    (C.leftMultiplicityCharacter ψ hψ).degree =
      Module.finrank ℂ (C.leftMultiplicityFDRep ψ hψ) := by
  letI : Simple (C.leftMultiplicityFDRep ψ hψ) :=
    C.leftMultiplicityFDRep_simple ψ hψ
  rfl

theorem leftMultiplicityFDRep_finrank
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    Module.finrank ℂ (C.leftMultiplicityFDRep ψ hψ) =
      T.character.degree *
        Module.finrank ℂ (C.rightMultiplicitySpace ψ) := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  change
    Module.finrank ℂ
        (V ⊗[ℂ] C.rightMultiplicitySpace ψ) =
      T.character.degree *
        Module.finrank ℂ (C.rightMultiplicitySpace ψ)
  rw [Module.finrank_tensorProduct,
    C.leftAssociated.finrank_eq_character_degree]

/-- The right tensor source used by evaluation has the degree of `ψ`. -/
theorem rightMultiplicityTensor_finrank
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    Module.finrank ℂ
        (W ⊗[ℂ] C.rightMultiplicitySpace ψ) =
      ψ.degree := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  calc
    Module.finrank ℂ
        (W ⊗[ℂ] C.rightMultiplicitySpace ψ) =
        Module.finrank ℂ ψ.realization :=
      (C.rightMultiplicityEvaluationEquiv ψ hψ).toLinearEquiv.finrank_eq
    _ = ψ.degree := ψ.realization_finrank

/-- Fixing a multiplicity vector embeds the associated left restriction in
the normal restriction of the transported tensor representation. -/
def leftNormalTensorHom
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ)
    (z : C.rightMultiplicitySpace ψ) :
    C.leftAssociated.fdRestriction ⟶
      FDRep.res T.normalSubgroup.subtype
        (C.leftMultiplicityFDRep ψ hψ) := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  let L : V →ₗ[ℂ] V ⊗[ℂ] C.rightMultiplicitySpace ψ :=
    (TensorProduct.mk ℂ V
      (C.rightMultiplicitySpace ψ)).flip z
  refine
    { hom := FGModuleCat.ofHom L
      comm := ?_ }
  intro x
  apply FGModuleCat.hom_ext
  ext v
  change
    L (C.leftAssociated.restriction x v) =
      C.leftProjective.cancelTensorRepresentation
          (C.liftedRightMultiplicityProjective ψ hψ)
          (C.liftedRightMultiplicity_hasInverseFactorSet ψ hψ)
          (x : A) (L v)
  rw [C.leftAssociated.restriction_apply]
  change
    C.leftProjective.operator (x : A) v ⊗ₜ[ℂ] z =
      TensorProduct.congr
        (C.leftProjective.operator (x : A))
        ((C.liftedRightMultiplicityProjective ψ hψ).operator
          (x : A)) (v ⊗ₜ[ℂ] z)
  rw [TensorProduct.congr_tmul]
  have hx :=
    C.liftedRightMultiplicity_isTrivialOnNormal ψ hψ x
  change
    (C.liftedRightMultiplicityProjective ψ hψ).operator
      (x : A) = 1 at hx
  rw [hx]
  rfl

theorem leftNormalTensorHom_ne_zero
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ)
    {z : C.rightMultiplicitySpace ψ} (hz : z ≠ 0) :
    C.leftNormalTensorHom ψ hψ z ≠ 0 := by
  obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ :=
    Module.Projective.exists_dual_eq_one ℂ hz
  intro hzero
  have hlinear :=
    congrArg
      (fun f :
        C.leftAssociated.fdRestriction ⟶
          FDRep.res T.normalSubgroup.subtype
            (C.leftMultiplicityFDRep ψ hψ) ↦
        f.hom.hom)
      hzero
  have happ := ConcreteCategory.congr_hom hlinear v
  change v ⊗ₜ[ℂ] z = 0 at happ
  have hsliced :=
    congrArg
      (fun t : V ⊗[ℂ] C.rightMultiplicitySpace ψ ↦
        TensorProduct.rid ℂ V
          (φ.lTensor V t))
      happ
  simp only [map_zero,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
    hφ, one_smul] at hsliced
  exact hv hsliced

/-- The reverse transported character lies over the prescribed left normal
character. -/
theorem leftMultiplicityCharacter_liesOver
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character
      (C.leftMultiplicityCharacter ψ hψ) := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  letI : Simple (C.leftMultiplicityFDRep ψ hψ) :=
    C.leftMultiplicityFDRep_simple ψ hψ
  obtain ⟨z : C.rightMultiplicitySpace ψ, hz⟩ :=
    exists_ne (0 : C.rightMultiplicitySpace ψ)
  let i :
      C.leftAssociated.fdRestriction ≅
        T.character.realization :=
    MultiplicityProjective.restrictionIsoRealization
      C.leftAssociated
  let fD :
      T.character.realization ⟶
        FDRep.res T.normalSubgroup.subtype
          (C.leftMultiplicityFDRep ψ hψ) :=
    i.inv ≫ C.leftNormalTensorHom ψ hψ z
  have hfD : fD ≠ 0 := by
    intro hfD
    apply C.leftNormalTensorHom_ne_zero ψ hψ hz
    have hzero := congrArg (fun q ↦ i.hom ≫ q) hfD
    simpa [fD, Category.assoc] using hzero
  let χ : IrreducibleCharacter A :=
    C.leftMultiplicityCharacter ψ hψ
  have hchar :
      (C.leftMultiplicityFDRep ψ hψ).character =
        χ.realization.character := by
    rw [χ.realization_character]
    exact (C.leftMultiplicityCharacter_values ψ hψ).symm
  obtain ⟨j :
      C.leftMultiplicityFDRep ψ hψ ≅ χ.realization⟩ :=
    FDRep.nonempty_iso_of_character_eq
      (C.leftMultiplicityFDRep ψ hψ)
      χ.realization hchar
  let jRes :
      FDRep.res T.normalSubgroup.subtype
          (C.leftMultiplicityFDRep ψ hψ) ⟶
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

theorem leftMultiplicityCharacter_degree_eq
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    (C.leftMultiplicityCharacter ψ hψ).degree =
      T.character.degree *
        Module.finrank ℂ (C.rightMultiplicitySpace ψ) := by
  rw [C.leftMultiplicityCharacter_degree]
  exact C.leftMultiplicityFDRep_finrank ψ hψ

theorem leftMultiplicityCharacter_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    (C.leftMultiplicityCharacter ψ hψ).IsPPrimeDegree p ↔
      ψ.IsPPrimeDegree p := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  have htransport :=
    C.tensorDimension_isPPrime_iff
      (Z := C.rightMultiplicitySpace ψ) hp hT hU
  rw [IrreducibleCharacter.IsPPrimeDegree,
    C.leftMultiplicityCharacter_degree]
  change
    (¬p ∣ Module.finrank ℂ
      (V ⊗[ℂ] C.rightMultiplicitySpace ψ)) ↔
      ¬p ∣ ψ.degree
  rw [← C.rightMultiplicityTensor_finrank ψ hψ]
  exact htransport

/-- The explicit reverse map on irreducible characters lying over the
prescribed normal characters. -/
def leftCharacterMap
    (C : CentralIsomorphismWitness T U V W) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        U.normalSubgroup.subtype U.character →
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character :=
  fun ψ ↦
    ⟨C.leftMultiplicityCharacter ψ.1 ψ.2,
      C.leftMultiplicityCharacter_liesOver ψ.1 ψ.2⟩

@[simp]
theorem leftCharacterMap_apply_value
    (C : CentralIsomorphismWitness T U V W)
    (ψ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      U.normalSubgroup.subtype U.character) :
    (C.leftCharacterMap ψ).1 =
      C.leftMultiplicityCharacter ψ.1 ψ.2 :=
  rfl

theorem leftCharacterMap_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (ψ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      U.normalSubgroup.subtype U.character)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    (C.leftCharacterMap ψ).1.IsPPrimeDegree p ↔
      ψ.1.IsPPrimeDegree p :=
  C.leftMultiplicityCharacter_isPPrime_iff
    hp ψ.1 ψ.2 hT hU

/-- The concrete right tensor representation is equivalent to the chosen
realization of the forward transported character. -/
def rightMultiplicityRealizationEquiv
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation.Equiv
      (C.rightMultiplicityFDRep χ hχ).ρ
      (C.rightMultiplicityCharacter χ hχ).realization.ρ := by
  letI : Simple (C.rightMultiplicityFDRep χ hχ) :=
    C.rightMultiplicityFDRep_simple χ hχ
  let ψ := C.rightMultiplicityCharacter χ hχ
  have hchar :
      (C.rightMultiplicityFDRep χ hχ).character =
        ψ.realization.character := by
    rw [ψ.realization_character]
    exact (C.rightMultiplicityCharacter_values χ hχ).symm
  let i :
      C.rightMultiplicityFDRep χ hχ ≅
        ψ.realization :=
    Classical.choice
      (FDRep.nonempty_iso_of_character_eq
        (C.rightMultiplicityFDRep χ hχ)
        ψ.realization hchar)
  exact
    CentralCharacterCorrespondence.representationEquivOfFDRepIso i

/-- Applying the reverse construction to a forward transported character
recovers the original left character. -/
theorem leftMultiplicityCharacter_rightMultiplicityCharacter
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    C.leftMultiplicityCharacter
        (C.rightMultiplicityCharacter χ hχ)
        (C.rightMultiplicityCharacter_liesOver χ hχ) =
      χ := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  let ψ := C.rightMultiplicityCharacter χ hχ
  let hψ :
      CliffordCorrespondence.LiesOverAlong
        U.normalSubgroup.subtype U.character ψ :=
    C.rightMultiplicityCharacter_liesOver χ hχ
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  let Q :=
    C.leftMultiplicityProjective χ
  let QB := Q.comap C.embedding
  let hQB :
      C.rightProjective.HasInverseFactorSet QB :=
    C.right_hasInverseFactorSet Q
      (C.leftMultiplicity_hasInverseFactorSet χ)
  let hQBtriv : QB.IsTrivialOnNormal U :=
    C.right_isTrivialOnNormal Q
      (C.leftMultiplicity_isTrivialOnNormal χ)
  let fB :
      QB.IntertwiningMap
        (C.rightMultiplicityProjective ψ) :=
    MultiplicityProjective.tensorFactorMultiplicityIntertwiningMap
        C.rightAssociated QB hQB hQBtriv
        ψ.realization.ρ
        (C.rightMultiplicityRealizationEquiv χ hχ)
  have hfB : fB.toLinearMap ≠ 0 :=
    MultiplicityProjective.tensorFactorMultiplicityIntertwiningMap_ne_zero
        C.rightAssociated QB hQB hQBtriv
        ψ.realization.ρ
        (C.rightMultiplicityRealizationEquiv χ hχ)
  let R :=
    C.liftedRightMultiplicityProjective ψ hψ
  have hRcomap :
      R.comap C.embedding =
        C.rightMultiplicityProjective ψ :=
    C.liftedRightMultiplicity_comap ψ hψ
  let fB' :
      QB.IntertwiningMap (R.comap C.embedding) :=
    fB.transport rfl hRcomap.symm
  have hfB' : fB'.toLinearMap ≠ 0 := by
    dsimp only [fB']
    rw [ProjectiveRepresentation.IntertwiningMap.transport_toLinearMap]
    exact hfB
  let fA :
      Q.IntertwiningMap R :=
    C.extendProjectiveIntertwiningMap
      Q R
      (C.leftMultiplicity_hasInverseFactorSet χ)
      (C.liftedRightMultiplicity_hasInverseFactorSet ψ hψ)
      (C.leftMultiplicity_isTrivialOnNormal χ)
      (C.liftedRightMultiplicity_isTrivialOnNormal ψ hψ)
      fB'
  have hfA : fA.toLinearMap ≠ 0 := by
    dsimp only [fA]
    rw [C.extendProjectiveIntertwiningMap_toLinearMap]
    exact hfB'
  let eTensor :
      Representation.Equiv
        (C.leftProjective.cancelTensorRepresentation
          Q (C.leftMultiplicity_hasInverseFactorSet χ))
        (C.leftProjective.cancelTensorRepresentation
          R
          (C.liftedRightMultiplicity_hasInverseFactorSet ψ hψ)) :=
    ProjectiveRepresentation.cancelTensorRepresentationEquivOfIntertwiningMap
        C.leftProjective Q R
        (C.leftMultiplicity_hasInverseFactorSet χ)
        (C.liftedRightMultiplicity_hasInverseFactorSet ψ hψ)
        fA
        (C.leftMultiplicityProjective_isIrreducible χ hχ)
        (C.liftedRightMultiplicity_isIrreducible ψ hψ)
        hfA
  let eRecovered :
      Representation.Equiv
        (C.leftMultiplicityFDRep ψ hψ).ρ
        χ.realization.ρ :=
    eTensor.symm.trans
      (C.leftMultiplicityEvaluationEquiv χ hχ)
  apply IrreducibleCharacter.ext
  funext a
  change
    (C.leftMultiplicityFDRep ψ hψ).character a =
      χ.values a
  calc
    (C.leftMultiplicityFDRep ψ hψ).character a =
        χ.realization.character a :=
      congrFun (Representation.char_iso eRecovered) a
    _ = χ.values a :=
      congrFun χ.realization_character a

/-- The reverse map is a left inverse of the forward map. -/
theorem leftCharacterMap_rightCharacterMap
    (C : CentralIsomorphismWitness T U V W)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character) :
    C.leftCharacterMap (C.rightCharacterMap χ) = χ := by
  apply Subtype.ext
  exact
    C.leftMultiplicityCharacter_rightMultiplicityCharacter
      χ.1 χ.2

/-- The concrete left tensor representation is equivalent to the chosen
realization of the reverse transported character. -/
def leftMultiplicityRealizationEquiv
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    Representation.Equiv
      (C.leftMultiplicityFDRep ψ hψ).ρ
      (C.leftMultiplicityCharacter ψ hψ).realization.ρ := by
  letI : Simple (C.leftMultiplicityFDRep ψ hψ) :=
    C.leftMultiplicityFDRep_simple ψ hψ
  let χ := C.leftMultiplicityCharacter ψ hψ
  have hchar :
      (C.leftMultiplicityFDRep ψ hψ).character =
        χ.realization.character := by
    rw [χ.realization_character]
    exact (C.leftMultiplicityCharacter_values ψ hψ).symm
  let i :
      C.leftMultiplicityFDRep ψ hψ ≅
        χ.realization :=
    Classical.choice
      (FDRep.nonempty_iso_of_character_eq
        (C.leftMultiplicityFDRep ψ hψ)
        χ.realization hchar)
  exact
    CentralCharacterCorrespondence.representationEquivOfFDRepIso i

/-- Applying the forward construction to a reverse transported character
recovers the original right character. -/
theorem rightMultiplicityCharacter_leftMultiplicityCharacter
    (C : CentralIsomorphismWitness T U V W)
    (ψ : IrreducibleCharacter B)
    (hψ : CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character ψ) :
    C.rightMultiplicityCharacter
        (C.leftMultiplicityCharacter ψ hψ)
        (C.leftMultiplicityCharacter_liesOver ψ hψ) =
      ψ := by
  letI : Nontrivial (C.rightMultiplicitySpace ψ) :=
    C.rightMultiplicitySpace_nontrivial ψ hψ
  let χ := C.leftMultiplicityCharacter ψ hψ
  let hχ :
      CliffordCorrespondence.LiesOverAlong
        T.normalSubgroup.subtype T.character χ :=
    C.leftMultiplicityCharacter_liesOver ψ hψ
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  let Q :=
    C.rightMultiplicityProjective ψ
  let R :=
    C.liftedRightMultiplicityProjective ψ hψ
  let S :=
    C.leftMultiplicityProjective χ
  let fA :
      R.IntertwiningMap S :=
    MultiplicityProjective.tensorFactorMultiplicityIntertwiningMap
      C.leftAssociated R
      (C.liftedRightMultiplicity_hasInverseFactorSet ψ hψ)
      (C.liftedRightMultiplicity_isTrivialOnNormal ψ hψ)
      χ.realization.ρ
      (C.leftMultiplicityRealizationEquiv ψ hψ)
  have hfA : fA.toLinearMap ≠ 0 :=
    MultiplicityProjective.tensorFactorMultiplicityIntertwiningMap_ne_zero
        C.leftAssociated R
        (C.liftedRightMultiplicity_hasInverseFactorSet ψ hψ)
        (C.liftedRightMultiplicity_isTrivialOnNormal ψ hψ)
        χ.realization.ρ
        (C.leftMultiplicityRealizationEquiv ψ hψ)
  have hRcomap :
      R.comap C.embedding = Q :=
    C.liftedRightMultiplicity_comap ψ hψ
  let fB :
      Q.IntertwiningMap (S.comap C.embedding) :=
    (fA.comap C.embedding).transport hRcomap rfl
  have hfB : fB.toLinearMap ≠ 0 := by
    dsimp only [fB]
    rw [ProjectiveRepresentation.IntertwiningMap.transport_toLinearMap,
      ProjectiveRepresentation.IntertwiningMap.comap_toLinearMap]
    exact hfA
  have hSirr : S.IsIrreducible :=
    C.leftMultiplicityProjective_isIrreducible χ hχ
  have hScomapIrr :
      (S.comap C.embedding).IsIrreducible :=
    (C.multiplicity_isIrreducible_iff_comap
      S
      (C.leftMultiplicity_hasInverseFactorSet χ)
      (C.leftMultiplicity_isTrivialOnNormal χ)).mp
      hSirr
  let eTensor :
      Representation.Equiv
        (C.rightProjective.cancelTensorRepresentation
          Q (C.rightMultiplicity_hasInverseFactorSet ψ))
        (C.rightProjective.cancelTensorRepresentation
          (S.comap C.embedding)
          (C.right_hasInverseFactorSet S
            (C.leftMultiplicity_hasInverseFactorSet χ))) :=
    ProjectiveRepresentation.cancelTensorRepresentationEquivOfIntertwiningMap
      C.rightProjective Q (S.comap C.embedding)
      (C.rightMultiplicity_hasInverseFactorSet ψ)
      (C.right_hasInverseFactorSet S
        (C.leftMultiplicity_hasInverseFactorSet χ))
      fB
      (C.rightMultiplicityProjective_isIrreducible ψ hψ)
      hScomapIrr
      hfB
  let eRecovered :
      Representation.Equiv
        (C.rightMultiplicityFDRep χ hχ).ρ
        ψ.realization.ρ :=
    eTensor.symm.trans
      (C.rightMultiplicityEvaluationEquiv ψ hψ)
  apply IrreducibleCharacter.ext
  funext b
  change
    (C.rightMultiplicityFDRep χ hχ).character b =
      ψ.values b
  calc
    (C.rightMultiplicityFDRep χ hχ).character b =
        ψ.realization.character b :=
      congrFun (Representation.char_iso eRecovered) b
    _ = ψ.values b :=
      congrFun ψ.realization_character b

/-- The forward map is a left inverse of the reverse map. -/
theorem rightCharacterMap_leftCharacterMap
    (C : CentralIsomorphismWitness T U V W)
    (ψ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      U.normalSubgroup.subtype U.character) :
    C.rightCharacterMap (C.leftCharacterMap ψ) = ψ := by
  apply Subtype.ext
  exact
    C.rightMultiplicityCharacter_leftMultiplicityCharacter
      ψ.1 ψ.2

/-- The character correspondence attached to a central isomorphism, as an
explicit equivalence on all irreducible characters lying over the two
distinguished normal characters. -/
def centralCharacterEquiv
    (C : CentralIsomorphismWitness T U V W) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character ≃
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        U.normalSubgroup.subtype U.character where
  toFun := C.rightCharacterMap
  invFun := C.leftCharacterMap
  left_inv := C.leftCharacterMap_rightCharacterMap
  right_inv := C.rightCharacterMap_leftCharacterMap

@[simp]
theorem centralCharacterEquiv_apply
    (C : CentralIsomorphismWitness T U V W)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character) :
    C.centralCharacterEquiv χ = C.rightCharacterMap χ :=
  rfl

@[simp]
theorem centralCharacterEquiv_symm_apply
    (C : CentralIsomorphismWitness T U V W)
    (ψ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      U.normalSubgroup.subtype U.character) :
    C.centralCharacterEquiv.symm ψ = C.leftCharacterMap ψ :=
  rfl

/-- The explicit reverse map restricted to prime-to-`p` characters. -/
def leftPPrimeCharacterMap
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character →
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character :=
  fun ψ ↦
    ⟨C.leftCharacterMap ψ.1,
      (C.leftCharacterMap_isPPrime_iff
        hp ψ.1 hT hU).mpr ψ.2⟩

@[simp]
theorem leftPPrimeCharacterMap_apply_value
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (ψ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character) :
    (C.leftPPrimeCharacterMap hp hT hU ψ).1 =
      C.leftCharacterMap ψ.1 :=
  rfl

/-- The central character correspondence restricted to irreducible
characters of prime-to-`p` degree. -/
def centralPPrimeCharacterEquiv
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character ≃
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character where
  toFun := C.rightPPrimeCharacterMap hp hT hU
  invFun := C.leftPPrimeCharacterMap hp hT hU
  left_inv χ := by
    apply Subtype.ext
    exact C.leftCharacterMap_rightCharacterMap χ.1
  right_inv ψ := by
    apply Subtype.ext
    exact C.rightCharacterMap_leftCharacterMap ψ.1

@[simp]
theorem centralPPrimeCharacterEquiv_apply
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (χ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character) :
    C.centralPPrimeCharacterEquiv hp hT hU χ =
      C.rightPPrimeCharacterMap hp hT hU χ :=
  rfl

@[simp]
theorem centralPPrimeCharacterEquiv_symm_apply
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (ψ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character) :
    (C.centralPPrimeCharacterEquiv hp hT hU).symm ψ =
      C.leftPPrimeCharacterMap hp hT hU ψ :=
  rfl

end FactorMatchedIsomorphismWitness

namespace CentralIsomorphismWitness

variable {A B : Type}
variable [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]

export FactorMatchedIsomorphismWitness
  (rightMultiplicitySpace rightMultiplicityProjective
    rightMultiplicity_hasInverseFactorSet
    rightMultiplicity_isTrivialOnNormal
    rightMultiplicitySpace_nontrivial rightMultiplicityEvaluationEquiv
    rightMultiplicityProjective_isIrreducible
    liftedRightMultiplicityProjective
    liftedRightMultiplicity_hasInverseFactorSet
    liftedRightMultiplicity_isTrivialOnNormal liftedRightMultiplicity_comap
    liftedRightMultiplicity_isIrreducible leftMultiplicityFDRep
    leftMultiplicityFDRep_isIrreducible leftMultiplicityFDRep_simple
    leftMultiplicityCharacter leftMultiplicityCharacter_values
    leftMultiplicityCharacter_degree leftMultiplicityFDRep_finrank
    rightMultiplicityTensor_finrank leftNormalTensorHom
    leftNormalTensorHom_ne_zero leftMultiplicityCharacter_liesOver
    leftMultiplicityCharacter_degree_eq
    leftMultiplicityCharacter_isPPrime_iff leftCharacterMap
    leftCharacterMap_apply_value leftCharacterMap_isPPrime_iff
    leftMultiplicityCharacter_rightMultiplicityCharacter
    leftCharacterMap_rightCharacterMap leftMultiplicityRealizationEquiv
    rightMultiplicityCharacter_leftMultiplicityCharacter
    rightCharacterMap_leftCharacterMap
    centralCharacterEquiv_symm_apply
    leftPPrimeCharacterMap leftPPrimeCharacterMap_apply_value
    centralPPrimeCharacterEquiv_symm_apply)

def rightMultiplicityRealizationEquiv
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation.Equiv
      (C.rightMultiplicityFDRep χ hχ).ρ
      (C.rightMultiplicityCharacter χ hχ).realization.ρ :=
  C.toFactorMatchedIsomorphismWitness
    |>.rightMultiplicityRealizationEquiv χ hχ

def centralCharacterEquiv
    (C : CentralIsomorphismWitness T U V W) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character ≃
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        U.normalSubgroup.subtype U.character :=
  C.toFactorMatchedIsomorphismWitness.centralCharacterEquiv

@[simp]
theorem centralCharacterEquiv_apply
    (C : CentralIsomorphismWitness T U V W)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character) :
    C.centralCharacterEquiv χ = C.rightCharacterMap χ :=
  rfl

def centralPPrimeCharacterEquiv
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character ≃
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character :=
  C.toFactorMatchedIsomorphismWitness.centralPPrimeCharacterEquiv
    hp hT hU

@[simp]
theorem centralPPrimeCharacterEquiv_apply
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (χ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character) :
    C.centralPPrimeCharacterEquiv hp hT hU χ =
      C.rightPPrimeCharacterMap hp hT hU χ :=
  rfl

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
