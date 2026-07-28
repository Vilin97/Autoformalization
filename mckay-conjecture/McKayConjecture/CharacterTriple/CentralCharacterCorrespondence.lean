/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Construction
import McKayConjecture.CharacterTriple.AssociatedTensorIrreducible
import McKayConjecture.CharacterTriple.CentralMultiplicity
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# The forward character correspondence for a central isomorphism

For an irreducible character on the left lying over the prescribed normal
character, its projective multiplicity space has the inverse factor set.
Restricting that projective action across the central-isomorphism embedding
and tensoring it with the associated projective representation on the right
gives an irreducible ordinary representation.

This file packages that representation as an irreducible character, proves
its normal-subgroup and degree formulas, and proves preservation of
prime-to-`p` degree.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra TensorProduct

namespace McKayConjecture
namespace CharacterTriple

namespace CentralCharacterCorrespondence

variable {G : Type} [Group G]

/-- Irreducible characters lying over a fixed character and having
prime-to-`p` degree. -/
abbrev PPrimeIrreducibleCharactersOverAlong
    {H : Type} [Group H] (p : ℕ) (φ : H →* G)
    (η : IrreducibleCharacter H) :=
  CliffordCorrespondence.PPrimeIrreducibleCharactersOverAlong φ η p

/-- Convert lattice irreducibility of a finite-dimensional complex
representation into categorical simplicity of the corresponding `FDRep`. -/
theorem simpleFDRepOfIsIrreducible
    {X : Type} [AddCommGroup X] [Module ℂ X] [Module.Finite ℂ X]
    (ρ : Representation ℂ G X) [Representation.IsIrreducible ρ] :
    Simple (FDRep.of ρ) := by
  let R : Rep ℂ G :=
    (forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of ρ)
  letI : IsSimpleModule ℂ[G] ρ.asModule := inferInstance
  letI : Simple (ModuleCat.of ℂ[G] ρ.asModule) := inferInstance
  letI : Simple
      ((Rep.equivalenceModuleMonoidAlgebra
        (k := ℂ) (G := G)).functor.obj R) := by
    change Simple (ModuleCat.of ℂ[G] ρ.asModule)
    infer_instance
  letI : Simple R :=
    Functor.simple_of_simple_obj
      (Rep.equivalenceModuleMonoidAlgebra
        (k := ℂ) (G := G)).functor R
  exact
    Functor.simple_of_simple_obj
      (forget₂ (FDRep ℂ G) (Rep ℂ G)) (FDRep.of ρ)

/-- Irreducibility transports across an equivalence of complex
representations. -/
theorem isIrreducibleOfEquiv
    {X Y : Type}
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

/-- The multiplicity-space projective representation attached to a left
character lying over the normal character is irreducible. -/
theorem leftMultiplicityProjective_isIrreducible
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (C.leftMultiplicityProjective χ).IsIrreducible := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  letI : Representation.IsIrreducible χ.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple χ.realization
  have hleft :
      (C.leftTensorRepresentation
        (C.leftMultiplicityProjective χ)
        (C.leftMultiplicity_hasInverseFactorSet χ)).IsIrreducible :=
    CentralCharacterCorrespondence.isIrreducibleOfEquiv
      (CliffordRestriction.isIrreducible_of_simple χ.realization)
      (C.leftMultiplicityEvaluationEquiv χ hχ).symm
  apply
    (C.leftAssociated.cancelTensorRepresentation_isIrreducible_iff
      (C.leftMultiplicityProjective χ)
      (C.leftMultiplicity_hasInverseFactorSet χ)
      (C.leftMultiplicity_isTrivialOnNormal χ)).mp
  exact hleft

/-- The right multiplicity tensor is irreducible. -/
theorem rightMultiplicityFDRep_isIrreducible
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation.IsIrreducible
      (C.rightMultiplicityFDRep χ hχ).ρ := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  have hQ :
      (C.leftMultiplicityProjective χ).IsIrreducible :=
    C.leftMultiplicityProjective_isIrreducible χ hχ
  have hQright :
      ((C.leftMultiplicityProjective χ).comap
        C.embedding).IsIrreducible :=
    (C.multiplicity_isIrreducible_iff_comap
      (C.leftMultiplicityProjective χ)
      (C.leftMultiplicity_hasInverseFactorSet χ)
      (C.leftMultiplicity_isTrivialOnNormal χ)).mp hQ
  apply
    (C.rightAssociated.cancelTensorRepresentation_isIrreducible_iff
      ((C.leftMultiplicityProjective χ).comap C.embedding)
      (C.right_hasInverseFactorSet
        (C.leftMultiplicityProjective χ)
        (C.leftMultiplicity_hasInverseFactorSet χ))
      (C.right_isTrivialOnNormal
        (C.leftMultiplicityProjective χ)
        (C.leftMultiplicity_isTrivialOnNormal χ))).mpr
  exact hQright

/-- The right multiplicity tensor is a simple finite-dimensional
representation. -/
theorem rightMultiplicityFDRep_simple
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Simple (C.rightMultiplicityFDRep χ hχ) := by
  letI :
      Representation.IsIrreducible
        (C.rightMultiplicityFDRep χ hχ).ρ :=
    C.rightMultiplicityFDRep_isIrreducible χ hχ
  exact
    CentralCharacterCorrespondence.simpleFDRepOfIsIrreducible
      (C.rightMultiplicityFDRep χ hχ).ρ

/-- The irreducible character transported to the right by the common
projective multiplicity space. -/
def rightMultiplicityCharacter
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    IrreducibleCharacter B := by
  letI : Simple (C.rightMultiplicityFDRep χ hχ) :=
    C.rightMultiplicityFDRep_simple χ hχ
  exact
    IrreducibleCharacter.ofSimple
      (C.rightMultiplicityFDRep χ hχ)

@[simp]
theorem rightMultiplicityCharacter_values
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (C.rightMultiplicityCharacter χ hχ).values =
      (C.rightMultiplicityFDRep χ hχ).character := by
  letI : Simple (C.rightMultiplicityFDRep χ hχ) :=
    C.rightMultiplicityFDRep_simple χ hχ
  rfl

@[simp]
theorem rightMultiplicityCharacter_degree
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (C.rightMultiplicityCharacter χ hχ).degree =
      Module.finrank ℂ (C.rightMultiplicityFDRep χ hχ) := by
  letI : Simple (C.rightMultiplicityFDRep χ hχ) :=
    C.rightMultiplicityFDRep_simple χ hχ
  rfl

/-- Exact normal-restriction formula for the transported irreducible
character. -/
theorem rightMultiplicityCharacter_on_normal
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (m : U.normalSubgroup) :
    (C.rightMultiplicityCharacter χ hχ).values (m : B) =
      U.character.values m *
        Module.finrank ℂ (C.leftMultiplicitySpace χ) := by
  rw [C.rightMultiplicityCharacter_values]
  exact C.rightMultiplicityFDRep_character_on_normal χ hχ m

/-- Fixing a vector in the multiplicity space embeds the associated right
normal representation into the normal restriction of the transported tensor
representation. -/
def rightNormalTensorHom
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (z : C.leftMultiplicitySpace χ) :
    C.rightAssociated.fdRestriction ⟶
      FDRep.res U.normalSubgroup.subtype
        (C.rightMultiplicityFDRep χ hχ) := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  let L : W →ₗ[ℂ] W ⊗[ℂ] C.leftMultiplicitySpace χ :=
    (TensorProduct.mk ℂ W
      (C.leftMultiplicitySpace χ)).flip z
  refine
    { hom := FGModuleCat.ofHom L
      comm := ?_ }
  intro m
  apply FGModuleCat.hom_ext
  ext w
  change
    L (C.rightAssociated.restriction m w) =
      C.rightTensorRepresentation
          (C.leftMultiplicityProjective χ)
          (C.leftMultiplicity_hasInverseFactorSet χ)
          (m : B) (L w)
  rw [C.rightAssociated.restriction_apply]
  change
    C.rightProjective.operator (m : B) w ⊗ₜ[ℂ] z =
      TensorProduct.congr
        (C.rightProjective.operator (m : B))
        ((C.leftMultiplicityProjective χ).operator
          (C.embedding (m : B))) (w ⊗ₜ[ℂ] z)
  rw [TensorProduct.congr_tmul]
  have hm :=
    C.right_isTrivialOnNormal
      (C.leftMultiplicityProjective χ)
      (C.leftMultiplicity_isTrivialOnNormal χ) m
  change
    (C.leftMultiplicityProjective χ).operator
      (C.embedding (m : B)) = 1 at hm
  rw [hm]
  rfl

/-- The fixed-vector normal tensor embedding is nonzero when the chosen
multiplicity vector is nonzero. -/
theorem rightNormalTensorHom_ne_zero
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    {z : C.leftMultiplicitySpace χ} (hz : z ≠ 0) :
    C.rightNormalTensorHom χ hχ z ≠ 0 := by
  obtain ⟨w : W, hw⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ :=
    Module.Projective.exists_dual_eq_one ℂ hz
  intro hzero
  have hlinear :=
    congrArg
      (fun f :
        C.rightAssociated.fdRestriction ⟶
          FDRep.res U.normalSubgroup.subtype
            (C.rightMultiplicityFDRep χ hχ) ↦
        f.hom.hom)
      hzero
  have happ := ConcreteCategory.congr_hom hlinear w
  change w ⊗ₜ[ℂ] z = 0 at happ
  have hsliced :=
    congrArg
      (fun t : W ⊗[ℂ] C.leftMultiplicitySpace χ ↦
        TensorProduct.rid ℂ W
          (φ.lTensor W t))
      happ
  simp only [map_zero,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
    hφ, one_smul] at hsliced
  exact hw hsliced

/-- The transported irreducible character lies over the prescribed right
normal character. -/
theorem rightMultiplicityCharacter_liesOver
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character
      (C.rightMultiplicityCharacter χ hχ) := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  letI : Simple (C.rightMultiplicityFDRep χ hχ) :=
    C.rightMultiplicityFDRep_simple χ hχ
  obtain ⟨z : C.leftMultiplicitySpace χ, hz⟩ :=
    exists_ne (0 : C.leftMultiplicitySpace χ)
  let i :
      C.rightAssociated.fdRestriction ≅
        U.character.realization :=
    MultiplicityProjective.restrictionIsoRealization
      C.rightAssociated
  let fD :
      U.character.realization ⟶
        FDRep.res U.normalSubgroup.subtype
          (C.rightMultiplicityFDRep χ hχ) :=
    i.inv ≫ C.rightNormalTensorHom χ hχ z
  have hfD : fD ≠ 0 := by
    intro hfD
    apply C.rightNormalTensorHom_ne_zero χ hχ hz
    have hzero :=
      congrArg (fun q ↦ i.hom ≫ q) hfD
    simpa [fD, Category.assoc] using hzero
  let ψ : IrreducibleCharacter B :=
    C.rightMultiplicityCharacter χ hχ
  have hchar :
      (C.rightMultiplicityFDRep χ hχ).character =
        ψ.realization.character := by
    rw [ψ.realization_character]
    exact (C.rightMultiplicityCharacter_values χ hχ).symm
  obtain ⟨j :
      C.rightMultiplicityFDRep χ hχ ≅ ψ.realization⟩ :=
    FDRep.nonempty_iso_of_character_eq
      (C.rightMultiplicityFDRep χ hχ)
      ψ.realization hchar
  let jRes :
      FDRep.res U.normalSubgroup.subtype
          (C.rightMultiplicityFDRep χ hχ) ⟶
        FDRep.res U.normalSubgroup.subtype ψ.realization :=
    (FDRep.resFunctor U.normalSubgroup.subtype).map j.hom
  let f :
      U.character.realization ⟶
        FDRep.res U.normalSubgroup.subtype ψ.realization :=
    fD ≫ jRes
  apply
    (CliffordCorrespondence.liesOverAlong_iff_exists_nonzero
      U.normalSubgroup.subtype U.character ψ).mpr
  refine ⟨f, ?_⟩
  intro hf
  apply hfD
  have hzero :=
    congrArg
      (fun q ↦
        q ≫
          (FDRep.resFunctor U.normalSubgroup.subtype).map j.inv)
      hf
  simpa [f, jRes, Category.assoc] using hzero

/-- The degree of the transported irreducible character. -/
theorem rightMultiplicityCharacter_degree_eq
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (C.rightMultiplicityCharacter χ hχ).degree =
      U.character.degree *
        Module.finrank ℂ (C.leftMultiplicitySpace χ) := by
  rw [C.rightMultiplicityCharacter_degree]
  exact C.rightMultiplicityFDRep_finrank χ hχ

/-- If the two prescribed normal characters have prime-to-`p` degree, the
forward central-triple transport preserves prime-to-`p` degree exactly. -/
theorem rightMultiplicityCharacter_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    (C.rightMultiplicityCharacter χ hχ).IsPPrimeDegree p ↔
      χ.IsPPrimeDegree p := by
  rw [IrreducibleCharacter.IsPPrimeDegree,
    C.rightMultiplicityCharacter_degree]
  exact
    C.rightMultiplicityFDRep_isPPrime_iff
      hp χ hχ hT hU

/-- The explicit forward map on irreducible characters lying over the
prescribed normal characters. -/
def rightCharacterMap
    (C : CentralIsomorphismWitness T U V W) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character →
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        U.normalSubgroup.subtype U.character :=
  fun χ ↦
    ⟨C.rightMultiplicityCharacter χ.1 χ.2,
      C.rightMultiplicityCharacter_liesOver χ.1 χ.2⟩

@[simp]
theorem rightCharacterMap_apply_value
    (C : CentralIsomorphismWitness T U V W)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character) :
    (C.rightCharacterMap χ).1 =
      C.rightMultiplicityCharacter χ.1 χ.2 :=
  rfl

/-- The forward map preserves prime-to-`p` degree exactly when the two
normal characters have prime-to-`p` degree. -/
theorem rightCharacterMap_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    (C.rightCharacterMap χ).1.IsPPrimeDegree p ↔
      χ.1.IsPPrimeDegree p :=
  C.rightMultiplicityCharacter_isPPrime_iff
    hp χ.1 χ.2 hT hU

/-- The explicit forward map restricted to prime-to-`p` characters. -/
def rightPPrimeCharacterMap
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character →
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character :=
  fun χ ↦
    ⟨C.rightCharacterMap χ.1,
      (C.rightCharacterMap_isPPrime_iff
        hp χ.1 hT hU).mpr χ.2⟩

@[simp]
theorem rightPPrimeCharacterMap_apply_value
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (χ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character) :
    (C.rightPPrimeCharacterMap hp hT hU χ).1 =
      C.rightCharacterMap χ.1 :=
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
  (rightMultiplicityFDRep_isIrreducible rightMultiplicityFDRep_simple
    rightMultiplicityCharacter_degree rightNormalTensorHom
    rightNormalTensorHom_ne_zero rightMultiplicityCharacter_isPPrime_iff
    rightCharacterMap_isPPrime_iff)

theorem leftMultiplicityProjective_isIrreducible
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (C.leftMultiplicityProjective χ).IsIrreducible :=
  C.toFactorMatchedIsomorphismWitness
    |>.leftMultiplicityProjective_isIrreducible χ hχ

def rightMultiplicityCharacter
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    IrreducibleCharacter B :=
  C.toFactorMatchedIsomorphismWitness.rightMultiplicityCharacter χ hχ

@[simp]
theorem rightMultiplicityCharacter_values
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (C.rightMultiplicityCharacter χ hχ).values =
      (C.rightMultiplicityFDRep χ hχ).character :=
  C.toFactorMatchedIsomorphismWitness
    |>.rightMultiplicityCharacter_values χ hχ

theorem rightMultiplicityCharacter_on_normal
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (m : U.normalSubgroup) :
    (C.rightMultiplicityCharacter χ hχ).values (m : B) =
      U.character.values m *
        Module.finrank ℂ (C.leftMultiplicitySpace χ) :=
  C.toFactorMatchedIsomorphismWitness
    |>.rightMultiplicityCharacter_on_normal χ hχ m

theorem rightMultiplicityCharacter_liesOver
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    CliffordCorrespondence.LiesOverAlong
      U.normalSubgroup.subtype U.character
      (C.rightMultiplicityCharacter χ hχ) :=
  C.toFactorMatchedIsomorphismWitness
    |>.rightMultiplicityCharacter_liesOver χ hχ

theorem rightMultiplicityCharacter_degree_eq
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    (C.rightMultiplicityCharacter χ hχ).degree =
      U.character.degree *
        Module.finrank ℂ (C.leftMultiplicitySpace χ) :=
  C.toFactorMatchedIsomorphismWitness
    |>.rightMultiplicityCharacter_degree_eq χ hχ

def rightCharacterMap
    (C : CentralIsomorphismWitness T U V W) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character →
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        U.normalSubgroup.subtype U.character :=
  C.toFactorMatchedIsomorphismWitness.rightCharacterMap

@[simp]
theorem rightCharacterMap_apply_value
    (C : CentralIsomorphismWitness T U V W)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character) :
    (C.rightCharacterMap χ).1 =
      C.rightMultiplicityCharacter χ.1 χ.2 :=
  rfl

def rightPPrimeCharacterMap
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character →
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p U.normalSubgroup.subtype U.character :=
  C.toFactorMatchedIsomorphismWitness.rightPPrimeCharacterMap
    hp hT hU

@[simp]
theorem rightPPrimeCharacterMap_apply_value
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (χ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p T.normalSubgroup.subtype T.character) :
    (C.rightPPrimeCharacterMap hp hT hU χ).1 =
      C.rightCharacterMap χ.1 :=
  rfl

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
