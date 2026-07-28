/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCorrespondence
import McKayConjecture.CharacterTriple.MultiplicityReconstruction

/-!
# Multiplicity-space transport across a central character-triple isomorphism

Given a central-isomorphism witness and an irreducible character on the left
lying over the prescribed normal character, its multiplicity space carries
the inverse projective factor.  Tensoring that same multiplicity space with
the associated projective representation on the right is the canonical
candidate for the transported character.

This file packages the construction, proves exact reconstruction on the
left, the normal-restriction formula on the right, and preservation of
prime-to-`p` degree.  Irreducibility of the right tensor representation is
proved in the separate associated-tensor irreducibility layer.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace McKayConjecture
namespace CharacterTriple
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

/-- The multiplicity space of a left irreducible character relative to the
associated projective representation stored in the witness. -/
abbrev leftMultiplicitySpace
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :=
  MultiplicityProjective.Space
    C.leftAssociated χ.realization.ρ

/-- The canonical inverse-factor projective action on the left multiplicity
space. -/
abbrev leftMultiplicityProjective
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :
    ProjectiveRepresentation ℂ A
      (C.leftMultiplicitySpace χ) :=
  MultiplicityProjective.projective
    C.leftAssociated χ.realization.ρ

/-- The left associated factor and the multiplicity factor are pointwise
inverses. -/
theorem leftMultiplicity_hasInverseFactorSet
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :
    C.leftProjective.HasInverseFactorSet
      (C.leftMultiplicityProjective χ) :=
  MultiplicityProjective.hasInverseFactorSet
    C.leftAssociated χ.realization.ρ

/-- The multiplicity lift is the identity on the left normal subgroup. -/
theorem leftMultiplicity_isTrivialOnNormal
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :
    (C.leftMultiplicityProjective χ).IsTrivialOnNormal T :=
  MultiplicityProjective.projective_operator_normal
    C.leftAssociated χ.realization.ρ

/-- Lying over the normal character makes the multiplicity space nonzero. -/
theorem leftMultiplicitySpace_nontrivial
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Nontrivial (C.leftMultiplicitySpace χ) :=
  MultiplicityProjective.space_nontrivial_of_liesOver
    C.leftAssociated χ hχ

/-- The left tensor construction is exactly the multiplicity-space
reconstruction of `χ`. -/
def leftMultiplicityEvaluationEquiv
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation.Equiv
      (C.leftTensorRepresentation
        (C.leftMultiplicityProjective χ)
        (C.leftMultiplicity_hasInverseFactorSet χ))
      χ.realization.ρ := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  exact
    MultiplicityProjective.evaluationRepresentationEquivOfLiesOver
      C.leftAssociated χ hχ

/-- The left tensor has exactly the degree of the reconstructed character. -/
theorem leftMultiplicityTensor_finrank
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Module.finrank ℂ
        (V ⊗[ℂ] C.leftMultiplicitySpace χ) =
      χ.degree := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  calc
    Module.finrank ℂ
        (V ⊗[ℂ] C.leftMultiplicitySpace χ) =
        Module.finrank ℂ χ.realization :=
      (C.leftMultiplicityEvaluationEquiv χ hχ).toLinearEquiv.finrank_eq
    _ = χ.degree := χ.realization_finrank

/-- The finite-dimensional right tensor representation which is the
candidate transport of `χ`. -/
def rightMultiplicityFDRep
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (_hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    FDRep ℂ B := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ _hχ
  exact
    FDRep.of
      (C.rightTensorRepresentation
        (C.leftMultiplicityProjective χ)
        (C.leftMultiplicity_hasInverseFactorSet χ))

/-- The transported candidate has carrier dimension
`U.character.degree * multiplicity`. -/
theorem rightMultiplicityFDRep_finrank
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Module.finrank ℂ (C.rightMultiplicityFDRep χ hχ) =
      U.character.degree *
        Module.finrank ℂ (C.leftMultiplicitySpace χ) := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  change
    Module.finrank ℂ
        (W ⊗[ℂ] C.leftMultiplicitySpace χ) =
      U.character.degree *
        Module.finrank ℂ (C.leftMultiplicitySpace χ)
  rw [Module.finrank_tensorProduct,
    C.rightAssociated.finrank_eq_character_degree]

/-- Exact restriction character of the transported candidate on the right
normal subgroup. -/
theorem rightMultiplicityFDRep_character_on_normal
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (m : U.normalSubgroup) :
    (C.rightMultiplicityFDRep χ hχ).character (m : B) =
      U.character.values m *
        Module.finrank ℂ (C.leftMultiplicitySpace χ) := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  exact
    C.rightTensorRepresentation_character_on_normal
      (C.leftMultiplicityProjective χ)
      (C.leftMultiplicity_hasInverseFactorSet χ)
      (C.leftMultiplicity_isTrivialOnNormal χ) m

/-- If both normal characters have `p'`-degree, the candidate transport has
`p'`-dimension exactly when the source character has `p'`-degree. -/
theorem rightMultiplicityFDRep_isPPrime_iff
    {p : ℕ} (hp : p.Prime)
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p) :
    (¬p ∣ Module.finrank ℂ
        (C.rightMultiplicityFDRep χ hχ)) ↔
      χ.IsPPrimeDegree p := by
  letI : Nontrivial (C.leftMultiplicitySpace χ) :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  have htransport :=
    C.tensorDimension_isPPrime_iff
      (Z := C.leftMultiplicitySpace χ) hp hT hU
  change
    (¬p ∣ Module.finrank ℂ
      (W ⊗[ℂ] C.leftMultiplicitySpace χ)) ↔
      ¬p ∣ χ.degree
  rw [← C.leftMultiplicityTensor_finrank χ hχ]
  exact htransport.symm

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
  (rightMultiplicityFDRep_finrank
    rightMultiplicityFDRep_character_on_normal
    rightMultiplicityFDRep_isPPrime_iff)

abbrev leftMultiplicitySpace
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :=
  C.toFactorMatchedIsomorphismWitness.leftMultiplicitySpace χ

abbrev leftMultiplicityProjective
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :
    ProjectiveRepresentation ℂ A
      (C.leftMultiplicitySpace χ) :=
  C.toFactorMatchedIsomorphismWitness.leftMultiplicityProjective χ

theorem leftMultiplicity_hasInverseFactorSet
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :
    C.leftProjective.HasInverseFactorSet
      (C.leftMultiplicityProjective χ) :=
  C.toFactorMatchedIsomorphismWitness
    |>.leftMultiplicity_hasInverseFactorSet χ

theorem leftMultiplicity_isTrivialOnNormal
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A) :
    (C.leftMultiplicityProjective χ).IsTrivialOnNormal T :=
  C.toFactorMatchedIsomorphismWitness
    |>.leftMultiplicity_isTrivialOnNormal χ

theorem leftMultiplicitySpace_nontrivial
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Nontrivial (C.leftMultiplicitySpace χ) :=
  C.toFactorMatchedIsomorphismWitness
    |>.leftMultiplicitySpace_nontrivial χ hχ

def leftMultiplicityEvaluationEquiv
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Representation.Equiv
      (C.leftTensorRepresentation
        (C.leftMultiplicityProjective χ)
        (C.leftMultiplicity_hasInverseFactorSet χ))
      χ.realization.ρ :=
  C.toFactorMatchedIsomorphismWitness
    |>.leftMultiplicityEvaluationEquiv χ hχ

def rightMultiplicityFDRep
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    FDRep ℂ B :=
  C.toFactorMatchedIsomorphismWitness.rightMultiplicityFDRep χ hχ

theorem leftMultiplicityTensor_finrank
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ) :
    Module.finrank ℂ
        (V ⊗[ℂ] C.leftMultiplicitySpace χ) =
      χ.degree :=
  C.toFactorMatchedIsomorphismWitness
    |>.leftMultiplicityTensor_finrank χ hχ

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
