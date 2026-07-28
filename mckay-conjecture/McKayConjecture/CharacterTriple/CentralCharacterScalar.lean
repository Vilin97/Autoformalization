/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCharacterBijection

/-!
# Central scalars in a central character-triple correspondence

The character correspondence attached to a central isomorphism uses one
common projective multiplicity representation on the two sides.  At a
matched element centralizing the left normal subgroup, the two associated
projective representations act through the same scalar.  The common
multiplicity trace therefore cancels, giving equality of normalized
character values.

The result is stated in cross-multiplied form, so no division by character
degrees is needed.
-/

noncomputable section

open scoped TensorProduct

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

variable {A B : Type}
variable [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]

/-- The forward central character-triple correspondence preserves the
normalized value at every pair of elements matched by the stored embedding
whose left member centralizes the distinguished normal subgroup. -/
theorem rightMultiplicityCharacter_matchedCentral_cross
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T.normalSubgroup.subtype T.character χ)
    (b : B)
    (hb :
      C.embedding b ∈
        Subgroup.centralizer (T.normalSubgroup : Set A)) :
    χ.values (C.embedding b) *
        ((C.rightMultiplicityCharacter χ hχ).degree : ℂ) =
      (C.rightMultiplicityCharacter χ hχ).values b *
        (χ.degree : ℂ) := by
  let Z := C.leftMultiplicitySpace χ
  let Q := C.leftMultiplicityProjective χ
  let hQ := C.leftMultiplicity_hasInverseFactorSet χ
  letI : Nontrivial Z :=
    C.leftMultiplicitySpace_nontrivial χ hχ
  obtain ⟨c, hleft, hright⟩ :=
    C.scalar_agreement b hb
  have hleftTrace :
      C.leftProjective.traceFunction (C.embedding b) =
        (c : ℂ) * (Module.finrank ℂ V : ℂ) := by
    change
      LinearMap.trace ℂ V
          (C.leftProjective.operator (C.embedding b) :
            V →ₗ[ℂ] V) =
        (c : ℂ) * (Module.finrank ℂ V : ℂ)
    rw [hleft]
    have hscalar :
        ((scalarLinearEquiv ℂ V c : V ≃ₗ[ℂ] V) :
            V →ₗ[ℂ] V) =
          (c : ℂ) •
            (LinearMap.id : Module.End ℂ V) := by
      ext v
      simp
    rw [hscalar, map_smul, LinearMap.trace_id]
    simp only [smul_eq_mul]
  have hrightTrace :
      C.rightProjective.traceFunction b =
        (c : ℂ) * (Module.finrank ℂ W : ℂ) := by
    change
      LinearMap.trace ℂ W
          (C.rightProjective.operator b :
            W →ₗ[ℂ] W) =
        (c : ℂ) * (Module.finrank ℂ W : ℂ)
    rw [hright]
    have hscalar :
        ((scalarLinearEquiv ℂ W c : W ≃ₗ[ℂ] W) :
            W →ₗ[ℂ] W) =
          (c : ℂ) •
            (LinearMap.id : Module.End ℂ W) := by
      ext w
      simp
    rw [hscalar, map_smul, LinearMap.trace_id]
    simp only [smul_eq_mul]
  have hχvalue :
      χ.values (C.embedding b) =
        ((c : ℂ) * (Module.finrank ℂ V : ℂ)) *
          Q.traceFunction (C.embedding b) := by
    calc
      χ.values (C.embedding b) =
          χ.realization.character (C.embedding b) :=
        (congrFun χ.realization_character
          (C.embedding b)).symm
      _ =
          (C.leftTensorRepresentation Q hQ).character
            (C.embedding b) :=
        (congrFun
          (Representation.char_iso
            (C.leftMultiplicityEvaluationEquiv χ hχ))
          (C.embedding b)).symm
      _ =
          C.leftProjective.traceFunction (C.embedding b) *
            Q.traceFunction (C.embedding b) := by
        rw [C.leftTensorRepresentation_character]
        rfl
      _ = _ := by rw [hleftTrace]
  have hrightValue :
      (C.rightMultiplicityCharacter χ hχ).values b =
        ((c : ℂ) * (Module.finrank ℂ W : ℂ)) *
          Q.traceFunction (C.embedding b) := by
    calc
      (C.rightMultiplicityCharacter χ hχ).values b =
          (C.rightMultiplicityFDRep χ hχ).character b := by
        rw [C.rightMultiplicityCharacter_values]
      _ =
          (C.rightTensorRepresentation Q hQ).character b :=
        rfl
      _ =
          C.rightProjective.traceFunction b *
            Q.traceFunction (C.embedding b) := by
        rw [C.rightTensorRepresentation_character]
        rfl
      _ = _ := by rw [hrightTrace]
  have hχdegreeNat :
      χ.degree =
        Module.finrank ℂ V * Module.finrank ℂ Z := by
    calc
      χ.degree =
          Module.finrank ℂ (V ⊗[ℂ] Z) :=
        (C.leftMultiplicityTensor_finrank χ hχ).symm
      _ =
          Module.finrank ℂ V * Module.finrank ℂ Z :=
        Module.finrank_tensorProduct
  have hrightDegreeNat :
      (C.rightMultiplicityCharacter χ hχ).degree =
        Module.finrank ℂ W * Module.finrank ℂ Z := by
    calc
      (C.rightMultiplicityCharacter χ hχ).degree =
          U.character.degree * Module.finrank ℂ Z :=
        C.rightMultiplicityCharacter_degree_eq χ hχ
      _ =
          Module.finrank ℂ W * Module.finrank ℂ Z := by
        rw [C.rightAssociated.finrank_eq_character_degree]
  have hχdegree :
      (χ.degree : ℂ) =
        (Module.finrank ℂ V : ℂ) *
          (Module.finrank ℂ Z : ℂ) := by
    exact_mod_cast hχdegreeNat
  have hrightDegree :
      ((C.rightMultiplicityCharacter χ hχ).degree : ℂ) =
        (Module.finrank ℂ W : ℂ) *
          (Module.finrank ℂ Z : ℂ) := by
    exact_mod_cast hrightDegreeNat
  rw [hχvalue, hrightValue, hχdegree, hrightDegree]
  ring

/-- Cross identity for the bundled forward character correspondence. -/
theorem rightCharacterMap_matchedCentral_cross
    (C : CentralIsomorphismWitness T U V W)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character)
    (b : B)
    (hb :
      C.embedding b ∈
        Subgroup.centralizer (T.normalSubgroup : Set A)) :
    χ.1.values (C.embedding b) *
        ((C.rightCharacterMap χ).1.degree : ℂ) =
      (C.rightCharacterMap χ).1.values b *
        (χ.1.degree : ℂ) :=
  C.rightMultiplicityCharacter_matchedCentral_cross
    χ.1 χ.2 b hb

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
