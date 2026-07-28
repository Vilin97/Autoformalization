/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GeneralizedCharacter
import McKayConjecture.Character.InductionMultiplicityDegree

/-!
# Induction, character pairings, and generalized characters

The classical induction formula is linear in the inducing class function.
Using irreducible-character completeness and representation-theoretic
Frobenius reciprocity, this file proves Frobenius reciprocity for arbitrary
complex class functions:

`⟪Ind_S^G θ, f⟫_G = ⟪θ, Res_S^G f⟫_S`.

It follows that induction carries integral generalized characters to
integral generalized characters.  These are the formal character-theoretic
inputs needed to deduce Brauer's local-to-global criterion from Brauer
induction.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

noncomputable local instance classFunctionInductionPairingFintypeG :
    Fintype G :=
  Fintype.ofFinite _

/-- Classical class-function induction, bundled as a complex-linear map. -/
def induceLinearMap (S : Subgroup G) :
    ClassFunction S →ₗ[ℂ] ClassFunction G where
  toFun := induce S
  map_add' θ κ := by
    classical
    ext g
    simp only [induce_apply, inductionTerm, AddMemClass.coe_add,
      Pi.add_apply]
    have hsum :
        (∑ x : G,
            if hx : x⁻¹ * g * x ∈ S then
              θ ⟨x⁻¹ * g * x, hx⟩ +
                κ ⟨x⁻¹ * g * x, hx⟩
            else 0) =
          (∑ x : G,
              if hx : x⁻¹ * g * x ∈ S then
                θ ⟨x⁻¹ * g * x, hx⟩
              else 0) +
            ∑ x : G,
              if hx : x⁻¹ * g * x ∈ S then
                κ ⟨x⁻¹ * g * x, hx⟩
              else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      split_ifs <;> simp
    rw [hsum]
    ring
  map_smul' c θ := by
    classical
    ext g
    simp only [induce_apply, inductionTerm, SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul]
    have hsum :
        (∑ x : G,
            if hx : x⁻¹ * g * x ∈ S then
              c * θ ⟨x⁻¹ * g * x, hx⟩
            else 0) =
          c * ∑ x : G,
            if hx : x⁻¹ * g * x ∈ S then
              θ ⟨x⁻¹ * g * x, hx⟩
            else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      split_ifs <;> simp
    rw [hsum]
    change
      (Nat.card S : ℂ)⁻¹ *
          (c * ∑ x : G,
            if hx : x⁻¹ * g * x ∈ S then
              θ ⟨x⁻¹ * g * x, hx⟩
            else 0) =
        c * ((Nat.card S : ℂ)⁻¹ *
          ∑ x : G,
            if hx : x⁻¹ * g * x ∈ S then
              θ ⟨x⁻¹ * g * x, hx⟩
            else 0)
    ring

@[simp]
theorem induceLinearMap_apply
    (S : Subgroup G) (θ : ClassFunction S) :
    induceLinearMap S θ = induce S θ :=
  rfl

@[simp]
theorem induce_zero (S : Subgroup G) :
    induce S (0 : ClassFunction S) = 0 :=
  map_zero (induceLinearMap S)

@[simp]
theorem induce_add (S : Subgroup G)
    (θ κ : ClassFunction S) :
    induce S (θ + κ) = induce S θ + induce S κ :=
  map_add (induceLinearMap S) θ κ

@[simp]
theorem induce_smul (S : Subgroup G)
    (c : ℂ) (θ : ClassFunction S) :
    induce S (c • θ) = c • induce S θ :=
  map_smul (induceLinearMap S) c θ

/-- Frobenius reciprocity when the inducing class function is
irreducible. -/
private theorem normalizedPairing_induce_irreducible
    (S : Subgroup G) (η : IrreducibleCharacter S)
    (f : ClassFunction G) :
    normalizedPairing (induce S η.toClassFunction) f =
      normalizedPairing η.toClassFunction
        (comapLinearMap S.subtype f) := by
  letI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  rw [irreducibleCharacter_fourierExpansion f]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro χ _hχ
  congr 1
  have hη :
      η.toClassFunction =
        FDRep.characterClassFunction η.realization := by
    apply ClassFunction.ext
    intro s
    exact (congrFun η.realization_character s).symm
  rw [hη, ← InductionCharacter.ind_characterClassFunction_eq_induce]
  change
      normalizedPairing
          (FDRep.characterClassFunction
            (FDRep.ind S.subtype η.realization))
          χ.toClassFunction =
        normalizedPairing
          (FDRep.characterClassFunction η.realization)
        (comapLinearMap S.subtype χ.toClassFunction)
  rw [
    CliffordCorrespondence.normalizedPairing_inducedCharacter_eq_restrictionMultiplicity]
  have hres :
      comapLinearMap S.subtype χ.toClassFunction =
        FDRep.characterClassFunction
          (FDRep.res S.subtype χ.realization) := by
    have hχ :
        χ.toClassFunction =
          FDRep.characterClassFunction χ.realization := by
      apply ClassFunction.ext
      intro g
      exact (congrFun χ.realization_character g).symm
    rw [hχ, ← characterClassFunction_res]
  rw [← hη, hres, normalizedPairing_comm,
    CliffordCorrespondence.normalizedPairing_restrictedCharacter_eq_restrictionMultiplicity]

/-- Frobenius reciprocity for arbitrary complex class functions. -/
theorem normalizedPairing_induce
    (S : Subgroup G) (θ : ClassFunction S)
    (f : ClassFunction G) :
    normalizedPairing (induce S θ) f =
      normalizedPairing θ (comapLinearMap S.subtype f) := by
  letI : Fintype (IrreducibleCharacter S) := Fintype.ofFinite _
  rw [irreducibleCharacter_fourierExpansion θ]
  change
    normalizedPairing
        (induceLinearMap S
          (∑ η : IrreducibleCharacter S,
            normalizedPairing θ η.toClassFunction •
              η.toClassFunction))
        f =
      normalizedPairing
        (∑ η : IrreducibleCharacter S,
          normalizedPairing θ η.toClassFunction •
            η.toClassFunction)
        (comapLinearMap S.subtype f)
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro η _hη
  congr 1
  exact normalizedPairing_induce_irreducible S η f

/-- Symmetric form of class-function Frobenius reciprocity. -/
theorem normalizedPairing_induce_right
    (S : Subgroup G) (f : ClassFunction G)
    (θ : ClassFunction S) :
    normalizedPairing f (induce S θ) =
      normalizedPairing
        (comapLinearMap S.subtype f) θ := by
  rw [normalizedPairing_comm, normalizedPairing_induce,
    normalizedPairing_comm]

/-- The pairing of two integral generalized characters is an ordinary
integer. -/
theorem IsGeneralizedCharacter.normalizedPairing_integral
    {f k : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (hk : IsGeneralizedCharacter k) :
    ∃ z : ℤ, normalizedPairing f k = (z : ℂ) := by
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨d, rfl⟩ := hk
  letI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  refine ⟨∑ χ : IrreducibleCharacter G, d χ * c χ, ?_⟩
  calc
    normalizedPairing
        (IrreducibleCharacter.integerCharacterCombination c)
        (IrreducibleCharacter.integerCharacterCombination d) =
        normalizedPairing
          (IrreducibleCharacter.integerCharacterCombination d)
          (IrreducibleCharacter.integerCharacterCombination c) :=
      normalizedPairing_comm _ _
    _ = ∑ χ : IrreducibleCharacter G,
          (d χ : ℂ) *
            normalizedPairing χ.toClassFunction
              (IrreducibleCharacter.integerCharacterCombination c) := by
        rw [IrreducibleCharacter.integerCharacterCombination]
        simp only [map_sum, LinearMap.sum_apply, map_smul,
          LinearMap.smul_apply, smul_eq_mul]
    _ = ∑ χ : IrreducibleCharacter G,
          (d χ : ℂ) * (c χ : ℂ) := by
        apply Finset.sum_congr rfl
        intro χ _hχ
        rw [normalizedPairing_comm,
          IrreducibleCharacter.normalizedPairing_integerCharacterCombination_irreducible]
    _ = ((∑ χ : IrreducibleCharacter G, d χ * c χ : ℤ) : ℂ) := by
        simp only [Int.cast_sum, Int.cast_mul]

/-- Induction from a subgroup preserves integral generalized characters. -/
theorem IsGeneralizedCharacter.induce
    (S : Subgroup G) {θ : ClassFunction S}
    (hθ : IsGeneralizedCharacter θ) :
    IsGeneralizedCharacter (induce S θ) := by
  rw [isGeneralizedCharacter_iff_pairings_integral]
  intro χ
  rw [normalizedPairing_induce]
  have hres :
      IsGeneralizedCharacter
        (comapLinearMap S.subtype χ.toClassFunction) :=
    isGeneralizedCharacter_comap_irreducible S.subtype χ
  exact hθ.normalizedPairing_integral hres

end ClassFunction
end McKayConjecture
