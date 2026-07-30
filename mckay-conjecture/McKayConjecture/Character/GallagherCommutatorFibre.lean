/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherCommutator

/-!
# Gallagher's commutator identity over a Clifford fibre

This file combines the irreducible Gallagher commutator identity with
the character decomposition of an induced invariant normal-subgroup
character.  The resulting formula is kept division-free.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace CliffordCorrespondence

variable {A : Type} [Group A] [Finite A]

noncomputable local instance (priority := 2000)
    gallagherCommutatorFibreGroupFintype
    (G : Type) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

attribute [local instance]
  irreducibleCharactersOverAlongFintype

/-- Summing Gallagher's global commutator identity over a Clifford
lying-over fibre counts that fibre. -/
theorem sum_degree_mul_sum_gallagherCommutator_charactersOver
    (N : Subgroup A)
    (θ : IrreducibleCharacter N) :
    ∑ χ : IrreducibleCharactersOverAlong N.subtype θ,
        (χ.1.degree : ℂ) *
          ∑ x : A, ∑ y : A,
            χ.1.values (x⁻¹ * y⁻¹ * x * y) =
      (Nat.card A : ℂ) ^ 2 *
        (Nat.card
          (IrreducibleCharactersOverAlong N.subtype θ) : ℂ) := by
  calc
    (∑ χ : IrreducibleCharactersOverAlong N.subtype θ,
        (χ.1.degree : ℂ) *
          ∑ x : A, ∑ y : A,
            χ.1.values (x⁻¹ * y⁻¹ * x * y)) =
        ∑ _χ : IrreducibleCharactersOverAlong N.subtype θ,
          (Nat.card A : ℂ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro χ _
      exact
        IrreducibleCharacter.degree_mul_sum_gallagherCommutator
          χ.1
    _ =
        (Nat.card A : ℂ) ^ 2 *
          (Nat.card
            (IrreducibleCharactersOverAlong N.subtype θ) : ℂ) := by
      simp [Finset.card_univ, ← Nat.card_eq_fintype_card,
        nsmul_eq_mul, mul_comm]

/-- Division-free Gallagher commutator identity for the character
induced from an invariant irreducible character of a normal subgroup. -/
theorem degree_mul_sum_inducedCharacter_gallagherCommutator
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ) :
    (θ.degree : ℂ) *
        ∑ x : A, ∑ y : A,
          (FDRep.characterClassFunction
            (FDRep.ind N.subtype θ.realization))
              (x⁻¹ * y⁻¹ * x * y) =
      (Nat.card A : ℂ) ^ 2 *
        (Nat.card
          (IrreducibleCharactersOverAlong N.subtype θ) : ℂ) := by
  let inducedCharacter : ClassFunction A :=
    FDRep.characterClassFunction
      (FDRep.ind N.subtype θ.realization)
  have hinduced :=
    degree_smul_inducedCharacter_eq_sum_charactersOver
      N θ hinvariant
  have hvalue (z : A) :
      (θ.degree : ℂ) * inducedCharacter z =
        ∑ χ : IrreducibleCharactersOverAlong N.subtype θ,
          (χ.1.degree : ℂ) * χ.1.values z := by
    have h :=
      congrArg (fun f : ClassFunction A ↦ f z) hinduced
    simpa [inducedCharacter, map_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul,
      IrreducibleCharacter.toClassFunction_apply] using h
  change
    (θ.degree : ℂ) *
        ∑ x : A, ∑ y : A,
          inducedCharacter (x⁻¹ * y⁻¹ * x * y) =
      _
  calc
    (θ.degree : ℂ) *
          ∑ x : A, ∑ y : A,
            inducedCharacter (x⁻¹ * y⁻¹ * x * y) =
        ∑ x : A, ∑ y : A,
          (θ.degree : ℂ) *
            inducedCharacter (x⁻¹ * y⁻¹ * x * y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ =
        ∑ x : A, ∑ y : A,
          ∑ χ : IrreducibleCharactersOverAlong N.subtype θ,
            (χ.1.degree : ℂ) *
              χ.1.values (x⁻¹ * y⁻¹ * x * y) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact hvalue (x⁻¹ * y⁻¹ * x * y)
    _ =
        ∑ x : A,
          ∑ χ : IrreducibleCharactersOverAlong N.subtype θ,
            ∑ y : A,
              (χ.1.degree : ℂ) *
                χ.1.values (x⁻¹ * y⁻¹ * x * y) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ =
        ∑ χ : IrreducibleCharactersOverAlong N.subtype θ,
          ∑ x : A, ∑ y : A,
            (χ.1.degree : ℂ) *
              χ.1.values (x⁻¹ * y⁻¹ * x * y) := by
      rw [Finset.sum_comm]
    _ =
        ∑ χ : IrreducibleCharactersOverAlong N.subtype θ,
          (χ.1.degree : ℂ) *
            ∑ x : A, ∑ y : A,
              χ.1.values (x⁻¹ * y⁻¹ * x * y) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ =
        (Nat.card A : ℂ) ^ 2 *
          (Nat.card
            (IrreducibleCharactersOverAlong N.subtype θ) : ℂ) :=
      sum_degree_mul_sum_gallagherCommutator_charactersOver
        N θ

end CliffordCorrespondence
end McKayConjecture
