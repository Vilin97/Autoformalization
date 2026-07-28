/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Realization
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Finiteness of ordinary irreducible characters

Schur orthogonality makes the irreducible complex characters of a finite group
linearly independent in the finite-dimensional space `G → ℂ`.  Consequently
there are only finitely many such characters.  Consumers needing finite sums
can install `Fintype.ofFinite (IrreducibleCharacter G)` locally.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture.IrreducibleCharacter

variable {G : Type u} [Group G]

/-- The normalized character pairing with a fixed irreducible character,
viewed as a complex-linear functional on all functions `G → ℂ`. -/
def pairingFunctional [Fintype G] (ψ : IrreducibleCharacter G) :
    Module.Dual ℂ (G → ℂ) where
  toFun φ := (Nat.card G : ℂ)⁻¹ * ∑ g : G, φ g * ψ.values g⁻¹
  map_add' φ₁ φ₂ := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c φ := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring

@[simp]
theorem pairingFunctional_apply [Fintype G] (ψ : IrreducibleCharacter G) (φ : G → ℂ) :
    ψ.pairingFunctional φ =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, φ g * ψ.values g⁻¹ :=
  rfl

/-- Distinct irreducible characters are orthogonal for the normalized pairing. -/
theorem pairingFunctional_eq_zero_of_ne [Fintype G]
    (χ ψ : IrreducibleCharacter G) (hχψ : χ ≠ ψ) :
    ψ.pairingFunctional χ.values = 0 := by
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hnoIso : ¬Nonempty (χ.realization ≅ ψ.realization) := by
    rintro ⟨i⟩
    apply hχψ
    apply IrreducibleCharacter.ext
    rw [← χ.realization_character, ← ψ.realization_character]
    exact FDRep.char_iso i
  simpa [pairingFunctional, hnoIso, χ.realization_character, ψ.realization_character] using
    FDRep.char_orthonormal χ.realization ψ.realization

/-- Every irreducible character has normalized self-pairing one. -/
theorem pairingFunctional_self [Fintype G] (χ : IrreducibleCharacter G) :
    χ.pairingFunctional χ.values = 1 := by
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hself : Nonempty (χ.realization ≅ χ.realization) := ⟨Iso.refl _⟩
  simpa [pairingFunctional, χ.realization_character, hself] using
    FDRep.char_orthonormal χ.realization χ.realization

/-- The value functions of the irreducible complex characters of a finite group
are linearly independent. -/
theorem linearIndependent_values [Finite G] :
    LinearIndependent ℂ (fun χ : IrreducibleCharacter G ↦ χ.values) := by
  letI : Fintype G := Fintype.ofFinite G
  refine LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun ψ ↦ ψ.pairingFunctional) (fun χ ψ hχψ ↦ ?_) (fun χ ↦ ?_)
  · exact pairingFunctional_eq_zero_of_ne ψ χ (Ne.symm hχψ)
  · exact pairingFunctional_self χ

/-- A finite group has only finitely many irreducible complex characters. -/
instance instFiniteIrreducibleCharacter [Finite G] :
    Finite (IrreducibleCharacter G) :=
  (linearIndependent_values (G := G)).finite

/-- The number of irreducible characters is at most the order of the group.

This follows by placing their linearly independent value functions in `G → ℂ`.
The sharper bound by the number of conjugacy classes requires a bundled
class-function API.
-/
theorem natCard_le_group_order [Finite G] :
    Nat.card (IrreducibleCharacter G) ≤ Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  calc
    Nat.card (IrreducibleCharacter G) = Fintype.card (IrreducibleCharacter G) :=
      Nat.card_eq_fintype_card
    _ ≤ Module.finrank ℂ (G → ℂ) :=
      (linearIndependent_values (G := G)).fintype_card_le_finrank
    _ = Fintype.card G := Module.finrank_fintype_fun_eq_card ℂ
    _ = Nat.card G := Nat.card_eq_fintype_card.symm

end McKayConjecture.IrreducibleCharacter

namespace McKayConjecture

variable {G : Type u} [Group G]

/-- The `p'`-degree irreducible characters of a finite group form a finite type. -/
instance instFinitePPrimeIrreducibleCharacter [Finite G] (p : ℕ) :
    Finite (PPrimeIrreducibleCharacter G p) :=
  Finite.of_injective Subtype.val Subtype.coe_injective

end McKayConjecture
