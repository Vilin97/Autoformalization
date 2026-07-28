/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionPairing

/-!
# An integral norm-one criterion for signed irreducibility

The cyclic step in Glauberman's proof first expands the canonical
generator-coset trace as an integral linear combination of irreducible
characters of the fixed-point subgroup.  A separate coset-orthogonality
calculation says that the sum of the squares of those integral
coefficients is one.  The conclusion that the trace is a signed
irreducible character is then elementary.

This file formalizes that final elementary implication.  It cleanly
separates the two substantive inputs still needed for the noncommutative
cyclic case:

* integrality of the Fourier coefficients of the coset trace;
* the coset norm identity.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type} [Group G] [Finite G]

/-- The generalized character with integral irreducible coefficients
`c`. -/
def integerCharacterCombination
    (c : IrreducibleCharacter G → ℤ) :
    ClassFunction G := by
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  exact
    ∑ χ : IrreducibleCharacter G,
      (c χ : ℂ) • χ.toClassFunction

/-- The integral squared norm of a coefficient family. -/
def integerCoefficientSqSum
    (c : IrreducibleCharacter G → ℤ) :
    ℤ := by
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  exact
    ∑ χ : IrreducibleCharacter G, (c χ) ^ 2

/-- The same squared norm, computed from natural absolute values. -/
def integerCoefficientNatAbsSqSum
    (c : IrreducibleCharacter G → ℤ) :
    ℕ := by
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  exact
    ∑ χ : IrreducibleCharacter G,
      (c χ).natAbs ^ 2

/-- An integral squared norm of one is also a natural-absolute-value
squared norm of one. -/
theorem natAbsSqSum_eq_one_of_sqSum_eq_one
    (c : IrreducibleCharacter G → ℤ)
    (h : integerCoefficientSqSum c = 1) :
    integerCoefficientNatAbsSqSum c = 1 := by
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  rw [integerCoefficientSqSum] at h
  rw [integerCoefficientNatAbsSqSum]
  apply Nat.cast_injective (R := ℤ)
  push_cast
  simpa only [sq_abs] using h

/-- A finite family of integers whose squared norm is one has exactly
one nonzero coefficient, and that coefficient is `1` or `-1`. -/
theorem integerCoefficientPattern_of_natAbsSqSum_eq_one
    (c : IrreducibleCharacter G → ℤ)
    (h : integerCoefficientNatAbsSqSum c = 1) :
    ∃ χ : IrreducibleCharacter G,
      (c χ = 1 ∨ c χ = -1) ∧
      ∀ ψ : IrreducibleCharacter G,
        ψ ≠ χ → c ψ = 0 := by
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  classical
  rw [integerCoefficientNatAbsSqSum] at h
  let d : IrreducibleCharacter G →₀ ℕ :=
    (Finsupp.equivFunOnFinite).symm
      (fun χ ↦ (c χ).natAbs ^ 2)
  have hd :
      d.sum (fun _ n ↦ n) = 1 := by
    simpa [d, Finsupp.sum_fintype] using h
  obtain ⟨χ, hdχ⟩ :=
    (Finsupp.sum_eq_one_iff d).mp hd
  refine ⟨χ, ?_, ?_⟩
  · have hsq :
        (c χ).natAbs ^ 2 = 1 := by
      have hχ :=
        congrArg
          (fun z :
            IrreducibleCharacter G →₀ ℕ ↦ z χ)
          hdχ
      simpa [d] using hχ
    have habs :
        (c χ).natAbs = 1 :=
      (Nat.pow_eq_one.mp hsq).resolve_right
        (by decide)
    exact Int.natAbs_eq_iff.mp habs
  · intro ψ hne
    have hsq :
        (c ψ).natAbs ^ 2 = 0 := by
      have hψ :=
        congrArg
          (fun z :
            IrreducibleCharacter G →₀ ℕ ↦ z ψ)
          hdχ
      simpa [d, hne] using hψ
    exact
      Int.natAbs_eq_zero.mp
        (sq_eq_zero_iff.mp hsq)

/-- An integral combination with coefficient squared norm one is a
signed irreducible character. -/
theorem
    integerCharacterCombination_eq_signedIrreducible_of_sqSum_eq_one
    (c : IrreducibleCharacter G → ℤ)
    (h : integerCoefficientSqSum c = 1) :
    ∃ χ : IrreducibleCharacter G,
      integerCharacterCombination c =
          χ.toClassFunction ∨
        integerCharacterCombination c =
          -χ.toClassFunction := by
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  classical
  obtain ⟨χ, hsign, hzero⟩ :=
    integerCoefficientPattern_of_natAbsSqSum_eq_one
      c
      (natAbsSqSum_eq_one_of_sqSum_eq_one c h)
  refine ⟨χ, ?_⟩
  rw [integerCharacterCombination,
    Finset.sum_eq_single χ]
  · rcases hsign with hpos | hneg
    · left
      simp [hpos]
    · right
      rw [hneg, Int.cast_neg, Int.cast_one]
      exact neg_one_smul ℂ χ.toClassFunction
  · intro ψ _ hne
    rw [hzero ψ hne]
    simp
  · simp

/-- A class function with an integral irreducible expansion of squared
coefficient norm one is signed irreducible. -/
theorem eq_signedIrreducible_of_integerExpansion_sqSum_eq_one
    (f : ClassFunction G)
    (c : IrreducibleCharacter G → ℤ)
    (hexpansion :
      f = integerCharacterCombination c)
    (hnorm : integerCoefficientSqSum c = 1) :
    ∃ χ : IrreducibleCharacter G,
      f = χ.toClassFunction ∨
        f = -χ.toClassFunction := by
  obtain ⟨χ, hχ⟩ :=
    integerCharacterCombination_eq_signedIrreducible_of_sqSum_eq_one
      c hnorm
  rcases hχ with hχ | hχ
  · exact ⟨χ, Or.inl (hexpansion.trans hχ)⟩
  · exact ⟨χ, Or.inr (hexpansion.trans hχ)⟩

/-- The Fourier coefficient of an integral irreducible-character
combination is the corresponding integer coefficient. -/
theorem normalizedPairing_integerCharacterCombination_irreducible
    (c : IrreducibleCharacter G → ℤ)
    (χ : IrreducibleCharacter G) :
    ClassFunction.normalizedPairing
        (integerCharacterCombination c)
        χ.toClassFunction =
      (c χ : ℂ) := by
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  classical
  rw [integerCharacterCombination]
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single χ]
  · simp
  · intro ψ _hψ hne
    rw [
      ClassFunction.normalizedPairing_irreducible_eq_zero_of_ne
        ψ χ hne]
    simp
  · simp

/-- Orthogonality identifies the normalized self-pairing of an integral
character combination with the complex cast of the squared coefficient
sum. -/
theorem normalizedPairing_integerCharacterCombination
    (c : IrreducibleCharacter G → ℤ) :
    ClassFunction.normalizedPairing
        (integerCharacterCombination c)
        (integerCharacterCombination c) =
      (integerCoefficientSqSum c : ℂ) := by
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  classical
  rw [integerCharacterCombination,
    integerCoefficientSqSum]
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  have hinner :
      ∀ χ : IrreducibleCharacter G,
        (∑ ψ : IrreducibleCharacter G,
            (c ψ : ℂ) *
              ClassFunction.normalizedPairing
                ψ.toClassFunction χ.toClassFunction) =
          (c χ : ℂ) := by
    intro χ
    rw [Finset.sum_eq_single χ]
    · simp
    · intro ψ _hψ hne
      rw [
        ClassFunction.normalizedPairing_irreducible_eq_zero_of_ne
          ψ χ hne]
      simp
    · simp
  simp_rw [hinner]
  push_cast
  apply Finset.sum_congr rfl
  intro χ _hχ
  ring

/-- An integral irreducible expansion and normalized self-pairing one
already force signed irreducibility. -/
theorem eq_signedIrreducible_of_integerExpansion_pairing_eq_one
    (f : ClassFunction G)
    (c : IrreducibleCharacter G → ℤ)
    (hexpansion :
      f = integerCharacterCombination c)
    (hnorm :
      ClassFunction.normalizedPairing f f = 1) :
    ∃ χ : IrreducibleCharacter G,
      f = χ.toClassFunction ∨
        f = -χ.toClassFunction := by
  have hcast :
      (integerCoefficientSqSum c : ℂ) = 1 := by
    rw [hexpansion,
      normalizedPairing_integerCharacterCombination] at hnorm
    exact hnorm
  have hsq :
      integerCoefficientSqSum c = 1 := by
    exact_mod_cast hcast
  exact
    eq_signedIrreducible_of_integerExpansion_sqSum_eq_one
      f c hexpansion hsq

end IrreducibleCharacter
end McKayConjecture
