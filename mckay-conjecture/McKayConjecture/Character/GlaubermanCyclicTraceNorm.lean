/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionCompleteness
import McKayConjecture.Character.GlaubermanCyclicCosetAverage
import McKayConjecture.Character.GlaubermanCyclicCosetOrthogonality
import McKayConjecture.Character.GlaubermanCyclicTracePairing
import McKayConjecture.Character.InverseConjugate
import McKayConjecture.Character.SignedIrreducibilityCriterion

/-!
# Norm one for the cyclic Glauberman trace

This file combines the generator-coset character orthogonality theorem
with the cyclic coset class-counting formula. Once the cyclic trace has
an integral irreducible-character expansion, inversion of ordinary
characters is complex conjugation, so the Hermitian coset norm becomes
the normalized bilinear self-pairing of the trace. The result is one.

Consequently, coefficient integrality is the sole remaining
character-theoretic input needed to conclude that the cyclic trace is a
signed irreducible character.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace McKayConjecture

namespace IrreducibleCharacter

variable {H : Type} [Group H] [Finite H]

/-- Integral generalized characters take complex-conjugate values on
inverse elements. -/
theorem integerCharacterCombination_inv_eq_conj
    (coeff : IrreducibleCharacter H → ℤ)
    (x : H) :
    integerCharacterCombination coeff x⁻¹ =
      conj (integerCharacterCombination coeff x) := by
  classical
  letI : Fintype (IrreducibleCharacter H) :=
    Fintype.ofFinite _
  rw [integerCharacterCombination]
  change
    ClassFunction.coeLinearMap
        (∑ chi : IrreducibleCharacter H,
          (coeff chi : ℂ) • chi.toClassFunction) x⁻¹ =
      conj
        (ClassFunction.coeLinearMap
          (∑ chi : IrreducibleCharacter H,
            (coeff chi : ℂ) • chi.toClassFunction) x)
  simp only [map_sum, map_smul]
  simp only [Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro chi _
  rw [map_mul, map_intCast]
  change
    (coeff chi : ℂ) * chi.values x⁻¹ =
      (coeff chi : ℂ) * conj (chi.values x)
  rw [value_inv_eq_conj]

end IrreducibleCharacter

variable {G : Type} [Group G] [Finite G]

/-- The ambient class function `x ↦ χ(x) χ(x⁻¹)`. -/
def irreducibleCharacterBilinearNormClassFunction
    (chi : IrreducibleCharacter G) :
    ClassFunction G :=
  ⟨fun x ↦ chi.values x * chi.values x⁻¹, by
    intro x a
    change
      chi.toClassFunction (a * x * a⁻¹) *
          chi.toClassFunction (a * x * a⁻¹)⁻¹ =
        chi.toClassFunction x *
          chi.toClassFunction x⁻¹
    rw [conj_inv,
      ClassFunction.conj_apply,
      ClassFunction.conj_apply]⟩

omit [Finite G] in
@[simp]
theorem irreducibleCharacterBilinearNormClassFunction_apply
    (chi : IrreducibleCharacter G) (x : G) :
    irreducibleCharacterBilinearNormClassFunction chi x =
      chi.values x * chi.values x⁻¹ :=
  rfl

variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

theorem
    normalizedPairing_determinantNormalizedCyclicTrace_eq_one_of_integerExpansion
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (coeff :
      IrreducibleCharacter
        (cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G)) → ℤ)
    (hexpansion :
      determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ =
        IrreducibleCharacter.integerCharacterCombination
          coeff) :
    ClassFunction.normalizedPairing
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ)
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ) =
      1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype K := Fintype.ofFinite K
  let C : Type :=
    cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)
  letI : Fintype C := Fintype.ofFinite C
  let chi : IrreducibleCharacter G :=
    determinantNormalizedCyclicExtensionCharacter
      K P hK hP hgenerate θ
  let F : ClassFunction G :=
    irreducibleCharacterBilinearNormClassFunction chi
  have havg :=
    cyclicGeneratorCoset_classFunction_sum
      K P hK hP hgenerate F
  have hcoset :=
    determinantNormalizedCyclicExtension_generatorCoset_bilinearNorm
      K P hK hP hgenerate θ
  change
    (Nat.card C : ℂ) *
        ∑ k : K, F
          (((cyclicSubgroupGenerator P : P) : G) *
            (k : G)) =
      (Nat.card K : ℂ) *
        ∑ c : C, F
          (((cyclicSubgroupGenerator P : P) : G) *
            (c : G)) at havg
  change
    ∑ k : K, F
        (((cyclicSubgroupGenerator P : P) : G) *
          (k : G)) =
      (Nat.card K : ℂ) at hcoset
  rw [hcoset] at havg
  have hKne : (Nat.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card K).ne'
  have hfixed :
      (∑ c : C, F
          (((cyclicSubgroupGenerator P : P) : G) *
            (c : G))) =
        (Nat.card C : ℂ) := by
    apply mul_left_cancel₀ hKne
    calc
      (Nat.card K : ℂ) *
            ∑ c : C, F
              (((cyclicSubgroupGenerator P : P) : G) *
                (c : G)) =
          (Nat.card C : ℂ) *
            (Nat.card K : ℂ) :=
        havg.symm
      _ =
          (Nat.card K : ℂ) *
            (Nat.card C : ℂ) := by
        ring
  change
    (Nat.card C : ℂ)⁻¹ *
        ∑ c : C,
          determinantNormalizedCyclicTrace
              K P hK hP hgenerate θ c *
            determinantNormalizedCyclicTrace
              K P hK hP hgenerate θ c⁻¹ =
      1
  have htraceInv (c : C) :
      determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ c⁻¹ =
        chi.values
          ((((cyclicSubgroupGenerator P : P) : G) *
            (c : G))⁻¹) := by
    calc
      determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ c⁻¹ =
          conj
            (determinantNormalizedCyclicTrace
              K P hK hP hgenerate θ c) := by
        rw [hexpansion]
        exact
          IrreducibleCharacter.integerCharacterCombination_inv_eq_conj
            coeff c
      _ =
          conj
            (chi.values
              (((cyclicSubgroupGenerator P : P) : G) *
                (c : G))) := by
        rw [
          determinantNormalizedCyclicTrace_eq_extensionCharacter]
      _ =
          chi.values
            ((((cyclicSubgroupGenerator P : P) : G) *
              (c : G))⁻¹) := by
        rw [IrreducibleCharacter.value_inv_eq_conj]
  simp_rw [htraceInv]
  simp_rw [
    determinantNormalizedCyclicTrace_eq_extensionCharacter]
  change
    (Nat.card C : ℂ)⁻¹ *
        ∑ c : C, F
          (((cyclicSubgroupGenerator P : P) : G) *
            (c : G)) =
      1
  rw [hfixed]
  exact inv_mul_cancel₀
    (by
      exact_mod_cast
        (Nat.card_pos : 0 < Nat.card C).ne')

/-- An integral expansion of the cyclic trace, together with the coset
norm formula, forces the trace to be a signed irreducible character. -/
theorem
    determinantNormalizedCyclicTrace_eq_signedIrreducible_of_integerExpansion
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (coeff :
      IrreducibleCharacter
        (cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G)) → ℤ)
    (hexpansion :
      determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ =
        IrreducibleCharacter.integerCharacterCombination
          coeff) :
    ∃ psi :
        IrreducibleCharacter
          (cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G)),
      determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ =
          psi.toClassFunction ∨
        determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ =
          -psi.toClassFunction :=
  IrreducibleCharacter.eq_signedIrreducible_of_integerExpansion_pairing_eq_one
    (determinantNormalizedCyclicTrace
      K P hK hP hgenerate θ)
    coeff hexpansion
    (normalizedPairing_determinantNormalizedCyclicTrace_eq_one_of_integerExpansion
      K P hK hP hgenerate θ coeff hexpansion)

/-- If every irreducible Fourier coefficient of the cyclic trace is an
integer, then the cyclic trace is signed irreducible. -/
theorem
    determinantNormalizedCyclicTrace_eq_signedIrreducible_of_pairings_integral
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hintegral :
      ∀ psi :
          IrreducibleCharacter
            (cyclicFixedPoints K
              ((cyclicSubgroupGenerator P : P) : G)),
        ∃ z : ℤ,
          ClassFunction.normalizedPairing
              (determinantNormalizedCyclicTrace
                K P hK hP hgenerate θ)
              psi.toClassFunction =
            (z : ℂ)) :
    ∃ psi :
        IrreducibleCharacter
          (cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G)),
      determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ =
          psi.toClassFunction ∨
        determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ =
          -psi.toClassFunction := by
  obtain ⟨coeff, hexpansion⟩ :=
    ClassFunction.exists_integerCharacterCombination_of_pairings_integral
      (determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ)
      hintegral
  exact
    determinantNormalizedCyclicTrace_eq_signedIrreducible_of_integerExpansion
      K P hK hP hgenerate θ coeff hexpansion

end McKayConjecture
