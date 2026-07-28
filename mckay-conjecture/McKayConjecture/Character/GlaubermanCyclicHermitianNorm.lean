/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionHermitian
import McKayConjecture.Character.GlaubermanCyclicCosetAverage
import McKayConjecture.Character.GlaubermanCyclicCosetOrthogonality

/-!
# Unconditional Hermitian norm of the cyclic Glauberman trace

Coset orthogonality computes the Hermitian norm of the
determinant-normalized cyclic trace without any integrality or
rationality hypothesis.  Parseval then says that the sum of squared
norms of all irreducible Fourier coefficients is one.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- The unnormalized Hermitian norm sum of the
determinant-normalized cyclic trace. -/
def determinantNormalizedCyclicTraceHermitianSum
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ℂ := by
  letI : Fintype
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
    Fintype.ofFinite _
  exact
    ∑ c :
        cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G),
      determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ c *
        conj
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ c)

/-- The unnormalized Hermitian norm of the determinant-normalized
cyclic trace is the order of the fixed-point group. -/
theorem
    sum_determinantNormalizedCyclicTrace_mul_conj_eq_card_fixedPoints
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    determinantNormalizedCyclicTraceHermitianSum
        K P hK hP hgenerate θ =
      (Nat.card
        (cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G)) : ℂ) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype K := Fintype.ofFinite K
  let C : Type :=
    cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)
  letI : Fintype C := Fintype.ofFinite C
  rw [determinantNormalizedCyclicTraceHermitianSum]
  let chi : IrreducibleCharacter G :=
    determinantNormalizedCyclicExtensionCharacter
      K P hK hP hgenerate θ
  let F : ClassFunction G :=
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
    ∑ c : C,
      determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ c *
        conj
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ c) =
      (Nat.card C : ℂ)
  calc
    ∑ c : C,
          determinantNormalizedCyclicTrace
              K P hK hP hgenerate θ c *
            conj
              (determinantNormalizedCyclicTrace
                K P hK hP hgenerate θ c) =
        ∑ c : C, F
          (((cyclicSubgroupGenerator P : P) : G) *
            (c : G)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [
        determinantNormalizedCyclicTrace_eq_extensionCharacter]
      change
        chi.values
              (((cyclicSubgroupGenerator P : P) : G) *
                (c : G)) *
            conj
              (chi.values
                (((cyclicSubgroupGenerator P : P) : G) *
                  (c : G))) =
          chi.values
              (((cyclicSubgroupGenerator P : P) : G) *
                (c : G)) *
            chi.values
              ((((cyclicSubgroupGenerator P : P) : G) *
                (c : G))⁻¹)
      rw [IrreducibleCharacter.value_inv_eq_conj]
    _ = (Nat.card C : ℂ) :=
      hfixed

/-- The normalized Hermitian norm of the determinant-normalized cyclic
trace is one, unconditionally. -/
theorem
    normalizedHermitianPairing_determinantNormalizedCyclicTrace_eq_one
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ClassFunction.normalizedHermitianPairing
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ)
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ) =
      1 := by
  let C : Type :=
    cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)
  letI : Fintype C := Fintype.ofFinite C
  change
    (Nat.card C : ℂ)⁻¹ *
        determinantNormalizedCyclicTraceHermitianSum
          K P hK hP hgenerate θ =
      1
  rw [
    sum_determinantNormalizedCyclicTrace_mul_conj_eq_card_fixedPoints]
  exact
    inv_mul_cancel₀
      (by
        exact_mod_cast
          (Nat.card_pos : 0 < Nat.card C).ne')

/-- Parseval: the squared norms of all irreducible Fourier
coefficients of the cyclic trace sum to one. -/
theorem
    determinantNormalizedCyclicTrace_fourierCoefficientNormSqSum_eq_one
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ClassFunction.fourierCoefficientNormSqSum
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ) =
      1 := by
  rw [←
    ClassFunction.normalizedHermitianPairing_self_eq_fourierCoefficientNormSqSum]
  exact
    normalizedHermitianPairing_determinantNormalizedCyclicTrace_eq_one
      K P hK hP hgenerate θ

end McKayConjecture
