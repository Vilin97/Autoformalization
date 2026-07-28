/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionCoefficientLattice

/-!
# Prime-power reduction for elementary Brauer induction

The coefficient-lattice proof of Brauer induction only needs a congruence
for the irreducible basis vectors.  Additivity then gives the congruence
for every integral coefficient vector, and arithmetic separation makes the
elementary-induction lattice equal to the full lattice.

The predicate `HasElementaryPrimePowerBasisApproximation` below isolates
the remaining representation-theoretic step of the standard proof.  It is
an ordinary proposition whose witnesses later files must construct.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G]

/-- A coefficient vector is congruent modulo `p ^ n` to an element of the
elementary-induction lattice. -/
def IsElementaryCoefficientCongruent
    (p n : ℕ) (v : IrreducibleCharacter G → ℤ) : Prop :=
  ∃ w ∈ elementaryInductionLattice (G := G),
    ∃ y : IrreducibleCharacter G → ℤ,
      v = w + p ^ n • y

/-- The zero coefficient vector has every elementary congruence. -/
theorem isElementaryCoefficientCongruent_zero
    (p n : ℕ) :
    IsElementaryCoefficientCongruent
      (G := G) p n 0 := by
  refine ⟨0, (elementaryInductionLattice (G := G)).zero_mem, 0, ?_⟩
  simp

/-- Elementary coefficient congruences are closed under addition. -/
theorem IsElementaryCoefficientCongruent.add
    {p n : ℕ}
    {v₁ v₂ : IrreducibleCharacter G → ℤ}
    (h₁ : IsElementaryCoefficientCongruent
      (G := G) p n v₁)
    (h₂ : IsElementaryCoefficientCongruent
      (G := G) p n v₂) :
    IsElementaryCoefficientCongruent
      (G := G) p n (v₁ + v₂) := by
  obtain ⟨w₁, hw₁, y₁, hv₁⟩ := h₁
  obtain ⟨w₂, hw₂, y₂, hv₂⟩ := h₂
  refine
    ⟨w₁ + w₂,
      (elementaryInductionLattice (G := G)).add_mem hw₁ hw₂,
      y₁ + y₂, ?_⟩
  rw [hv₁, hv₂]
  simp only [nsmul_add]
  abel

/-- Elementary coefficient congruences are closed under integral scalar
multiplication. -/
theorem IsElementaryCoefficientCongruent.zsmul
    {p n : ℕ}
    {v : IrreducibleCharacter G → ℤ}
    (h : IsElementaryCoefficientCongruent
      (G := G) p n v)
    (a : ℤ) :
    IsElementaryCoefficientCongruent
      (G := G) p n (a • v) := by
  obtain ⟨w, hw, y, hv⟩ := h
  refine
    ⟨a • w,
      (elementaryInductionLattice (G := G)).zsmul_mem hw a,
      a • y, ?_⟩
  rw [hv, smul_add]
  simp only [zsmul_eq_mul, nsmul_eq_mul]
  funext χ
  dsimp only [Pi.add_apply, Pi.mul_apply]
  ring

/-- A finite sum of coefficient vectors satisfying an elementary
congruence satisfies the same congruence. -/
theorem isElementaryCoefficientCongruent_sum
    {ι : Type*} {s : Finset ι}
    {p n : ℕ}
    (v : ι → IrreducibleCharacter G → ℤ)
    (h :
      ∀ i ∈ s,
        IsElementaryCoefficientCongruent
          (G := G) p n (v i)) :
    IsElementaryCoefficientCongruent
      (G := G) p n (∑ i ∈ s, v i) := by
  classical
  exact
    Finset.sum_induction v
      (fun x =>
        IsElementaryCoefficientCongruent
          (G := G) p n x)
      (fun _x₁ _x₂ hx₁ hx₂ => hx₁.add hx₂)
      (isElementaryCoefficientCongruent_zero p n)
      h

variable [Finite G]

noncomputable local instance brauerPrimePowerFintypeG :
    Fintype G :=
  Fintype.ofFinite _

noncomputable local instance brauerPrimePowerFintypeIrr :
    Fintype (IrreducibleCharacter G) :=
  Fintype.ofFinite _

/-- The deep input isolated by the coefficient-lattice proof: every
irreducible basis vector can be approximated by elementary inductions
modulo every prime power. -/
def HasElementaryPrimePowerBasisApproximation : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ n : ℕ,
    ∀ χ : IrreducibleCharacter G,
      IsElementaryCoefficientCongruent
        (G := G) p n (irreducibleCoefficient χ)

/-- Basis-vector prime-power approximation implies approximation of every
integral coefficient vector. -/
theorem mod_prime_power_coefficients_of_basis_approximation
    (happrox :
      HasElementaryPrimePowerBasisApproximation (G := G))
    (p : ℕ) (hp : p.Prime) (n : ℕ)
    (v : IrreducibleCharacter G → ℤ) :
    IsElementaryCoefficientCongruent
      (G := G) p n v := by
  rw [← sum_smul_irreducibleCoefficient v]
  exact
    isElementaryCoefficientCongruent_sum
      (fun χ =>
        v χ • irreducibleCoefficient χ)
      (fun χ _hχ =>
        (happrox p hp n χ).zsmul (v χ))

/-- The basis-level prime-power approximation is sufficient for
denominator-one elementary Brauer induction. -/
theorem hasElementaryBrauerInduction_of_prime_power_basis_approximation
    (happrox :
      HasElementaryPrimePowerBasisApproximation (G := G)) :
    HasElementaryBrauerInduction (G := G) :=
  hasElementaryBrauerInduction_of_mod_prime_power_coefficients
    fun p hp n v =>
      mod_prime_power_coefficients_of_basis_approximation
        happrox p hp n v

/-- Brauer induction itself supplies the prime-power approximation: take
the basis vector as the lattice representative and zero as the error. -/
theorem prime_power_basis_approximation_of_hasElementaryBrauerInduction
    (hind : HasElementaryBrauerInduction (G := G)) :
    HasElementaryPrimePowerBasisApproximation (G := G) := by
  rw [hasElementaryBrauerInduction_iff_irreducibleCoefficient_mem] at hind
  intro p _hp n χ
  refine
    ⟨irreducibleCoefficient χ, hind χ, 0, ?_⟩
  simp

/-- The prime-power basis approximation is an exact arithmetic
reformulation of denominator-one elementary Brauer induction. -/
theorem
    hasElementaryBrauerInduction_iff_prime_power_basis_approximation :
    HasElementaryBrauerInduction (G := G) ↔
      HasElementaryPrimePowerBasisApproximation (G := G) :=
  ⟨prime_power_basis_approximation_of_hasElementaryBrauerInduction,
    hasElementaryBrauerInduction_of_prime_power_basis_approximation⟩

end ClassFunction
end McKayConjecture
