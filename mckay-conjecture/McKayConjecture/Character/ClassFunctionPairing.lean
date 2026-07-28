/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunction

/-!
# The normalized pairing on complex class functions

For a finite group `G`, the bilinear pairing

`(f, k) ↦ |G|⁻¹ ∑ g, f(g) k(g⁻¹)`

makes the irreducible characters orthonormal.  Bundling it as a linear map
in both variables lets finite character expansions be evaluated by ordinary
linear algebra.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The normalized bilinear pairing on complex class functions. -/
def normalizedPairing :
    ClassFunction G →ₗ[ℂ]
      ClassFunction G →ₗ[ℂ] ℂ := by
  letI : Fintype G := Fintype.ofFinite G
  refine LinearMap.mk₂ ℂ
    (fun f k ↦
      (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, f g * k g⁻¹) ?_ ?_ ?_ ?_
  · intro f₁ f₂ k
    simp only [AddMemClass.coe_add, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
    ring
  · intro c f k
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  · intro f k₁ k₂
    simp only [AddMemClass.coe_add, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  · intro c f k
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring

/-- Distinct irreducible characters are orthogonal for the normalized
class-function pairing. -/
theorem normalizedPairing_irreducible_eq_zero_of_ne
    (χ ψ : IrreducibleCharacter G)
    (hχψ : χ ≠ ψ) :
    normalizedPairing χ.toClassFunction ψ.toClassFunction = 0 := by
  letI : Fintype G := Fintype.ofFinite G
  exact
    IrreducibleCharacter.pairingFunctional_eq_zero_of_ne
      χ ψ hχψ

/-- Every irreducible character has normalized self-pairing one. -/
@[simp]
theorem normalizedPairing_irreducible_self
    (χ : IrreducibleCharacter G) :
    normalizedPairing χ.toClassFunction χ.toClassFunction = 1 := by
  letI : Fintype G := Fintype.ofFinite G
  exact IrreducibleCharacter.pairingFunctional_self χ

/-- The normalized pairing is symmetric. -/
theorem normalizedPairing_comm
    (f k : ClassFunction G) :
    normalizedPairing f k =
      normalizedPairing k f := by
  letI : Fintype G := Fintype.ofFinite G
  change
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * k g⁻¹ =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, k g * f g⁻¹
  congr 1
  calc
    (∑ g : G, f g * k g⁻¹) =
        ∑ g : G, f g⁻¹ * k g := by
      simpa using
        (Function.Bijective.sum_comp
          (Equiv.inv G).bijective
          (fun g : G ↦ f g⁻¹ * k g))
    _ = ∑ g : G, k g * f g⁻¹ := by
      apply Finset.sum_congr rfl
      intro g _hg
      ring

end ClassFunction
end McKayConjecture
