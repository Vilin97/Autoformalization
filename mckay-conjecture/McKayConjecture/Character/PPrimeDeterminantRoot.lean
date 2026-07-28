/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Data.Int.GCD
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Determinant

/-!
# Recovering central scalars from a prime-to-order determinant

Let a finite group `H` act through a representation of dimension `d`,
with `d` coprime to `|H|`.  The determinant of the restricted action,
raised to a Bézout inverse of `d` modulo `|H|`, is a linear character of
`H`.  At elements whose ambient action is scalar, this linear character
recovers that scalar exactly.

This elementary determinant-root construction is the normalization used
when extending a Glauberman correspondent across a Sylow direct factor.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

variable {G : Type u} [Group G]

/-- The determinant of the chosen realization, with no degree-one
assumption. -/
def determinantParameter (χ : IrreducibleCharacter G) :
    G →* ℂˣ :=
  LinearEquiv.det.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv
        ℂ χ.realization).toMonoidHom.comp
      χ.realization.ρ.toHomUnits)

@[simp]
theorem determinantParameter_eq_det
    (χ : IrreducibleCharacter G) (g : G) :
    ((determinantParameter χ g : ℂˣ) : ℂ) =
      LinearMap.det
        (χ.realization.ρ g :
          χ.realization →ₗ[ℂ] χ.realization) := by
  simp [determinantParameter, LinearEquiv.coe_det]

/-- The determinant of a scalar action is the scalar raised to the
character degree. -/
theorem determinantParameter_eq_scalar_pow
    (χ : IrreducibleCharacter G) (g : G) (c : ℂ)
    (hc :
      χ.realization.ρ g =
        c • (LinearMap.id :
          Module.End ℂ χ.realization)) :
    ((determinantParameter χ g : ℂˣ) : ℂ) =
      c ^ χ.degree := by
  rw [determinantParameter_eq_det, hc,
    LinearMap.det_smul, LinearMap.det_id, mul_one,
    χ.realization_finrank]

variable {H : Type v} [Group H] [Finite H]

/-- A scalar action of an element from a finite source group has order
dividing the order of that source group. -/
theorem scalar_pow_natCard_eq_one
    (χ : IrreducibleCharacter G)
    (f : H →* G) (h : H) (c : ℂ)
    (hc :
      χ.realization.ρ (f h) =
        c • (LinearMap.id :
          Module.End ℂ χ.realization)) :
    c ^ Nat.card H = 1 := by
  have hrho :
      (χ.realization.ρ (f h)) ^ Nat.card H = 1 := by
    calc
      (χ.realization.ρ (f h)) ^ Nat.card H =
          χ.realization.ρ ((f h) ^ Nat.card H) := by
        rw [map_pow]
      _ = χ.realization.ρ (f (h ^ Nat.card H)) := by
        exact congrArg χ.realization.ρ
          (map_pow f h (Nat.card H)).symm
      _ = χ.realization.ρ (f 1) := by
        rw [pow_card_eq_one']
      _ = 1 := by simp
  have hscalarPow :
      (c • (LinearMap.id :
          Module.End ℂ χ.realization)) ^ Nat.card H =
        c ^ Nat.card H •
          (LinearMap.id :
            Module.End ℂ χ.realization) := by
    induction Nat.card H with
    | zero =>
        simp [Module.End.one_eq_id]
    | succ n ih =>
        rw [pow_succ, ih, pow_succ]
        apply LinearMap.ext
        intro x
        simp [smul_smul, mul_comm]
  have hmaps :
      c ^ Nat.card H •
          (LinearMap.id :
            Module.End ℂ χ.realization) =
        LinearMap.id := by
    rw [← hscalarPow, ← hc, hrho]
    rfl
  letI : Nontrivial χ.realization :=
    CliffordRestriction.nontrivial_of_simple
      χ.realization
  obtain ⟨x : χ.realization, hx⟩ :=
    exists_ne (0 : χ.realization)
  have happly :=
    LinearMap.congr_fun hmaps x
  have hsmul :
      c ^ Nat.card H • x = (1 : ℂ) • x := by
    simpa using happly
  exact
    (smul_left_injective ℂ hx) hsmul

/-- The scalar in the preceding lemma is nonzero. -/
theorem scalar_ne_zero_of_finite_source
    (χ : IrreducibleCharacter G)
    (f : H →* G) (h : H) (c : ℂ)
    (hc :
      χ.realization.ρ (f h) =
        c • (LinearMap.id :
          Module.End ℂ χ.realization)) :
    c ≠ 0 := by
  intro hzero
  have hpow :=
    scalar_pow_natCard_eq_one χ f h c hc
  have hn : Nat.card H ≠ 0 :=
    (Nat.card_ne_zero).2
      ⟨⟨1⟩, inferInstance⟩
  rw [hzero] at hpow
  simpa [zero_pow hn] using hpow

/-- Bézout inversion in a group: if `x^n = 1` and `n` is coprime to
`d`, then `x` is the Bézout power of `x^d`. -/
theorem eq_pow_gcdB_of_pow_eq_one
    {A : Type} [Group A]
    (x : A) (n d : ℕ)
    (hcoprime : n.Coprime d)
    (horder : x ^ n = 1) :
    x = (x ^ d) ^ n.gcdB d := by
  have key :=
    congrArg (x ^ ·) (n.gcd_eq_gcd_ab d)
  rw [hcoprime.gcd_eq_one] at key
  simpa only [zpow_add, zpow_mul,
    zpow_natCast, pow_one, horder,
    one_zpow, one_mul] using key

/-- The determinant character with the degree exponent inverted modulo
the order of the finite source group. -/
def determinantRootParameter
    (χ : IrreducibleCharacter G)
    (f : H →* G)
    (hcoprime : (Nat.card H).Coprime χ.degree) :
    H →* ℂˣ :=
  ((determinantParameter χ).comp f) ^
    (Nat.card H).gcdB χ.degree

/-- At a scalar element, the determinant-root character recovers the
scalar as a complex unit. -/
theorem determinantRootParameter_eq_scalarUnit
    (χ : IrreducibleCharacter G)
    (f : H →* G)
    (hcoprime : (Nat.card H).Coprime χ.degree)
    (h : H) (c : ℂ)
    (hc :
      χ.realization.ρ (f h) =
        c • (LinearMap.id :
          Module.End ℂ χ.realization)) :
    determinantRootParameter χ f hcoprime h =
      Units.mk0 c
        (scalar_ne_zero_of_finite_source
          χ f h c hc) := by
  let cu : ℂˣ :=
    Units.mk0 c
      (scalar_ne_zero_of_finite_source
        χ f h c hc)
  have hcuOrder :
      cu ^ Nat.card H = 1 := by
    apply Units.ext
    simpa [cu] using
      scalar_pow_natCard_eq_one χ f h c hc
  have hdet :
      determinantParameter χ (f h) =
        cu ^ χ.degree := by
    apply Units.ext
    simpa [cu] using
      determinantParameter_eq_scalar_pow
        χ (f h) c hc
  have hroot :
      cu =
        (cu ^ χ.degree) ^
          (Nat.card H).gcdB χ.degree :=
    eq_pow_gcdB_of_pow_eq_one
      cu (Nat.card H) χ.degree
      hcoprime hcuOrder
  change
    (determinantParameter χ (f h)) ^
        (Nat.card H).gcdB χ.degree =
      cu
  rw [hdet, ← hroot]

/-- Complex-valued form of determinant-root scalar recovery. -/
theorem determinantRootParameter_coe_eq_scalar
    (χ : IrreducibleCharacter G)
    (f : H →* G)
    (hcoprime : (Nat.card H).Coprime χ.degree)
    (h : H) (c : ℂ)
    (hc :
      χ.realization.ρ (f h) =
        c • (LinearMap.id :
          Module.End ℂ χ.realization)) :
    ((determinantRootParameter
        χ f hcoprime h : ℂˣ) : ℂ) =
      c := by
  rw [determinantRootParameter_eq_scalarUnit
    χ f hcoprime h c hc]
  rfl

end IrreducibleCharacter
end McKayConjecture
