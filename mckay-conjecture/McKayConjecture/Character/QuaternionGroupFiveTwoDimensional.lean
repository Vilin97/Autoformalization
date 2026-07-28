/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import McKayConjecture.Character.Burnside
import McKayConjecture.Character.Construction
import McKayConjecture.Character.QuaternionGroupTwoDimensional

/-!
# The four two-dimensional characters of the order-twenty dicyclic group

The exact normalizer of the fixed `5`-Sylow subgroup of
`SL(2, 𝔽₅)` is isomorphic to `QuaternionGroup 5`.  This file specializes
the generic matrix construction to a primitive tenth root of unity and
constructs its four two-dimensional irreducible representations.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace QuaternionGroupFive

open QuaternionGroupRepresentation

/-- A fixed primitive tenth root of unity. -/
def primitiveTenthRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 10)

/-- The chosen tenth root is primitive. -/
theorem primitiveTenthRoot_isPrimitive :
    IsPrimitiveRoot primitiveTenthRoot 10 := by
  exact Complex.isPrimitiveRoot_exp 10 (by norm_num)

theorem primitiveTenthRoot_ne_zero :
    primitiveTenthRoot ≠ 0 :=
  primitiveTenthRoot_isPrimitive.ne_zero (by norm_num)

/-- The parameter for the `k`-th two-dimensional representation, for
`k = 1,2,3,4`. -/
def twoDimensionalParameter (k : Fin 4) : ℂ :=
  primitiveTenthRoot ^ (k.val + 1)

theorem twoDimensionalParameter_ne_zero (k : Fin 4) :
    twoDimensionalParameter k ≠ 0 :=
  pow_ne_zero _ primitiveTenthRoot_ne_zero

theorem twoDimensionalParameter_pow_ten (k : Fin 4) :
    twoDimensionalParameter k ^ 10 = 1 := by
  rw [twoDimensionalParameter, ← pow_mul]
  rw [show (k.val + 1) * 10 =
      10 * (k.val + 1) by omega]
  rw [pow_mul, primitiveTenthRoot_isPrimitive.pow_eq_one,
    one_pow]

theorem twoDimensionalParameter_ne_inv (k : Fin 4) :
    twoDimensionalParameter k ≠
      (twoDimensionalParameter k)⁻¹ := by
  intro h
  have hmul :
      twoDimensionalParameter k *
          twoDimensionalParameter k = 1 :=
    calc
      twoDimensionalParameter k *
            twoDimensionalParameter k =
          (twoDimensionalParameter k)⁻¹ *
            twoDimensionalParameter k :=
        congrArg
          (fun z : ℂ => z * twoDimensionalParameter k) h
      _ = 1 :=
        inv_mul_cancel₀ (twoDimensionalParameter_ne_zero k)
  have hp :
      primitiveTenthRoot ^ (2 * (k.val + 1)) = 1 := by
    rw [two_mul, pow_add]
    exact hmul
  have hdvd : 10 ∣ 2 * (k.val + 1) :=
    (primitiveTenthRoot_isPrimitive.pow_eq_one_iff_dvd _).mp hp
  exact
    (Nat.not_dvd_of_pos_of_lt
      (by omega)
      (by omega)) hdvd

/-- The four standard two-dimensional representations of
`QuaternionGroup 5`. -/
def twoDimensionalRepresentation (k : Fin 4) :
    Representation ℂ (QuaternionGroup 5) (Fin 2 → ℂ) :=
  standardRepresentation
    (twoDimensionalParameter k)
    (twoDimensionalParameter_ne_zero k)
    (by simpa using twoDimensionalParameter_pow_ten k)

theorem twoDimensionalRepresentation_isIrreducible
    (k : Fin 4) :
    Representation.IsIrreducible
      (twoDimensionalRepresentation k) := by
  exact
    standardRepresentation_isIrreducible
      (twoDimensionalParameter k)
      (twoDimensionalParameter_ne_zero k)
      (by simpa using twoDimensionalParameter_pow_ten k)
      (twoDimensionalParameter_ne_inv k)

/-- The finite-dimensional object underlying the `k`-th matrix row. -/
abbrev twoDimensionalFDRep (k : Fin 4) :
    FDRep ℂ (QuaternionGroup 5) :=
  FDRep.of (twoDimensionalRepresentation k)

theorem twoDimensionalFDRep_simple (k : Fin 4) :
    Simple (twoDimensionalFDRep k) := by
  letI :
      Representation.IsIrreducible
        (twoDimensionalRepresentation k) :=
    twoDimensionalRepresentation_isIrreducible k
  exact
    FDRep.simple_of_representation_isIrreducible
      (twoDimensionalRepresentation k)

/-- The four two-dimensional irreducible characters. -/
def twoDimensionalCharacter (k : Fin 4) :
    IrreducibleCharacter (QuaternionGroup 5) := by
  letI : Simple (twoDimensionalFDRep k) :=
    twoDimensionalFDRep_simple k
  exact
    IrreducibleCharacter.ofSimple
      (twoDimensionalFDRep k)

@[simp]
theorem twoDimensionalCharacter_degree (k : Fin 4) :
    (twoDimensionalCharacter k).degree = 2 := by
  change Module.finrank ℂ (twoDimensionalFDRep k) = 2
  simp [twoDimensionalFDRep]

@[simp]
theorem twoDimensionalCharacter_values_a_natCast
    (k : Fin 4) (m : ℕ) :
    (twoDimensionalCharacter k).values
        (QuaternionGroup.a (m : ZMod 10)) =
      twoDimensionalParameter k ^ m +
        (twoDimensionalParameter k)⁻¹ ^ m := by
  change
    (twoDimensionalRepresentation k).character
        (QuaternionGroup.a (m : ZMod 10)) = _
  exact
    standardCharacter_apply_a_natCast
      (n := 5)
      (twoDimensionalParameter k)
      (twoDimensionalParameter_ne_zero k)
      (by simpa using twoDimensionalParameter_pow_ten k)
      m

@[simp]
theorem twoDimensionalCharacter_values_xa
    (k : Fin 4) (i : ZMod 10) :
    (twoDimensionalCharacter k).values
        (QuaternionGroup.xa i) = 0 := by
  change
    (twoDimensionalRepresentation k).character
        (QuaternionGroup.xa i) = 0
  exact
    standardCharacter_apply_xa
      (n := 5)
      (twoDimensionalParameter k)
      (twoDimensionalParameter_ne_zero k)
      (by simpa using twoDimensionalParameter_pow_ten k)
      (by norm_num)
      i

end QuaternionGroupFive
end McKayConjecture
