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
# Two-dimensional characters of the generalized quaternion group of order sixteen

Specializing the generic dicyclic matrix construction to a primitive eighth
root of unity produces the three two-dimensional irreducible characters of
`QuaternionGroup 4`.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace QuaternionGroupFour

open QuaternionGroupRepresentation

/-- A fixed primitive eighth root of unity. -/
def primitiveEighthRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 8)

theorem primitiveEighthRoot_isPrimitive :
    IsPrimitiveRoot primitiveEighthRoot 8 := by
  exact Complex.isPrimitiveRoot_exp 8 (by norm_num)

theorem primitiveEighthRoot_ne_zero :
    primitiveEighthRoot ≠ 0 :=
  primitiveEighthRoot_isPrimitive.ne_zero (by norm_num)

/-- Parameters `ζ`, `ζ²`, and `ζ³` for the three matrix rows. -/
def twoDimensionalParameter (k : Fin 3) : ℂ :=
  primitiveEighthRoot ^ (k.val + 1)

theorem twoDimensionalParameter_ne_zero (k : Fin 3) :
    twoDimensionalParameter k ≠ 0 :=
  pow_ne_zero _ primitiveEighthRoot_ne_zero

theorem twoDimensionalParameter_pow_eight (k : Fin 3) :
    twoDimensionalParameter k ^ 8 = 1 := by
  rw [twoDimensionalParameter, ← pow_mul]
  rw [show (k.val + 1) * 8 =
      8 * (k.val + 1) by omega]
  rw [pow_mul, primitiveEighthRoot_isPrimitive.pow_eq_one,
    one_pow]

theorem twoDimensionalParameter_ne_inv (k : Fin 3) :
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
      primitiveEighthRoot ^ (2 * (k.val + 1)) = 1 := by
    rw [two_mul, pow_add]
    exact hmul
  have hdvd : 8 ∣ 2 * (k.val + 1) :=
    (primitiveEighthRoot_isPrimitive.pow_eq_one_iff_dvd _).mp hp
  exact
    (Nat.not_dvd_of_pos_of_lt
      (by omega)
      (by omega)) hdvd

/-- The three standard two-dimensional representations. -/
def twoDimensionalRepresentation (k : Fin 3) :
    Representation ℂ (QuaternionGroup 4) (Fin 2 → ℂ) :=
  standardRepresentation
    (twoDimensionalParameter k)
    (twoDimensionalParameter_ne_zero k)
    (by simpa using twoDimensionalParameter_pow_eight k)

theorem twoDimensionalRepresentation_isIrreducible
    (k : Fin 3) :
    Representation.IsIrreducible
      (twoDimensionalRepresentation k) :=
  standardRepresentation_isIrreducible
    (twoDimensionalParameter k)
    (twoDimensionalParameter_ne_zero k)
    (by simpa using twoDimensionalParameter_pow_eight k)
    (twoDimensionalParameter_ne_inv k)

/-- The finite-dimensional object underlying a matrix row. -/
abbrev twoDimensionalFDRep (k : Fin 3) :
    FDRep ℂ (QuaternionGroup 4) :=
  FDRep.of (twoDimensionalRepresentation k)

theorem twoDimensionalFDRep_simple (k : Fin 3) :
    Simple (twoDimensionalFDRep k) := by
  letI :
      Representation.IsIrreducible
        (twoDimensionalRepresentation k) :=
    twoDimensionalRepresentation_isIrreducible k
  exact
    FDRep.simple_of_representation_isIrreducible
      (twoDimensionalRepresentation k)

/-- The three two-dimensional irreducible characters. -/
def twoDimensionalCharacter (k : Fin 3) :
    IrreducibleCharacter (QuaternionGroup 4) := by
  letI : Simple (twoDimensionalFDRep k) :=
    twoDimensionalFDRep_simple k
  exact IrreducibleCharacter.ofSimple (twoDimensionalFDRep k)

@[simp]
theorem twoDimensionalCharacter_degree (k : Fin 3) :
    (twoDimensionalCharacter k).degree = 2 := by
  change Module.finrank ℂ (twoDimensionalFDRep k) = 2
  simp [twoDimensionalFDRep]

@[simp]
theorem twoDimensionalCharacter_values_a_natCast
    (k : Fin 3) (m : ℕ) :
    (twoDimensionalCharacter k).values
        (QuaternionGroup.a (m : ZMod 8)) =
      twoDimensionalParameter k ^ m +
        (twoDimensionalParameter k)⁻¹ ^ m := by
  change
    (twoDimensionalRepresentation k).character
        (QuaternionGroup.a (m : ZMod 8)) = _
  exact
    standardCharacter_apply_a_natCast
      (n := 4)
      (twoDimensionalParameter k)
      (twoDimensionalParameter_ne_zero k)
      (by simpa using twoDimensionalParameter_pow_eight k)
      m

@[simp]
theorem twoDimensionalCharacter_values_xa
    (k : Fin 3) (i : ZMod 8) :
    (twoDimensionalCharacter k).values
        (QuaternionGroup.xa i) = 0 := by
  change
    (twoDimensionalRepresentation k).character
        (QuaternionGroup.xa i) = 0
  exact
    standardCharacter_apply_xa
      (n := 4)
      (twoDimensionalParameter k)
      (twoDimensionalParameter_ne_zero k)
      (by simpa using twoDimensionalParameter_pow_eight k)
      (by norm_num)
      i

theorem twoDimensionalCharacter_injective :
    Function.Injective twoDimensionalCharacter := by
  intro k l h
  have hvalue :=
    congrArg
      (fun χ : IrreducibleCharacter (QuaternionGroup 4) =>
        χ.values
          (QuaternionGroup.a
            ((1 : ℕ) : ZMod 8))) h
  rw [twoDimensionalCharacter_values_a_natCast,
    twoDimensionalCharacter_values_a_natCast] at hvalue
  have hvalue' :
      twoDimensionalParameter k +
          (twoDimensionalParameter k)⁻¹ =
        twoDimensionalParameter l +
          (twoDimensionalParameter l)⁻¹ := by
    simpa only [pow_one] using hvalue
  let u : ℂ := twoDimensionalParameter k
  let v : ℂ := twoDimensionalParameter l
  have hu : u ≠ 0 :=
    twoDimensionalParameter_ne_zero k
  have hv : v ≠ 0 :=
    twoDimensionalParameter_ne_zero l
  have huv :
      (u - v) * (u - v⁻¹) = 0 := by
    calc
      (u - v) * (u - v⁻¹) =
          u * (u + u⁻¹ - (v + v⁻¹)) := by
            field_simp [hu, hv]
            ring
      _ = 0 := by
        change
          u *
            (twoDimensionalParameter k +
                (twoDimensionalParameter k)⁻¹ -
              (twoDimensionalParameter l +
                (twoDimensionalParameter l)⁻¹)) = 0
        rw [hvalue']
        ring
  rcases mul_eq_zero.mp huv with hsame | hinverse
  · apply Fin.ext
    exact
      Nat.add_right_cancel
        (primitiveEighthRoot_isPrimitive.pow_inj
          (by omega)
          (by omega)
          (sub_eq_zero.mp hsame))
  · have hmul : u * v = 1 := by
      have huv' : u = v⁻¹ :=
        sub_eq_zero.mp hinverse
      rw [huv']
      exact inv_mul_cancel₀ hv
    have hpow :
        primitiveEighthRoot ^
            ((k.val + 1) + (l.val + 1)) = 1 := by
      rw [pow_add]
      exact hmul
    have hdvd :
        8 ∣ (k.val + 1) + (l.val + 1) :=
      (primitiveEighthRoot_isPrimitive.pow_eq_one_iff_dvd _).mp hpow
    exact False.elim <|
      (Nat.not_dvd_of_pos_of_lt
        (by omega)
        (by omega)) hdvd

end QuaternionGroupFour
end McKayConjecture
