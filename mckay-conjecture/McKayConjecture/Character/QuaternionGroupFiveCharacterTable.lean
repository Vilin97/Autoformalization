/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Finiteness
import McKayConjecture.Character.IrreducibleCharacterBasis
import McKayConjecture.Character.QuaternionGroupFiveLinear
import McKayConjecture.Character.QuaternionGroupFiveTwoDimensional

/-!
# Complete character enumeration for the order-twenty dicyclic group

The four linear and four two-dimensional rows constructed in the preceding
files are pairwise distinct.  A conjugacy-class count then proves that they
exhaust all ordinary irreducible characters.  Since their degrees are one
or two, the same list is the complete `5'`-character table.
-/

noncomputable section

namespace McKayConjecture
namespace QuaternionGroupFive

local instance : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- Eight-row index for the complete table. -/
inductive CharacterRow
  | linear (j : Fin 4)
  | twoDimensional (k : Fin 4)
  deriving DecidableEq, Fintype

theorem twoDimensionalCharacter_injective :
    Function.Injective twoDimensionalCharacter := by
  intro k l h
  have hvalue :=
    congrArg
      (fun χ : IrreducibleCharacter (QuaternionGroup 5) =>
        χ.values
          (QuaternionGroup.a
            ((1 : ℕ) : ZMod 10))) h
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
        (primitiveTenthRoot_isPrimitive.pow_inj
          (by omega)
          (by omega)
          (sub_eq_zero.mp hsame))
  · have hmul : u * v = 1 := by
      have huv' : u = v⁻¹ :=
        sub_eq_zero.mp hinverse
      rw [huv']
      exact inv_mul_cancel₀ hv
    have hpow :
        primitiveTenthRoot ^
            ((k.val + 1) + (l.val + 1)) = 1 := by
      rw [pow_add]
      exact hmul
    have hdvd :
        10 ∣ (k.val + 1) + (l.val + 1) :=
      (primitiveTenthRoot_isPrimitive.pow_eq_one_iff_dvd _).mp hpow
    exact False.elim <|
      (Nat.not_dvd_of_pos_of_lt
        (by omega)
        (by omega)) hdvd

/-- A linear row, packaged with its `5'`-degree proof. -/
def linearPPrimeCharacter (j : Fin 4) :
    PPrimeIrreducibleCharacter (QuaternionGroup 5) 5 :=
  ⟨linearCharacter j,
    IrreducibleCharacter.linear_isPPrimeDegree
      (linearHom j) 5⟩

@[simp]
theorem linearPPrimeCharacter_degree (j : Fin 4) :
    (linearPPrimeCharacter j).1.degree = 1 :=
  linearCharacter_degree j

/-- A two-dimensional row, packaged with its `5'`-degree proof. -/
def twoDimensionalPPrimeCharacter (k : Fin 4) :
    PPrimeIrreducibleCharacter (QuaternionGroup 5) 5 :=
  ⟨twoDimensionalCharacter k, by
    rw [IrreducibleCharacter.IsPPrimeDegree,
      twoDimensionalCharacter_degree]
    norm_num⟩

@[simp]
theorem twoDimensionalPPrimeCharacter_degree (k : Fin 4) :
    (twoDimensionalPPrimeCharacter k).1.degree = 2 :=
  twoDimensionalCharacter_degree k

/-- Character attached to an eight-row table index. -/
def pPrimeCharacter :
    CharacterRow →
      PPrimeIrreducibleCharacter (QuaternionGroup 5) 5
  | .linear j => linearPPrimeCharacter j
  | .twoDimensional k => twoDimensionalPPrimeCharacter k

@[simp]
theorem pPrimeCharacter_degree_linear (j : Fin 4) :
    (pPrimeCharacter (.linear j)).1.degree = 1 :=
  linearPPrimeCharacter_degree j

@[simp]
theorem pPrimeCharacter_degree_twoDimensional (k : Fin 4) :
    (pPrimeCharacter (.twoDimensional k)).1.degree = 2 :=
  twoDimensionalPPrimeCharacter_degree k

theorem pPrimeCharacter_injective :
    Function.Injective pPrimeCharacter := by
  intro r s h
  rcases r with j | k <;> rcases s with l | m
  · congr 1
    apply linearCharacter_injective
    exact congrArg Subtype.val h
  · exfalso
    have hdegree :=
      congrArg
        (fun χ :
            PPrimeIrreducibleCharacter
              (QuaternionGroup 5) 5 =>
          χ.1.degree) h
    norm_num at hdegree
  · exfalso
    have hdegree :=
      congrArg
        (fun χ :
            PPrimeIrreducibleCharacter
              (QuaternionGroup 5) 5 =>
          χ.1.degree) h
    norm_num at hdegree
  · congr 1
    apply twoDimensionalCharacter_injective
    exact congrArg Subtype.val h

/-- The order-twenty dicyclic group has eight conjugacy classes and hence
eight ordinary irreducible characters. -/
theorem natCard_irreducibleCharacter :
    Nat.card (IrreducibleCharacter (QuaternionGroup 5)) = 8 := by
  rw [ClassFunction.natCard_irreducibleCharacter_eq_conjClasses]
  rw [Nat.card_eq_fintype_card]
  native_decide

theorem pPrimeCharacter_bijective :
    Function.Bijective pPrimeCharacter := by
  apply pPrimeCharacter_injective.bijective_of_nat_card_le
  have hrows : Nat.card CharacterRow = 8 := by
    rw [Nat.card_eq_fintype_card]
    native_decide
  have hpPrimeLe :
      Nat.card
          (PPrimeIrreducibleCharacter
            (QuaternionGroup 5) 5) ≤
        Nat.card
          (IrreducibleCharacter
            (QuaternionGroup 5)) :=
    Nat.card_le_card_of_injective
      (fun χ :
          PPrimeIrreducibleCharacter
            (QuaternionGroup 5) 5 => χ.1)
      Subtype.val_injective
  have hirreducible := natCard_irreducibleCharacter
  omega

/-- Complete concrete enumeration of the `5'`-degree irreducible
characters. -/
def pPrimeCharacterEquiv :
    CharacterRow ≃
      PPrimeIrreducibleCharacter (QuaternionGroup 5) 5 :=
  Equiv.ofBijective pPrimeCharacter
    pPrimeCharacter_bijective

@[simp]
theorem pPrimeCharacterEquiv_apply (r : CharacterRow) :
    pPrimeCharacterEquiv r = pPrimeCharacter r :=
  rfl

end QuaternionGroupFive
end McKayConjecture
