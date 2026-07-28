/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import McKayConjecture.Character.LinearRestrictionMultiplicity
import McKayConjecture.Character.SimpleCharacterRowCertificate
import McKayConjecture.GroupTheory.FiniteDualOrthogonality
import McKayConjecture.GroupTheory.QuaternionGroupHom

/-!
# The complete character table of the cyclic group of order eight

This file constructs the eight complex linear characters of `C₈`
explicitly from a primitive eighth root of unity.  Finite abelian
duality proves that they exhaust the complex dual, and commutativity
then proves that they exhaust all ordinary irreducible characters.

Every row has degree one, hence is of `3'` degree.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CyclicEight

/-- The cyclic group of order eight in multiplicative notation. -/
abbrev Group :=
  Multiplicative (ZMod 8)

/-- A fixed primitive complex eighth root of unity. -/
def primitiveEighthRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 8)

theorem primitiveEighthRoot_isPrimitive :
    IsPrimitiveRoot primitiveEighthRoot 8 :=
  Complex.isPrimitiveRoot_exp 8 (by norm_num)

theorem primitiveEighthRoot_ne_zero :
    primitiveEighthRoot ≠ 0 :=
  primitiveEighthRoot_isPrimitive.ne_zero (by norm_num)

/-- The primitive eighth root as a complex unit. -/
def primitiveEighthRootUnit : ℂˣ :=
  Units.mk0 primitiveEighthRoot primitiveEighthRoot_ne_zero

@[simp]
theorem primitiveEighthRootUnit_pow_eight :
    primitiveEighthRootUnit ^ 8 = 1 := by
  apply Units.ext
  exact primitiveEighthRoot_isPrimitive.pow_eq_one

/-- The eight parameters `1, ζ, ..., ζ⁷`. -/
def eighthRootParameter (j : Fin 8) : ℂˣ :=
  primitiveEighthRootUnit ^ j.val

theorem eighthRootParameter_injective :
    Function.Injective eighthRootParameter := by
  intro i j hij
  apply Fin.ext
  apply primitiveEighthRoot_isPrimitive.pow_inj i.isLt j.isLt
  simpa [eighthRootParameter, primitiveEighthRootUnit] using
    congrArg Units.val hij

theorem eighthRootParameter_pow_eight (j : Fin 8) :
    eighthRootParameter j ^ 8 = 1 := by
  rw [eighthRootParameter, ← pow_mul]
  rw [show j.val * 8 = 8 * j.val by omega,
    pow_mul, primitiveEighthRootUnit_pow_eight, one_pow]

/-- The homomorphism sending the canonical generator of `C₈` to the
`j`-th eighth root. -/
def linearHom (j : Fin 8) : Group →* ℂˣ where
  toFun i :=
    QuaternionGroup.zmodPower
      (eighthRootParameter j)
      (eighthRootParameter_pow_eight j)
      (Multiplicative.toAdd i)
  map_one' :=
    QuaternionGroup.zmodPower_zero
      (eighthRootParameter j)
      (eighthRootParameter_pow_eight j)
  map_mul' i k :=
    QuaternionGroup.zmodPower_add
      (eighthRootParameter j)
      (eighthRootParameter_pow_eight j)
      (Multiplicative.toAdd i)
      (Multiplicative.toAdd k)

@[simp]
theorem linearHom_generator (j : Fin 8) :
    linearHom j (Multiplicative.ofAdd 1) =
      eighthRootParameter j := by
  change
    QuaternionGroup.zmodPower
        (eighthRootParameter j)
        (eighthRootParameter_pow_eight j)
        ((1 : ℕ) : ZMod 8) =
      eighthRootParameter j
  rw [QuaternionGroup.zmodPower_natCast]
  simp

theorem linearHom_injective :
    Function.Injective linearHom := by
  intro i j hij
  apply eighthRootParameter_injective
  rw [← linearHom_generator i, ← linearHom_generator j, hij]

private noncomputable instance cyclicEightComplexDualFinite :
    Finite (Group →* ℂˣ) :=
  Finite.of_equiv Group
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
      Group ℂ).some.symm.toEquiv

theorem linearHom_bijective :
    Function.Bijective linearHom := by
  apply linearHom_injective.bijective_of_nat_card_le
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  simp [Group, ZMod.card, Nat.card_eq_fintype_card]

/-- Explicit enumeration of the full complex dual of `C₈`. -/
def linearHomEquiv :
    Fin 8 ≃ (Group →* ℂˣ) :=
  Equiv.ofBijective linearHom linearHom_bijective

@[simp]
theorem linearHomEquiv_apply (j : Fin 8) :
    linearHomEquiv j = linearHom j :=
  rfl

/-- The eight one-dimensional representations. -/
abbrev linearFDRep (j : Fin 8) : FDRep ℂ Group :=
  IrreducibleCharacter.linearFDRep (linearHom j)

theorem linearFDRep_simple (j : Fin 8) :
    Simple (linearFDRep j) :=
  IrreducibleCharacter.linearFDRep_simple (linearHom j)

@[simp]
theorem linearFDRep_character (j : Fin 8) :
    (linearFDRep j).character =
      fun g ↦ (linearHom j g : ℂ) :=
  IrreducibleCharacter.linearFDRep_character (linearHom j)

@[simp]
theorem linearFDRep_finrank (j : Fin 8) :
    Module.finrank ℂ (linearFDRep j) = 1 :=
  IrreducibleCharacter.linearFDRep_finrank (linearHom j)

/-- The irreducible character afforded by the `j`-th row. -/
def linearCharacter (j : Fin 8) :
    IrreducibleCharacter Group :=
  IrreducibleCharacter.linear (linearHom j)

@[simp]
theorem linearCharacter_degree (j : Fin 8) :
    (linearCharacter j).degree = 1 :=
  IrreducibleCharacter.linear_degree (linearHom j)

theorem linearCharacter_injective :
    Function.Injective linearCharacter :=
  IrreducibleCharacter.linear_injective.comp linearHom_injective

/-- For a commutative group, every irreducible character is linear. -/
def irreducibleCharacterLinearEquiv :
    IrreducibleCharacter Group ≃ (Group →* ℂˣ) where
  toFun χ :=
    IrreducibleCharacter.linearParameterOfDegreeOne χ
      (IrreducibleCharacter.degree_eq_one_of_isMulCommutative χ)
  invFun := IrreducibleCharacter.linear
  left_inv χ :=
    IrreducibleCharacter.linear_linearParameterOfDegreeOne χ
      (IrreducibleCharacter.degree_eq_one_of_isMulCommutative χ)
  right_inv lam := by
    apply IrreducibleCharacter.linear_injective
    exact
      IrreducibleCharacter.linear_linearParameterOfDegreeOne
        (IrreducibleCharacter.linear lam)
        (IrreducibleCharacter.linear_degree lam)

/-- Complete ordinary irreducible-character enumeration of `C₈`. -/
def irreducibleCharacterEquiv :
    Fin 8 ≃ IrreducibleCharacter Group :=
  linearHomEquiv.trans irreducibleCharacterLinearEquiv.symm

@[simp]
theorem irreducibleCharacterEquiv_apply (j : Fin 8) :
    irreducibleCharacterEquiv j = linearCharacter j := by
  change
    IrreducibleCharacter.linear (linearHomEquiv j) =
      IrreducibleCharacter.linear (linearHom j)
  rw [linearHomEquiv_apply]

local instance cyclicEightFactPrimeThree :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The eight rows, packaged as `3'`-degree characters. -/
def pPrimeCharacter (j : Fin 8) :
    PPrimeIrreducibleCharacter Group 3 :=
  ⟨linearCharacter j,
    IrreducibleCharacter.linear_isPPrimeDegree
      (linearHom j) 3⟩

/-- Complete `3'`-degree character enumeration of `C₈`. -/
def pPrimeCharacterEquiv :
    Fin 8 ≃ PPrimeIrreducibleCharacter Group 3 :=
  linearHomEquiv.trans
    (IrreducibleCharacter.commutativePPrimeLinearEquiv 3).symm

@[simp]
theorem pPrimeCharacterEquiv_apply (j : Fin 8) :
    pPrimeCharacterEquiv j = pPrimeCharacter j := by
  apply Subtype.ext
  change
    IrreducibleCharacter.linear (linearHomEquiv j) =
      IrreducibleCharacter.linear (linearHom j)
  rw [linearHomEquiv_apply]

@[simp]
theorem pPrimeCharacterEquiv_degree (j : Fin 8) :
    (pPrimeCharacterEquiv j).1.degree = 1 := by
  rw [pPrimeCharacterEquiv_apply]
  exact linearCharacter_degree j

@[simp]
theorem natCard_irreducibleCharacter :
    Nat.card (IrreducibleCharacter Group) = 8 := by
  calc
    Nat.card (IrreducibleCharacter Group) =
        Nat.card (Fin 8) :=
      Nat.card_congr irreducibleCharacterEquiv.symm
    _ = 8 := by simp

@[simp]
theorem natCard_pPrimeIrreducibleCharacter :
    Nat.card (PPrimeIrreducibleCharacter Group 3) = 8 := by
  calc
    Nat.card (PPrimeIrreducibleCharacter Group 3) =
        Nat.card (Fin 8) :=
      Nat.card_congr pPrimeCharacterEquiv.symm
    _ = 8 := by simp

end CyclicEight
end McKayConjecture
