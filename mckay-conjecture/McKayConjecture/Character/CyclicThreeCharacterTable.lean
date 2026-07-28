/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import McKayConjecture.Character.FiniteCharacterTableCertificate
import McKayConjecture.Character.LinearRestrictionMultiplicity
import McKayConjecture.Character.SimpleCharacterRowCertificate
import McKayConjecture.GroupTheory.FiniteDualOrthogonality
import McKayConjecture.GroupTheory.QuaternionGroupHom

/-!
# The complete character table of the cyclic group of order three

This file constructs the three complex linear representations explicitly
from a primitive third root of unity.  Duality for finite abelian groups
proves that the three homomorphisms exhaust the complex dual, and
commutativity then proves that they exhaust all irreducible characters.

The same rows are also packaged through `FiniteCharacterTableCertificate`.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CyclicThree

/-- The cyclic group of order three in multiplicative notation. -/
abbrev Group :=
  Multiplicative (ZMod 3)

/-- A fixed primitive complex third root of unity. -/
def primitiveThirdRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 3)

theorem primitiveThirdRoot_isPrimitive :
    IsPrimitiveRoot primitiveThirdRoot 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem primitiveThirdRoot_ne_zero :
    primitiveThirdRoot ≠ 0 :=
  primitiveThirdRoot_isPrimitive.ne_zero (by norm_num)

/-- The primitive third root, regarded as a complex unit. -/
def primitiveThirdRootUnit : ℂˣ :=
  Units.mk0 primitiveThirdRoot primitiveThirdRoot_ne_zero

@[simp]
theorem primitiveThirdRootUnit_pow_three :
    primitiveThirdRootUnit ^ 3 = 1 := by
  apply Units.ext
  exact primitiveThirdRoot_isPrimitive.pow_eq_one

/-- The three third roots `1, ζ, ζ²`. -/
def thirdRootParameter (j : Fin 3) : ℂˣ :=
  primitiveThirdRootUnit ^ j.val

theorem thirdRootParameter_injective :
    Function.Injective thirdRootParameter := by
  intro i j hij
  apply Fin.ext
  apply primitiveThirdRoot_isPrimitive.pow_inj i.isLt j.isLt
  simpa [thirdRootParameter, primitiveThirdRootUnit] using
    congrArg Units.val hij

theorem thirdRootParameter_pow_three (j : Fin 3) :
    thirdRootParameter j ^ 3 = 1 := by
  rw [thirdRootParameter, ← pow_mul]
  rw [show j.val * 3 = 3 * j.val by omega,
    pow_mul, primitiveThirdRootUnit_pow_three, one_pow]

/-- The homomorphism sending the canonical generator of `C₃` to the
`j`-th third root of unity. -/
def linearHom (j : Fin 3) : Group →* ℂˣ where
  toFun i :=
    QuaternionGroup.zmodPower
      (thirdRootParameter j)
      (thirdRootParameter_pow_three j)
      (Multiplicative.toAdd i)
  map_one' :=
    QuaternionGroup.zmodPower_zero
      (thirdRootParameter j)
      (thirdRootParameter_pow_three j)
  map_mul' i k :=
    QuaternionGroup.zmodPower_add
      (thirdRootParameter j)
      (thirdRootParameter_pow_three j)
      (Multiplicative.toAdd i)
      (Multiplicative.toAdd k)

@[simp]
theorem linearHom_generator (j : Fin 3) :
    linearHom j (Multiplicative.ofAdd 1) =
      thirdRootParameter j := by
  change
    QuaternionGroup.zmodPower
        (thirdRootParameter j)
        (thirdRootParameter_pow_three j)
        ((1 : ℕ) : ZMod 3) =
      thirdRootParameter j
  rw [QuaternionGroup.zmodPower_natCast]
  simp

theorem linearHom_injective :
    Function.Injective linearHom := by
  intro i j hij
  apply thirdRootParameter_injective
  rw [← linearHom_generator i, ← linearHom_generator j, hij]

private noncomputable instance cyclicThreeComplexDualFinite :
    Finite (Group →* ℂˣ) :=
  Finite.of_equiv Group
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
      Group ℂ).some.symm.toEquiv

theorem linearHom_bijective :
    Function.Bijective linearHom := by
  apply linearHom_injective.bijective_of_nat_card_le
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  simp [Group, ZMod.card, Nat.card_eq_fintype_card]

/-- Explicit enumeration of the full complex dual of `C₃`. -/
def linearHomEquiv :
    Fin 3 ≃ (Group →* ℂˣ) :=
  Equiv.ofBijective linearHom linearHom_bijective

@[simp]
theorem linearHomEquiv_apply (j : Fin 3) :
    linearHomEquiv j = linearHom j :=
  rfl

/-- The three explicit one-dimensional representations. -/
abbrev linearFDRep (j : Fin 3) : FDRep ℂ Group :=
  IrreducibleCharacter.linearFDRep (linearHom j)

theorem linearFDRep_simple (j : Fin 3) :
    Simple (linearFDRep j) :=
  IrreducibleCharacter.linearFDRep_simple (linearHom j)

@[simp]
theorem linearFDRep_character (j : Fin 3) :
    (linearFDRep j).character =
      fun g ↦ (linearHom j g : ℂ) :=
  IrreducibleCharacter.linearFDRep_character (linearHom j)

@[simp]
theorem linearFDRep_finrank (j : Fin 3) :
    Module.finrank ℂ (linearFDRep j) = 1 :=
  IrreducibleCharacter.linearFDRep_finrank (linearHom j)

/-- The irreducible character afforded by the `j`-th representation. -/
def linearCharacter (j : Fin 3) :
    IrreducibleCharacter Group :=
  IrreducibleCharacter.linear (linearHom j)

@[simp]
theorem linearCharacter_degree (j : Fin 3) :
    (linearCharacter j).degree = 1 :=
  IrreducibleCharacter.linear_degree (linearHom j)

theorem linearCharacter_injective :
    Function.Injective linearCharacter :=
  IrreducibleCharacter.linear_injective.comp linearHom_injective

/-- For a commutative group, every irreducible character is uniquely
determined by its degree-one linear parameter. -/
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

/-- Complete ordinary irreducible-character enumeration of `C₃`. -/
def irreducibleCharacterEquiv :
    Fin 3 ≃ IrreducibleCharacter Group :=
  linearHomEquiv.trans irreducibleCharacterLinearEquiv.symm

@[simp]
theorem irreducibleCharacterEquiv_apply (j : Fin 3) :
    irreducibleCharacterEquiv j = linearCharacter j := by
  change
    IrreducibleCharacter.linear (linearHomEquiv j) =
      IrreducibleCharacter.linear (linearHom j)
  rw [linearHomEquiv_apply]

local instance cyclicThreeFactPrimeFive :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The three rows, packaged as `5'`-degree irreducible characters. -/
def pPrimeCharacter (j : Fin 3) :
    PPrimeIrreducibleCharacter Group 5 :=
  ⟨linearCharacter j,
    IrreducibleCharacter.linear_isPPrimeDegree
      (linearHom j) 5⟩

/-- Complete `5'`-degree character enumeration of `C₃`. -/
def pPrimeCharacterEquiv :
    Fin 3 ≃ PPrimeIrreducibleCharacter Group 5 :=
  linearHomEquiv.trans
    (IrreducibleCharacter.commutativePPrimeLinearEquiv 5).symm

@[simp]
theorem pPrimeCharacterEquiv_apply (j : Fin 3) :
    pPrimeCharacterEquiv j = pPrimeCharacter j := by
  apply Subtype.ext
  change
    IrreducibleCharacter.linear (linearHomEquiv j) =
      IrreducibleCharacter.linear (linearHom j)
  rw [linearHomEquiv_apply]

@[simp]
theorem pPrimeCharacterEquiv_degree (j : Fin 3) :
    (pPrimeCharacterEquiv j).1.degree = 1 := by
  rw [pPrimeCharacterEquiv_apply]
  exact linearCharacter_degree j

/-- The normalized certificate attached to an explicit `C₃` row. -/
def rowCertificate (j : Fin 3) :
    CharacterRowCertificate Group := by
  letI : Simple (linearFDRep j) := linearFDRep_simple j
  exact CharacterRowCertificate.ofSimple (linearFDRep j)

theorem rowCertificate_irreducibleCharacter (j : Fin 3) :
    (rowCertificate j).irreducibleCharacter =
      linearCharacter j := by
  apply IrreducibleCharacter.ext
  funext g
  rw [(rowCertificate j).irreducibleCharacter_values_apply]
  change
    (linearFDRep j).character g =
      (linearCharacter j).values g
  rw [linearFDRep_character]
  change
    (linearHom j g : ℂ) =
      (IrreducibleCharacter.linear (linearHom j)).values g
  rw [IrreducibleCharacter.linear_values]

/-- Generic finite-table certificate for the three explicit rows. -/
def finiteCharacterTableCertificate :
    FiniteCharacterTableCertificate Group (Fin 3) where
  row := rowCertificate
  row_injective := by
    intro i j hij
    change
      (rowCertificate i).irreducibleCharacter =
        (rowCertificate j).irreducibleCharacter at hij
    apply linearCharacter_injective
    rw [← rowCertificate_irreducibleCharacter i,
      ← rowCertificate_irreducibleCharacter j]
    exact hij
  row_count := by
    calc
      Nat.card (Fin 3) =
          Nat.card (IrreducibleCharacter Group) :=
        Nat.card_congr irreducibleCharacterEquiv
      _ = Nat.card (ConjClasses Group) :=
        ClassFunction.natCard_irreducibleCharacter_eq_conjClasses

end CyclicThree
end McKayConjecture
