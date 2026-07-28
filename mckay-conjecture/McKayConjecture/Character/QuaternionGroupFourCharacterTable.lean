/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.QuaternionGroupFourLinear
import McKayConjecture.Character.QuaternionGroupFourTwoDimensional
import McKayConjecture.Character.TableEnumeration
import McKayConjecture.GroupTheory.QuaternionGroupFourConjugacyClasses

/-!
# Complete character table of the generalized quaternion group of order sixteen

The four linear rows and three two-dimensional matrix rows are pairwise
distinct.  The explicit seven-class calculation proves that they exhaust
all ordinary irreducible characters.  Filtering by odd degree leaves
exactly the four linear rows.
-/

noncomputable section

namespace McKayConjecture
namespace QuaternionGroupFour

/-- Seven-row index for the complete ordinary table. -/
abbrev CharacterRow :=
  LinearIndex ⊕ Fin 3

/-- The irreducible character attached to a table row. -/
def character :
    CharacterRow → IrreducibleCharacter (QuaternionGroup 4)
  | .inl r => linearCharacter r
  | .inr k => twoDimensionalCharacter k

@[simp]
theorem character_degree_linear (r : LinearIndex) :
    (character (.inl r)).degree = 1 :=
  linearCharacter_degree r

@[simp]
theorem character_degree_twoDimensional (k : Fin 3) :
    (character (.inr k)).degree = 2 :=
  twoDimensionalCharacter_degree k

@[simp]
theorem character_values_linear_a
    (r : LinearIndex) (m : ℕ) :
    (character (.inl r)).values
        (QuaternionGroup.a (m : ZMod 8)) =
      (signParameter r.1 ^ m : ℂˣ) :=
  linearCharacter_values_a_natCast r m

@[simp]
theorem character_values_linear_xa
    (r : LinearIndex) (m : ℕ) :
    (character (.inl r)).values
        (QuaternionGroup.xa (m : ZMod 8)) =
      (signParameter r.2 * signParameter r.1 ^ m : ℂˣ) :=
  linearCharacter_values_xa_natCast r m

@[simp]
theorem character_values_twoDimensional_a
    (k : Fin 3) (m : ℕ) :
    (character (.inr k)).values
        (QuaternionGroup.a (m : ZMod 8)) =
      twoDimensionalParameter k ^ m +
        (twoDimensionalParameter k)⁻¹ ^ m :=
  twoDimensionalCharacter_values_a_natCast k m

@[simp]
theorem character_values_twoDimensional_xa
    (k : Fin 3) (i : ZMod 8) :
    (character (.inr k)).values
        (QuaternionGroup.xa i) = 0 :=
  twoDimensionalCharacter_values_xa k i

theorem character_injective :
    Function.Injective character := by
  intro r s hrs
  rcases r with r | k <;> rcases s with s | l
  · congr 1
    exact linearCharacter_injective hrs
  · exfalso
    have hdegree :=
      congrArg
        (fun χ : IrreducibleCharacter (QuaternionGroup 4) =>
          χ.degree) hrs
    norm_num at hdegree
  · exfalso
    have hdegree :=
      congrArg
        (fun χ : IrreducibleCharacter (QuaternionGroup 4) =>
          χ.degree) hrs
    norm_num at hdegree
  · congr 1
    exact twoDimensionalCharacter_injective hrs

private theorem natCard_characterRow :
    Nat.card CharacterRow = 7 := by
  calc
    Nat.card CharacterRow =
        Nat.card LinearIndex + Nat.card (Fin 3) :=
      Nat.card_sum
    _ = 7 := by
      simp [LinearIndex]

/-- Complete ordinary irreducible-character enumeration. -/
def irreducibleCharacterEquiv :
    CharacterRow ≃ IrreducibleCharacter (QuaternionGroup 4) :=
  irreducibleCharacterEquivOfInjective
    character character_injective (by
      rw [natCard_characterRow, natCard_conjClasses])

@[simp]
theorem irreducibleCharacterEquiv_apply
    (r : CharacterRow) :
    irreducibleCharacterEquiv r = character r :=
  rfl

/-- There are exactly seven ordinary irreducible characters. -/
@[simp]
theorem natCard_irreducibleCharacter :
    Nat.card (IrreducibleCharacter (QuaternionGroup 4)) = 7 := by
  calc
    Nat.card (IrreducibleCharacter (QuaternionGroup 4)) =
        Nat.card CharacterRow :=
      Nat.card_congr irreducibleCharacterEquiv.symm
    _ = 7 := natCard_characterRow

local instance quaternionGroupFourCharacterTableFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- A linear row packaged with its odd-degree proof. -/
def linearPPrimeCharacter (r : LinearIndex) :
    PPrimeIrreducibleCharacter (QuaternionGroup 4) 2 :=
  ⟨linearCharacter r,
    IrreducibleCharacter.linear_isPPrimeDegree
      (linearHom r) 2⟩

@[simp]
theorem linearPPrimeCharacter_degree (r : LinearIndex) :
    (linearPPrimeCharacter r).1.degree = 1 :=
  linearCharacter_degree r

@[simp]
theorem linearPPrimeCharacter_values_a
    (r : LinearIndex) (m : ℕ) :
    (linearPPrimeCharacter r).1.values
        (QuaternionGroup.a (m : ZMod 8)) =
      (signParameter r.1 ^ m : ℂˣ) :=
  linearCharacter_values_a_natCast r m

@[simp]
theorem linearPPrimeCharacter_values_xa
    (r : LinearIndex) (m : ℕ) :
    (linearPPrimeCharacter r).1.values
        (QuaternionGroup.xa (m : ZMod 8)) =
      (signParameter r.2 * signParameter r.1 ^ m : ℂˣ) :=
  linearCharacter_values_xa_natCast r m

theorem linearPPrimeCharacter_bijective :
    Function.Bijective linearPPrimeCharacter := by
  constructor
  · intro r s hrs
    apply linearCharacter_injective
    exact congrArg Subtype.val hrs
  · intro χ
    let r : CharacterRow :=
      irreducibleCharacterEquiv.symm χ.1
    have hr :
        irreducibleCharacterEquiv r = χ.1 :=
      irreducibleCharacterEquiv.apply_symm_apply χ.1
    rcases r with r | k
    · refine ⟨r, ?_⟩
      apply Subtype.ext
      change linearCharacter r = χ.1
      simpa [character] using hr
    · have hp := χ.2
      rw [← hr, irreducibleCharacterEquiv_apply] at hp
      change ¬2 ∣ (twoDimensionalCharacter k).degree at hp
      rw [twoDimensionalCharacter_degree] at hp
      exact False.elim (hp (dvd_refl 2))

/-- Complete enumeration of the four odd-degree irreducible characters. -/
def pPrimeCharacterEquiv :
    LinearIndex ≃
      PPrimeIrreducibleCharacter (QuaternionGroup 4) 2 :=
  Equiv.ofBijective linearPPrimeCharacter
    linearPPrimeCharacter_bijective

@[simp]
theorem pPrimeCharacterEquiv_apply (r : LinearIndex) :
    pPrimeCharacterEquiv r = linearPPrimeCharacter r :=
  rfl

/-- There are exactly four odd-degree irreducible characters. -/
@[simp]
theorem natCard_pPrimeIrreducibleCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          (QuaternionGroup 4) 2) =
      4 := by
  calc
    Nat.card
        (PPrimeIrreducibleCharacter
          (QuaternionGroup 4) 2) =
        Nat.card LinearIndex :=
      Nat.card_congr pPrimeCharacterEquiv.symm
    _ = 4 := by simp [LinearIndex]

end QuaternionGroupFour
end McKayConjecture
