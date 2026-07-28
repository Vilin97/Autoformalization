/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveFiveAutomorphismClassification
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveFiveRowEquiv
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoOuterActions

/-!
# The outer action on the two `5'`-character tables of `SL(2, 𝔽₅)`

The diagonal outer automorphism sends the cyclic dicyclic generator `a`
to `a ^ 7` and fixes the reflection generator.  Its inverse therefore
sends `a` to `a ^ 3`.  The four linear normalizer rows are fixed, while
the two-dimensional rows are exchanged in opposite pairs.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open QuaternionGroupFive

local instance factPrimeFiveForOuterActions :
    Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The inverse of the restricted outer automorphism multiplies the
cyclic exponent by three. -/
@[simp]
theorem specialLinearTwoFiveSylowFiveOuterRestriction_symm_a
    (i : ZMod 10) :
    (SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowFive
        specialLinearTwoFiveSylowFiveOuterAutomorphism).symm
        (quaternionFiveEquivSylowFiveNormalizer
          (QuaternionGroup.a i)) =
      quaternionFiveEquivSylowFiveNormalizer
        (QuaternionGroup.a (3 * i)) := by
  apply
    (SylowAutStabilizer.normalizerRestrictionHom
      specialLinearTwoFiveSylowFive
      specialLinearTwoFiveSylowFiveOuterAutomorphism).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [SylowAutStabilizer.normalizerRestrictionHom_apply_coe]
  change
    specialLinearTwoFiveSylowFiveNormalizerA ^ i.val =
      specialLinearTwoFiveDiagonalOuterAutomorphism
        (specialLinearTwoFiveSylowFiveNormalizerA ^ (3 * i).val)
  rw [map_pow,
    specialLinearTwoFiveSylowFiveOuterAutomorphism_normalizerA]
  fin_cases i <;> decide

/-- The inverse restricted outer automorphism fixes the reflection
generator and multiplies its cyclic exponent by three. -/
@[simp]
theorem specialLinearTwoFiveSylowFiveOuterRestriction_symm_xa
    (i : ZMod 10) :
    (SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowFive
        specialLinearTwoFiveSylowFiveOuterAutomorphism).symm
        (quaternionFiveEquivSylowFiveNormalizer
          (QuaternionGroup.xa i)) =
      quaternionFiveEquivSylowFiveNormalizer
        (QuaternionGroup.xa (3 * i)) := by
  apply
    (SylowAutStabilizer.normalizerRestrictionHom
      specialLinearTwoFiveSylowFive
      specialLinearTwoFiveSylowFiveOuterAutomorphism).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [SylowAutStabilizer.normalizerRestrictionHom_apply_coe]
  change
    specialLinearTwoFiveSylowFiveNormalizerX *
        specialLinearTwoFiveSylowFiveNormalizerA ^ i.val =
      specialLinearTwoFiveDiagonalOuterAutomorphism
        (specialLinearTwoFiveSylowFiveNormalizerX *
          specialLinearTwoFiveSylowFiveNormalizerA ^ (3 * i).val)
  rw [map_mul, map_pow,
    specialLinearTwoFiveSylowFiveOuterAutomorphism_normalizerX,
    specialLinearTwoFiveSylowFiveOuterAutomorphism_normalizerA]
  fin_cases i <;> decide

/-- If an element has order dividing ten and square one, multiplication
of a `ZMod 10` exponent by three does not change its power. -/
theorem zmodPower_three_mul_of_sq_eq_one
    {H : Type*} [Group H]
    (A : H) (hA : A ^ 10 = 1) (hA2 : A ^ 2 = 1)
    (i : ZMod 10) :
    QuaternionGroup.zmodPower A hA (3 * i) =
      QuaternionGroup.zmodPower A hA i := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective i
  rw [show
    (3 : ZMod 10) * (z : ZMod 10) =
      ((3 * z : ℤ) : ZMod 10) by norm_num]
  simp only [QuaternionGroup.zmodPower_intCast]
  have hA3 : A ^ 3 = A := by
    calc
      A ^ 3 = A ^ 2 * A := by group
      _ = A := by rw [hA2, one_mul]
  calc
    A ^ (3 * z) = (A ^ (3 : ℤ)) ^ z := by
      rw [zpow_mul]
    _ = (A ^ (3 : ℕ)) ^ z := by norm_num
    _ = A ^ z := by rw [hA3]

/-- The four linear character values are unchanged when a cyclic
exponent is multiplied by three. -/
theorem quaternionGroupFiveLinearCharacter_values_a_three_mul
    (j : Fin 4) (i : ZMod 10) :
    (linearCharacter j).values (QuaternionGroup.a (3 * i)) =
      (linearCharacter j).values (QuaternionGroup.a i) := by
  simp only [linearCharacter, IrreducibleCharacter.linear_values]
  change
    ((QuaternionGroup.zmodPower
      (fourthRootParameter j ^ 2)
      (by
        exact
          show (fourthRootParameter j ^ 2) ^ (2 * 5) = 1 from by
            rw [← pow_mul]
            rw [show 2 * (2 * 5) = 4 * 5 by norm_num,
              pow_mul, fourthRootParameter_pow_four, one_pow])
      (3 * i) : ℂˣ) : ℂ) =
    ((QuaternionGroup.zmodPower
      (fourthRootParameter j ^ 2)
      (by
        exact
          show (fourthRootParameter j ^ 2) ^ (2 * 5) = 1 from by
            rw [← pow_mul]
            rw [show 2 * (2 * 5) = 4 * 5 by norm_num,
              pow_mul, fourthRootParameter_pow_four, one_pow])
      i : ℂˣ) : ℂ)
  rw [zmodPower_three_mul_of_sq_eq_one]
  rw [← pow_mul]
  simpa using fourthRootParameter_pow_four j

/-- The same invariance holds on the noncyclic dicyclic coset. -/
theorem quaternionGroupFiveLinearCharacter_values_xa_three_mul
    (j : Fin 4) (i : ZMod 10) :
    (linearCharacter j).values (QuaternionGroup.xa (3 * i)) =
      (linearCharacter j).values (QuaternionGroup.xa i) := by
  simp only [linearCharacter, IrreducibleCharacter.linear_values]
  change
    (((fourthRootParameter j) *
      QuaternionGroup.zmodPower
        (fourthRootParameter j ^ 2)
        (by
          exact
            show (fourthRootParameter j ^ 2) ^ (2 * 5) = 1 from by
              rw [← pow_mul]
              rw [show 2 * (2 * 5) = 4 * 5 by norm_num,
                pow_mul, fourthRootParameter_pow_four, one_pow])
        (3 * i) : ℂˣ) : ℂ) =
    (((fourthRootParameter j) *
      QuaternionGroup.zmodPower
        (fourthRootParameter j ^ 2)
        (by
          exact
            show (fourthRootParameter j ^ 2) ^ (2 * 5) = 1 from by
              rw [← pow_mul]
              rw [show 2 * (2 * 5) = 4 * 5 by norm_num,
                pow_mul, fourthRootParameter_pow_four, one_pow])
        i : ℂˣ) : ℂ)
  congr 2
  rw [zmodPower_three_mul_of_sq_eq_one]
  rw [← pow_mul]
  simpa using fourthRootParameter_pow_four j

/-- Powers of the fixed primitive tenth root can be reduced modulo ten. -/
theorem primitiveTenthRoot_pow_mod_ten (n : ℕ) :
    primitiveTenthRoot ^ n =
      primitiveTenthRoot ^ (n % 10) := by
  have h := pow_mod_orderOf primitiveTenthRoot n
  rw [← primitiveTenthRoot_isPrimitive.eq_orderOf] at h
  exact h.symm

/-- The inverse of the fixed primitive tenth root is its ninth power. -/
theorem primitiveTenthRoot_inv :
    primitiveTenthRoot⁻¹ = primitiveTenthRoot ^ 9 := by
  apply mul_left_cancel₀ primitiveTenthRoot_ne_zero
  rw [mul_inv_cancel₀ primitiveTenthRoot_ne_zero]
  rw [mul_comm, ← pow_succ]
  exact primitiveTenthRoot_isPrimitive.pow_eq_one.symm

/-- Cubing a two-dimensional parameter gives the opposite-row parameter,
up to inversion (which has the same trace). -/
theorem twoDimensionalParameter_opposite_eq_cube_or_inv
    (k : Fin 4) :
    twoDimensionalParameter
          (specialLinearTwoFiveFiveOppositeIndex k) =
        twoDimensionalParameter k ^ 3 ∨
      twoDimensionalParameter
          (specialLinearTwoFiveFiveOppositeIndex k) =
        (twoDimensionalParameter k ^ 3)⁻¹ := by
  fin_cases k
  · left
    norm_num [twoDimensionalParameter,
      specialLinearTwoFiveFiveOppositeIndex]
  · right
    norm_num [twoDimensionalParameter,
      specialLinearTwoFiveFiveOppositeIndex,
      ← inv_pow, primitiveTenthRoot_inv, ← pow_mul]
    rw [primitiveTenthRoot_pow_mod_ten 54]
  · right
    norm_num [twoDimensionalParameter,
      specialLinearTwoFiveFiveOppositeIndex,
      ← inv_pow, primitiveTenthRoot_inv, ← pow_mul]
    rw [primitiveTenthRoot_pow_mod_ten 81]
    norm_num
  · left
    norm_num [twoDimensionalParameter,
      specialLinearTwoFiveFiveOppositeIndex, ← pow_mul]
    rw [primitiveTenthRoot_pow_mod_ten 12]

/-- Multiplication of the cyclic exponent by three sends each
two-dimensional row to its opposite row. -/
theorem quaternionGroupFiveTwoDimensionalCharacter_values_a_three_mul
    (k : Fin 4) (i : ZMod 10) :
    (twoDimensionalCharacter k).values
        (QuaternionGroup.a (3 * i)) =
      (twoDimensionalCharacter
        (specialLinearTwoFiveFiveOppositeIndex k)).values
          (QuaternionGroup.a i) := by
  rw [← ZMod.natCast_zmod_val i]
  simpa [Nat.cast_mul] using
    (show
      (twoDimensionalCharacter k).values
          (QuaternionGroup.a ((3 * i.val : ℕ) : ZMod 10)) =
        (twoDimensionalCharacter
          (specialLinearTwoFiveFiveOppositeIndex k)).values
            (QuaternionGroup.a (i.val : ZMod 10)) by
      rw [twoDimensionalCharacter_values_a_natCast,
        twoDimensionalCharacter_values_a_natCast]
      rcases twoDimensionalParameter_opposite_eq_cube_or_inv k with h | h
      · rw [h]
        simp only [pow_mul, inv_pow]
      · rw [h]
        simp only [pow_mul, inv_pow, inv_inv]
        ring)

/-- On the cyclic subgroup, the restricted outer action fixes linear
rows and sends two-dimensional rows to their opposite partners. -/
theorem quaternionGroupFiveNormalizerOuterCharacterRow_values_a
    (r : CharacterRow) (i : ZMod 10) :
    (pPrimeCharacterEquiv r).1.values
        (QuaternionGroup.a (3 * i)) =
      (pPrimeCharacterEquiv
        (specialLinearTwoFiveFiveNormalizerOuterCharacterRow r)).1.values
          (QuaternionGroup.a i) := by
  rcases r with j | k
  · change
      (linearCharacter j).values (QuaternionGroup.a (3 * i)) =
        (linearCharacter j).values (QuaternionGroup.a i)
    exact quaternionGroupFiveLinearCharacter_values_a_three_mul j i
  · change
      (twoDimensionalCharacter k).values
          (QuaternionGroup.a (3 * i)) =
        (twoDimensionalCharacter
          (specialLinearTwoFiveFiveOppositeIndex k)).values
            (QuaternionGroup.a i)
    exact
      quaternionGroupFiveTwoDimensionalCharacter_values_a_three_mul k i

/-- The corresponding equality on the noncyclic dicyclic coset. -/
theorem quaternionGroupFiveNormalizerOuterCharacterRow_values_xa
    (r : CharacterRow) (i : ZMod 10) :
    (pPrimeCharacterEquiv r).1.values
        (QuaternionGroup.xa (3 * i)) =
      (pPrimeCharacterEquiv
        (specialLinearTwoFiveFiveNormalizerOuterCharacterRow r)).1.values
          (QuaternionGroup.xa i) := by
  rcases r with j | k
  · change
      (linearCharacter j).values (QuaternionGroup.xa (3 * i)) =
        (linearCharacter j).values (QuaternionGroup.xa i)
    exact quaternionGroupFiveLinearCharacter_values_xa_three_mul j i
  · change
      (twoDimensionalCharacter k).values
          (QuaternionGroup.xa (3 * i)) =
        (twoDimensionalCharacter
          (specialLinearTwoFiveFiveOppositeIndex k)).values
            (QuaternionGroup.xa i)
    simp only [twoDimensionalCharacter_values_xa]

/-- The restricted diagonal outer automorphism acts on the exact
normalizer table by the displayed row permutation. -/
theorem
    specialLinearTwoFiveSylowFiveOuterAutomorphism_smul_normalizerPPrime
    (r : CharacterRow) :
    specialLinearTwoFiveSylowFiveOuterAutomorphism •
        specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv r =
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
        (specialLinearTwoFiveFiveNormalizerOuterCharacterRow r) := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  obtain ⟨q, rfl⟩ :=
    quaternionFiveEquivSylowFiveNormalizer.surjective x
  rw [SylowAutStabilizer.smul_normalizer_pPrime_values]
  rcases q with i | i
  · rw [specialLinearTwoFiveSylowFiveOuterRestriction_symm_a,
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_values,
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_values]
    exact quaternionGroupFiveNormalizerOuterCharacterRow_values_a r i
  · rw [specialLinearTwoFiveSylowFiveOuterRestriction_symm_xa,
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_values,
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_values]
    exact quaternionGroupFiveNormalizerOuterCharacterRow_values_xa r i

/-- The diagonal outer permutation preserves the ambient `5'` rows. -/
def specialLinearTwoFiveFiveOuterPPrimeRow
    (r : SpecialLinearTwoFivePPrimeCharacterRow 5) :
    SpecialLinearTwoFivePPrimeCharacterRow 5 :=
  ⟨specialLinearTwoFiveOuterCharacterRow r.1, by
    rw [specialLinearTwoFiveOuterCharacterRow_degree]
    exact r.2⟩

@[simp]
theorem
    specialLinearTwoFiveDiagonalOuterAutomorphism_smul_fivePPrimeCharacter
    (r : SpecialLinearTwoFivePPrimeCharacterRow 5) :
    specialLinearTwoFiveDiagonalOuterAutomorphism •
        specialLinearTwoFivePPrimeCharacterEquiv 5 r =
      specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveOuterPPrimeRow r) := by
  apply Subtype.ext
  exact
    specialLinearTwoFiveDiagonalOuterAutomorphism_smul_irreducibleCharacter
      r.1

/-- The explicit ambient-to-normalizer row matching intertwines the two
outer permutations. -/
theorem specialLinearTwoFiveFiveCharacterRowEquiv_map_outer
    (r : SpecialLinearTwoFivePPrimeCharacterRow 5) :
    specialLinearTwoFiveFiveCharacterRowEquiv
        (specialLinearTwoFiveFiveOuterPPrimeRow r) =
      specialLinearTwoFiveFiveNormalizerOuterCharacterRow
        (specialLinearTwoFiveFiveCharacterRowEquiv r) :=
  specialLinearTwoFiveFiveCharacterRowEquiv_outer r

end InductiveMcKay
end McKayConjecture
