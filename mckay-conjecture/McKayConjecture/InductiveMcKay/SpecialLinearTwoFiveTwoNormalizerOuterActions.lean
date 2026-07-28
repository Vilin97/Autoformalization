/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoAutomorphismClassification
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoNormalizerRepresentations

/-!
# The outer action on the binary-tetrahedral `2'`-character table

The restricted diagonal outer automorphism inverts the `C₃` quotient of the
Sylow-two normalizer.  Consequently it sends the linear row indexed by `j`
to the row indexed by `-j`.  It fixes the unique degree-three row.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForNormalizerOuterActions :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The diagonal outer permutation of the four odd-degree normalizer rows. -/
def specialLinearTwoFiveTwoNormalizerOuterPPrimeRow
    (r : SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow) :
    SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow :=
  match r with
  | ⟨.linear j, _⟩ =>
      ⟨.linear (-j), by
        norm_num [
          specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩
  | ⟨.twoDimensional j, h⟩ =>
      False.elim <| h <| by
        simp [specialLinearTwoFiveTwoNormalizerCharacterRowDegree]
  | ⟨.threeDimensional, _⟩ =>
      ⟨.threeDimensional, by
        norm_num [
          specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩

/-- The restricted diagonal outer automorphism sends the normalizer linear
row indexed by `j` to the row indexed by `-j`. -/
theorem
    specialLinearTwoFiveSylowTwoOuterAutomorphism_smul_normalizerLinear
    (j : ZMod 3) :
    specialLinearTwoFiveSylowTwoOuterAutomorphism •
        specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
          ⟨.linear j, by
            norm_num [
              specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩ =
      specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
        ⟨.linear (-j), by
          norm_num [
            specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩ := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  rw [SylowAutStabilizer.smul_normalizer_pPrime_values]
  change
    (specialLinearTwoFiveTwoNormalizerLinearCharacter j).values
          ((SylowAutStabilizer.normalizerRestrictionHom
            specialLinearTwoFiveSylowTwo
            specialLinearTwoFiveSylowTwoOuterAutomorphism).symm x) =
      (specialLinearTwoFiveTwoNormalizerLinearCharacter (-j)).values x
  rw [
    specialLinearTwoFiveTwoNormalizerLinearCharacter_values,
    specialLinearTwoFiveTwoNormalizerLinearCharacter_values]
  change
    (specialLinearTwoFiveTwoNormalizerLinearHom j
          ((SylowAutStabilizer.normalizerRestrictionHom
            specialLinearTwoFiveSylowTwo
            specialLinearTwoFiveSylowTwoOuterAutomorphism).symm x) :
        ℂ) =
      (specialLinearTwoFiveTwoNormalizerLinearHom (-j) x : ℂ)
  change
    (ZMod.toCircle
        (j *
          Multiplicative.toAdd
            (specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient
              ((SylowAutStabilizer.normalizerRestrictionHom
                specialLinearTwoFiveSylowTwo
                specialLinearTwoFiveSylowTwoOuterAutomorphism).symm x))) :
      ℂ) =
    (ZMod.toCircle
        ((-j) *
          Multiplicative.toAdd
            (specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient x)) :
      ℂ)
  rw [
    specialLinearTwoFiveSylowTwoOuterAutomorphism_cyclicQuotient_symm]
  congr 2
  ring

/-- The unique degree-three normalizer row is fixed by the restricted
diagonal outer automorphism. -/
theorem
    specialLinearTwoFiveSylowTwoOuterAutomorphism_smul_normalizerThree :
    specialLinearTwoFiveSylowTwoOuterAutomorphism •
        specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
          ⟨.threeDimensional, by
            norm_num [
              specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩ =
      specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
        ⟨.threeDimensional, by
          norm_num [
            specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩ := by
  let χ :
      PPrimeIrreducibleCharacter
        SpecialLinearTwoFiveSylowTwoNormalizer 2 :=
    specialLinearTwoFiveSylowTwoOuterAutomorphism •
      specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
        ⟨.threeDimensional, by
          norm_num [
            specialLinearTwoFiveTwoNormalizerCharacterRowDegree]⟩
  let r : SpecialLinearTwoFiveTwoNormalizerCharacterRow :=
    specialLinearTwoFiveTwoNormalizerIrreducibleCharacterEquiv.symm χ.1
  have hrDegree :
      specialLinearTwoFiveTwoNormalizerCharacterRowDegree r = 3 := by
    rw [← specialLinearTwoFiveTwoNormalizerIrreducibleCharacter_degree]
    change
      (specialLinearTwoFiveTwoNormalizerIrreducibleCharacter r).degree =
        3
    rw [show
      specialLinearTwoFiveTwoNormalizerIrreducibleCharacter r = χ.1 by
        exact
          specialLinearTwoFiveTwoNormalizerIrreducibleCharacterEquiv
            |>.apply_symm_apply χ.1]
    change
      ((SylowAutStabilizer.normalizerRestrictionHom
          specialLinearTwoFiveSylowTwo
          specialLinearTwoFiveSylowTwoOuterAutomorphism) •
        specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter).degree =
        3
    rw [IrreducibleCharacter.smul_degree,
      specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter_degree]
  have hr : r = .threeDimensional := by
    rcases r with j | j | _
    · norm_num [
        specialLinearTwoFiveTwoNormalizerCharacterRowDegree] at hrDegree
    · norm_num [
        specialLinearTwoFiveTwoNormalizerCharacterRowDegree] at hrDegree
    · rfl
  apply Subtype.ext
  change χ.1 =
    specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter
  rw [←
    specialLinearTwoFiveTwoNormalizerIrreducibleCharacterEquiv
      |>.apply_symm_apply χ.1]
  change
    specialLinearTwoFiveTwoNormalizerIrreducibleCharacter r =
      specialLinearTwoFiveTwoNormalizerIrreducibleCharacter
        .threeDimensional
  rw [hr]

/-- The restricted diagonal outer automorphism acts by the displayed
permutation on all four odd-degree normalizer rows. -/
@[simp]
theorem specialLinearTwoFiveSylowTwoOuterAutomorphism_smul_normalizerPPrime
    (r : SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow) :
    specialLinearTwoFiveSylowTwoOuterAutomorphism •
        specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv r =
      specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv
        (specialLinearTwoFiveTwoNormalizerOuterPPrimeRow r) := by
  rcases r with ⟨r, hr⟩
  rcases r with j | j | _
  · exact
      specialLinearTwoFiveSylowTwoOuterAutomorphism_smul_normalizerLinear j
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveTwoNormalizerCharacterRowDegree]
  · exact
      specialLinearTwoFiveSylowTwoOuterAutomorphism_smul_normalizerThree

end InductiveMcKay
end McKayConjecture
