/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveFiveInnerProjectiveRows
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveGeneralLinearInvariantRows
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveGeneralLinearScalarAlignment

/-!
# The three nontrivial outer-fixed projective rows at `p = 5`

The symmetric-cube, tensor, and symmetric-fifth-power rows are fixed by
the outer automorphism.  They are matched with linear normalizer rows
`1`, `2`, and `3`.  Their values on the common central involution agree
after division by degree, so the general-linear scalar-alignment theorem
supplies the projective representations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open QuaternionGroupFive

local instance factPrimeFiveForFixedProjectiveRows :
    Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The three nontrivial ambient rows fixed by the outer automorphism. -/
def specialLinearTwoFiveFiveFixedAmbientRow
    (j : Fin 3) : SpecialLinearTwoFiveCharacterRow :=
  match j.val with
  | 0 => .symmetricCube
  | 1 => .tensor
  | _ => .symmetricFifthPower

/-- Their matching nontrivial linear row indices `1,2,3`. -/
def specialLinearTwoFiveFiveFixedLinearIndex
    (j : Fin 3) : Fin 4 :=
  ⟨j.val + 1, by omega⟩

/-- The corresponding rows in the ambient `5'` subtype. -/
def specialLinearTwoFiveFiveFixedPPrimeRow
    (j : Fin 3) : SpecialLinearTwoFivePPrimeCharacterRow 5 :=
  ⟨specialLinearTwoFiveFiveFixedAmbientRow j, by
    revert j
    native_decide⟩

@[simp]
theorem specialLinearTwoFiveFiveFixedAmbientRow_outer
    (j : Fin 3) :
    specialLinearTwoFiveOuterCharacterRow
        (specialLinearTwoFiveFiveFixedAmbientRow j) =
      specialLinearTwoFiveFiveFixedAmbientRow j := by
  fin_cases j <;> rfl

@[simp]
theorem specialLinearTwoFiveFiveCharacterRowEquiv_fixedRow
    (j : Fin 3) :
    specialLinearTwoFiveFiveCharacterRowEquiv
        (specialLinearTwoFiveFiveFixedPPrimeRow j) =
      .linear (specialLinearTwoFiveFiveFixedLinearIndex j) := by
  fin_cases j <;> rfl

/-- The local character paired with a fixed row is its displayed linear
normalizer character. -/
theorem specialLinearTwoFiveFiveFixedLocalCharacter_eq
    (j : Fin 3) :
    (specialLinearTwoFiveFiveEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveFixedPPrimeRow j))).1 =
      (specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
        (.linear
          (specialLinearTwoFiveFiveFixedLinearIndex j))).1 := by
  rw [specialLinearTwoFiveFiveEquivariantMcKayEquiv_apply,
    specialLinearTwoFiveFiveCharacterRowEquiv_fixedRow]

/-- Each of the three ambient characters is invariant under conjugation
by every element of `GL(2, 𝔽₅)`. -/
theorem specialLinearTwoFiveFiveFixedAmbient_generalLinear_invariant
    (j : Fin 3)
    (u : GeneralLinearTwoFive)
    (g : SpecialLinearTwoFive) :
    (specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveFixedPPrimeRow j)).1.values
          (generalLinearTwoFiveConjugation u g) =
      (specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveFixedPPrimeRow j)).1.values g := by
  change
    (specialLinearTwoFiveIrreducibleCharacter
      (specialLinearTwoFiveFiveFixedAmbientRow j)).values
        (generalLinearTwoFiveConjugation u g) =
      (specialLinearTwoFiveIrreducibleCharacter
        (specialLinearTwoFiveFiveFixedAmbientRow j)).values g
  exact
    specialLinearTwoFive_irreducibleCharacter_generalLinear_invariant_of_outer_fixed
      (specialLinearTwoFiveFiveFixedAmbientRow j)
      (specialLinearTwoFiveFiveFixedAmbientRow_outer j) u g

/-- The common scalar on the central involution: `-1,+1,-1` for the
three rows in order. -/
def specialLinearTwoFiveFiveFixedCentralSign
    (j : Fin 3) : ℂ :=
  if j.val = 1 then 1 else -1

theorem specialLinearTwoFiveFiveFixedAmbient_values_neg_one
    (j : Fin 3) :
    (specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveFixedPPrimeRow j)).1.values (-1) =
      specialLinearTwoFiveFiveFixedCentralSign j *
        ((specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveFixedPPrimeRow j)).1.degree : ℂ) := by
  change
    (specialLinearTwoFiveIrreducibleCharacter
      (specialLinearTwoFiveFiveFixedAmbientRow j)).values
        (specialLinearTwoFiveConjugacyRepresentative 1) =
      specialLinearTwoFiveFiveFixedCentralSign j *
        ((specialLinearTwoFiveIrreducibleCharacter
          (specialLinearTwoFiveFiveFixedAmbientRow j)).degree : ℂ)
  rw [specialLinearTwoFiveIrreducibleCharacter_values_representative,
    specialLinearTwoFiveIrreducibleCharacter_degree]
  fin_cases j <;>
    norm_num [specialLinearTwoFiveFiveFixedAmbientRow,
      specialLinearTwoFiveFiveFixedCentralSign,
      specialLinearTwoFiveCharacterTableValue,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralSymmetricCubeValue,
      binaryIcosahedralSymmetricFifthPowerValue,
      specialLinearTwoFiveCharacterRowDegree]

@[simp]
theorem quaternionGroupFiveLinearHom_apply_a_natCast
    (j : Fin 4) (n : ℕ) :
    linearHom j (QuaternionGroup.a (n : ZMod 10)) =
      (fourthRootParameter j ^ 2) ^ n := by
  simp [linearHom, linearHomOfFourthRoot,
    QuaternionGroup.zmodPower_natCast]

theorem specialLinearTwoFiveFiveFixedLocal_values_neg_one
    (j : Fin 3) :
    (specialLinearTwoFiveFiveEquivariantMcKayEquiv
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveFixedPPrimeRow j))).1.values
          (specialLinearTwoFiveCentralNegOneNormalizer
            specialLinearTwoFiveSylowFive) =
      specialLinearTwoFiveFiveFixedCentralSign j *
        ((specialLinearTwoFiveFiveEquivariantMcKayEquiv
          (specialLinearTwoFivePPrimeCharacterEquiv 5
            (specialLinearTwoFiveFiveFixedPPrimeRow j))).1.degree : ℂ) := by
  rw [specialLinearTwoFiveFiveFixedLocalCharacter_eq]
  have hneg :
      specialLinearTwoFiveCentralNegOneNormalizer
          specialLinearTwoFiveSylowFive =
        specialLinearTwoFiveSylowFiveNormalizerNegOne := by
    apply Subtype.ext
    simp
  rw [hneg]
  rw [show
    specialLinearTwoFiveSylowFiveNormalizerNegOne =
      quaternionFiveEquivSylowFiveNormalizer
        (QuaternionGroup.a 5) from rfl]
  rw [specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_values,
    specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_degree_linear]
  rw [pPrimeCharacterEquiv_apply]
  simp only [pPrimeCharacter, linearPPrimeCharacter]
  norm_num only [Nat.cast_one, mul_one]
  change
    (linearCharacter
      (specialLinearTwoFiveFiveFixedLinearIndex j)).values
        (QuaternionGroup.a (5 : ZMod 10)) =
      specialLinearTwoFiveFiveFixedCentralSign j
  simp only [linearCharacter, IrreducibleCharacter.linear_values]
  change
    ((linearHom
      (specialLinearTwoFiveFiveFixedLinearIndex j)
      (QuaternionGroup.a (5 : ZMod 10)) : ℂˣ) : ℂ) =
      specialLinearTwoFiveFiveFixedCentralSign j
  rw [show (5 : ZMod 10) = ((5 : ℕ) : ZMod 10) by norm_num,
    quaternionGroupFiveLinearHom_apply_a_natCast]
  fin_cases j <;>
    norm_num [specialLinearTwoFiveFiveFixedLinearIndex,
      specialLinearTwoFiveFiveFixedCentralSign,
      fourthRootParameter, imaginaryUnit,
      pow_succ, Complex.I_mul_I]

theorem specialLinearTwoFiveFiveFixed_centralCross
    (j : Fin 3) :
    (specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveFixedPPrimeRow j)).1.values (-1) *
          ((specialLinearTwoFiveFiveEquivariantMcKayEquiv
            (specialLinearTwoFivePPrimeCharacterEquiv 5
              (specialLinearTwoFiveFiveFixedPPrimeRow j))).1.degree :
            ℂ) =
      (specialLinearTwoFiveFiveEquivariantMcKayEquiv
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveFixedPPrimeRow j))).1.values
            (specialLinearTwoFiveCentralNegOneNormalizer
              specialLinearTwoFiveSylowFive) *
        ((specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveFixedPPrimeRow j)).1.degree : ℂ) := by
  rw [specialLinearTwoFiveFiveFixedAmbient_values_neg_one,
    specialLinearTwoFiveFiveFixedLocal_values_neg_one]
  ring

/-- Projective compatibility for each nontrivial outer-fixed `p = 5`
row. -/
theorem specialLinearTwoFiveFiveFixedRow_tripleCompatible
    (j : Fin 3) :
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveFixedPPrimeRow j)) := by
  apply
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
      |>.tripleCompatible_of_generalLinearCover
        specialLinearTwoFiveSylowFive
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveFixedPPrimeRow j))
  · exact
      specialLinearTwoFiveFiveFixedAmbient_generalLinear_invariant j
  · exact specialLinearTwoFiveFiveFixed_centralCross j

/-- Concrete projective row data for the three nontrivial fixed rows. -/
def specialLinearTwoFiveFiveFixedProjectiveRowData
    (j : Fin 3) :
    ExactNormalizerProjectiveRowData
      specialLinearTwoFiveFiveEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveFixedPPrimeRow j)) :=
  ExactNormalizerProjectiveRowData.ofTripleCompatible
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
    (specialLinearTwoFivePPrimeCharacterEquiv 5
      (specialLinearTwoFiveFiveFixedPPrimeRow j))
    (specialLinearTwoFiveFiveFixedRow_tripleCompatible j)

/-- All eight rows of the `5'` table satisfy the projective clause. -/
theorem specialLinearTwoFiveFive_allRows_tripleCompatible
    (r : SpecialLinearTwoFivePPrimeCharacterRow 5) :
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFivePPrimeCharacterEquiv 5 r) := by
  rcases r with ⟨r, hr⟩
  rcases r with _ | k | k | _ | _ | _ | _
  · have hrow :
        (⟨.trivial, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 5) =
            specialLinearTwoFiveFiveTrivialPPrimeRow :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveFiveTrivialRow_tripleCompatible
  · let j : Fin 4 :=
      Fin.cases 0 (fun _ : Fin 1 ↦ 2) k
    have hrow :
        (⟨.faithful k, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 5) =
            specialLinearTwoFiveFiveTwoDimensionalPPrimeRow j := by
      apply Subtype.ext
      fin_cases k <;> rfl
    rw [hrow]
    exact
      specialLinearTwoFiveFiveTwoDimensionalRow_tripleCompatible j
  · let j : Fin 4 :=
      Fin.cases 1 (fun _ : Fin 1 ↦ 3) k
    have hrow :
        (⟨.symmetricSquare k, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 5) =
            specialLinearTwoFiveFiveTwoDimensionalPPrimeRow j := by
      apply Subtype.ext
      fin_cases k <;> rfl
    rw [hrow]
    exact
      specialLinearTwoFiveFiveTwoDimensionalRow_tripleCompatible j
  · have hrow :
        (⟨.symmetricCube, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 5) =
            specialLinearTwoFiveFiveFixedPPrimeRow 0 :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveFiveFixedRow_tripleCompatible 0
  · have hrow :
        (⟨.tensor, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 5) =
            specialLinearTwoFiveFiveFixedPPrimeRow 1 :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveFiveFixedRow_tripleCompatible 1
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]
  · have hrow :
        (⟨.symmetricFifthPower, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 5) =
            specialLinearTwoFiveFiveFixedPPrimeRow 2 :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveFiveFixedRow_tripleCompatible 2

/-- The complete checked projective table at `p = 5`. -/
def specialLinearTwoFiveFiveProjectiveTableCompletion :
    SpecialLinearTwoFiveFiveProjectiveTableCompletion
      (SpecialLinearTwoFivePPrimeCharacterRow 5) where
  characterTable := specialLinearTwoFiveFiveCharacterTableCompletion
  projectiveRow r :=
    ExactNormalizerProjectiveRowData.ofTripleCompatible
      specialLinearTwoFiveFiveEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 5 r)
      (specialLinearTwoFiveFive_allRows_tripleCompatible r)

end InductiveMcKay
end McKayConjecture
