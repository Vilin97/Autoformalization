/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveGeneralLinearInvariantRows
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveGeneralLinearScalarAlignment
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeProjectiveRows

/-!
# Outer-fixed projective rows at `p = 3`

Besides the two faithful rows already handled by inner stabilizer lifts,
the `3'` table has four outer-fixed rows: trivial, symmetric cube, tensor,
and symmetric fourth power.  Their matched normalizer rows have the same
central-involution scalar, so the general-linear scalar-alignment theorem
supplies all four projective comparisons.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeThreeForFixedProjectiveRows :
    Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The four outer-fixed rows in the ambient `3'` table. -/
def specialLinearTwoFiveThreeFixedAmbientRow
    (j : Fin 4) : SpecialLinearTwoFiveCharacterRow :=
  match j.val with
  | 0 => .trivial
  | 1 => .symmetricCube
  | 2 => .tensor
  | _ => .symmetricFourthPower

/-- The corresponding rows in the exact-normalizer table. -/
def specialLinearTwoFiveThreeFixedNormalizerRow
    (j : Fin 4) : QuaternionGroupThreeCharacterRow :=
  match j.val with
  | 0 => .linear 0
  | 1 => .twoDimensional 0
  | 2 => .linear 2
  | _ => .twoDimensional 1

def specialLinearTwoFiveThreeFixedPPrimeRow
    (j : Fin 4) : SpecialLinearTwoFivePPrimeCharacterRow 3 :=
  ⟨specialLinearTwoFiveThreeFixedAmbientRow j, by
    revert j
    native_decide⟩

@[simp]
theorem specialLinearTwoFiveThreeFixedAmbientRow_outer
    (j : Fin 4) :
    specialLinearTwoFiveOuterCharacterRow
        (specialLinearTwoFiveThreeFixedAmbientRow j) =
      specialLinearTwoFiveThreeFixedAmbientRow j := by
  fin_cases j <;> rfl

@[simp]
theorem specialLinearTwoFiveThreeCharacterRowEquiv_fixedRow
    (j : Fin 4) :
    specialLinearTwoFiveThreeCharacterRowEquiv
        (specialLinearTwoFiveThreeFixedPPrimeRow j) =
      specialLinearTwoFiveThreeFixedNormalizerRow j := by
  fin_cases j <;> rfl

theorem specialLinearTwoFiveThreeFixedLocalCharacter_eq
    (j : Fin 4) :
    (specialLinearTwoFiveThreeEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeFixedPPrimeRow j))).1 =
      (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
        (specialLinearTwoFiveThreeFixedNormalizerRow j)).1 := by
  rw [specialLinearTwoFiveThreeEquivariantMcKayEquiv_apply,
    specialLinearTwoFiveThreeCharacterRowEquiv_fixedRow]

theorem specialLinearTwoFiveThreeFixedAmbient_generalLinear_invariant
    (j : Fin 4)
    (u : GeneralLinearTwoFive)
    (g : SpecialLinearTwoFive) :
    (specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeFixedPPrimeRow j)).1.values
          (generalLinearTwoFiveConjugation u g) =
      (specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeFixedPPrimeRow j)).1.values g := by
  change
    (specialLinearTwoFiveIrreducibleCharacter
      (specialLinearTwoFiveThreeFixedAmbientRow j)).values
        (generalLinearTwoFiveConjugation u g) =
      (specialLinearTwoFiveIrreducibleCharacter
        (specialLinearTwoFiveThreeFixedAmbientRow j)).values g
  exact
    specialLinearTwoFive_irreducibleCharacter_generalLinear_invariant_of_outer_fixed
      (specialLinearTwoFiveThreeFixedAmbientRow j)
      (specialLinearTwoFiveThreeFixedAmbientRow_outer j) u g

/-- The common central signs are `+1,-1,+1,+1`. -/
def specialLinearTwoFiveThreeFixedCentralSign (j : Fin 4) : ℂ :=
  if j.val = 1 then -1 else 1

theorem specialLinearTwoFiveThreeFixedAmbient_values_neg_one
    (j : Fin 4) :
    (specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeFixedPPrimeRow j)).1.values (-1) =
      specialLinearTwoFiveThreeFixedCentralSign j *
        ((specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFixedPPrimeRow j)).1.degree : ℂ) := by
  change
    (specialLinearTwoFiveIrreducibleCharacter
      (specialLinearTwoFiveThreeFixedAmbientRow j)).values
        (specialLinearTwoFiveConjugacyRepresentative 1) =
      specialLinearTwoFiveThreeFixedCentralSign j *
        ((specialLinearTwoFiveIrreducibleCharacter
          (specialLinearTwoFiveThreeFixedAmbientRow j)).degree : ℂ)
  rw [specialLinearTwoFiveIrreducibleCharacter_values_representative,
    specialLinearTwoFiveIrreducibleCharacter_degree]
  fin_cases j <;>
    norm_num [specialLinearTwoFiveThreeFixedAmbientRow,
      specialLinearTwoFiveThreeFixedCentralSign,
      specialLinearTwoFiveCharacterTableValue,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralSymmetricCubeValue,
      binaryIcosahedralSymmetricFourthPowerValue,
      specialLinearTwoFiveCharacterRowDegree]

theorem quaternionGroupThreeSixthRootCharacter_three :
    quaternionGroupThreeSixthRootCharacter (3 : ZMod 6) = -1 := by
  change ((ZMod.toCircle (3 : ZMod 6) : Circle) : ℂ) = -1
  calc
    _ = Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (3 : ℂ) / (6 : ℂ)) :=
      ZMod.toCircle_natCast (N := 6) 3
    _ = -1 := by
      convert Complex.exp_pi_mul_I using 1 <;> ring_nf

theorem specialLinearTwoFiveThreeFixedLocal_values_neg_one
    (j : Fin 4) :
    (specialLinearTwoFiveThreeEquivariantMcKayEquiv
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFixedPPrimeRow j))).1.values
          (specialLinearTwoFiveCentralNegOneNormalizer
            specialLinearTwoFiveSylowThree) =
      specialLinearTwoFiveThreeFixedCentralSign j *
        ((specialLinearTwoFiveThreeEquivariantMcKayEquiv
          (specialLinearTwoFivePPrimeCharacterEquiv 3
            (specialLinearTwoFiveThreeFixedPPrimeRow j))).1.degree : ℂ) := by
  rw [specialLinearTwoFiveThreeFixedLocalCharacter_eq]
  have hneg :
      specialLinearTwoFiveCentralNegOneNormalizer
          specialLinearTwoFiveSylowThree =
        specialLinearTwoFiveSylowThreeNormalizerNegOne := by
    apply Subtype.ext
    simp
  rw [hneg]
  change
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
      (specialLinearTwoFiveThreeFixedNormalizerRow j)).1.values
        (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
          (QuaternionGroup.a 3)) =
      specialLinearTwoFiveThreeFixedCentralSign j *
        ((specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
          (specialLinearTwoFiveThreeFixedNormalizerRow j)).1.degree : ℂ)
  rw [specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values,
    specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_degree,
    quaternionGroupThreePPrimeCharacterEquiv_apply]
  fin_cases j
  · simp only [specialLinearTwoFiveThreeFixedNormalizerRow]
    simp only [quaternionGroupThreePPrimeCharacter]
    rw [
      quaternionGroupThreeLinearPPrimeCharacter_values_a,
      quaternionGroupThreeLinearPPrimeCharacter_degree]
    simp [specialLinearTwoFiveThreeFixedCentralSign]
  · simp only [specialLinearTwoFiveThreeFixedNormalizerRow]
    simp only [quaternionGroupThreePPrimeCharacter]
    change
      (quaternionGroupThreeTwoIrreducibleCharacter 0).values
          (QuaternionGroup.a 3) =
        specialLinearTwoFiveThreeFixedCentralSign 1 *
          ((quaternionGroupThreeTwoIrreducibleCharacter 0).degree : ℂ)
    rw [quaternionGroupThreeTwoIrreducibleCharacter_values_a,
      quaternionGroupThreeTwoIrreducibleCharacter_degree]
    change
      quaternionGroupThreeSixthRootCharacter (3 : ZMod 6) +
          quaternionGroupThreeSixthRootCharacter (3 : ZMod 6) =
        (-1 : ℂ) * 2
    rw [quaternionGroupThreeSixthRootCharacter_three]
    norm_num
  · simp only [specialLinearTwoFiveThreeFixedNormalizerRow]
    simp only [quaternionGroupThreePPrimeCharacter]
    rw [
      quaternionGroupThreeLinearPPrimeCharacter_values_a,
      quaternionGroupThreeLinearPPrimeCharacter_degree]
    norm_num only [Nat.cast_one, mul_one]
    rw [show (3 : ZMod 6).val = 3 by native_decide]
    rw [show
      (2 : ZMod 4) *
          (2 * ((3 : ℕ) : ZMod 4)) =
        0 by native_decide]
    simp [specialLinearTwoFiveThreeFixedCentralSign]
  · simp only [specialLinearTwoFiveThreeFixedNormalizerRow]
    simp only [quaternionGroupThreePPrimeCharacter]
    change
      (quaternionGroupThreeTwoIrreducibleCharacter 1).values
          (QuaternionGroup.a 3) =
        specialLinearTwoFiveThreeFixedCentralSign 3 *
          ((quaternionGroupThreeTwoIrreducibleCharacter 1).degree : ℂ)
    rw [quaternionGroupThreeTwoIrreducibleCharacter_values_a,
      quaternionGroupThreeTwoIrreducibleCharacter_degree]
    change
      quaternionGroupThreeSixthRootCharacter (0 : ZMod 6) +
          quaternionGroupThreeSixthRootCharacter (0 : ZMod 6) =
        (1 : ℂ) * 2
    norm_num

theorem specialLinearTwoFiveThreeFixed_centralCross
    (j : Fin 4) :
    (specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeFixedPPrimeRow j)).1.values (-1) *
          ((specialLinearTwoFiveThreeEquivariantMcKayEquiv
            (specialLinearTwoFivePPrimeCharacterEquiv 3
              (specialLinearTwoFiveThreeFixedPPrimeRow j))).1.degree :
            ℂ) =
      (specialLinearTwoFiveThreeEquivariantMcKayEquiv
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFixedPPrimeRow j))).1.values
            (specialLinearTwoFiveCentralNegOneNormalizer
              specialLinearTwoFiveSylowThree) *
        ((specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFixedPPrimeRow j)).1.degree : ℂ) := by
  rw [specialLinearTwoFiveThreeFixedAmbient_values_neg_one,
    specialLinearTwoFiveThreeFixedLocal_values_neg_one]
  ring

theorem specialLinearTwoFiveThreeFixedRow_tripleCompatible
    (j : Fin 4) :
    specialLinearTwoFiveThreeEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFixedPPrimeRow j)) := by
  apply
    specialLinearTwoFiveThreeEquivariantMcKayEquiv
      |>.tripleCompatible_of_generalLinearCover
        specialLinearTwoFiveSylowThree
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFixedPPrimeRow j))
  · exact
      specialLinearTwoFiveThreeFixedAmbient_generalLinear_invariant j
  · exact specialLinearTwoFiveThreeFixed_centralCross j

def specialLinearTwoFiveThreeFixedProjectiveRowData
    (j : Fin 4) :
    ExactNormalizerProjectiveRowData
      specialLinearTwoFiveThreeEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeFixedPPrimeRow j)) :=
  ExactNormalizerProjectiveRowData.ofTripleCompatible
    specialLinearTwoFiveThreeEquivariantMcKayEquiv
    (specialLinearTwoFivePPrimeCharacterEquiv 3
      (specialLinearTwoFiveThreeFixedPPrimeRow j))
    (specialLinearTwoFiveThreeFixedRow_tripleCompatible j)

theorem specialLinearTwoFiveThree_allRows_tripleCompatible
    (r : SpecialLinearTwoFivePPrimeCharacterRow 3) :
    specialLinearTwoFiveThreeEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFivePPrimeCharacterEquiv 3 r) := by
  rcases r with ⟨r, hr⟩
  rcases r with _ | k | k | _ | _ | _ | _
  · have hrow :
        (⟨.trivial, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 3) =
            specialLinearTwoFiveThreeFixedPPrimeRow 0 :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveThreeFixedRow_tripleCompatible 0
  · have hrow :
        (⟨.faithful k, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 3) =
            specialLinearTwoFiveThreeFaithfulRow k :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveThreeFaithfulRow_tripleCompatible k
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]
  · have hrow :
        (⟨.symmetricCube, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 3) =
            specialLinearTwoFiveThreeFixedPPrimeRow 1 :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveThreeFixedRow_tripleCompatible 1
  · have hrow :
        (⟨.tensor, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 3) =
            specialLinearTwoFiveThreeFixedPPrimeRow 2 :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveThreeFixedRow_tripleCompatible 2
  · have hrow :
        (⟨.symmetricFourthPower, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 3) =
            specialLinearTwoFiveThreeFixedPPrimeRow 3 :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveThreeFixedRow_tripleCompatible 3
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]

def specialLinearTwoFiveThreeProjectiveTableCompletion :
    SpecialLinearTwoFiveThreeProjectiveTableCompletion
      (SpecialLinearTwoFivePPrimeCharacterRow 3) where
  characterTable := specialLinearTwoFiveThreeCharacterTableCompletion
  projectiveRow r :=
    ExactNormalizerProjectiveRowData.ofTripleCompatible
      specialLinearTwoFiveThreeEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 3 r)
      (specialLinearTwoFiveThree_allRows_tripleCompatible r)

end InductiveMcKay
end McKayConjecture
