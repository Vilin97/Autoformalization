/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveCharacterValues

/-!
# Orthogonality of the symbolic `SL(2, 𝔽₅)` character table

The symmetric-power formulas in
`SpecialLinearTwoFiveCharacterValues` first reduce to the familiar compact
binary-icosahedral table.  A direct weighted calculation with conjugacy
class sizes then proves all nine rows orthogonal, with squared norm `120`.

The calculation is split by rows so that every declaration remains well
within the default heartbeat budget.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Reduced symmetric-square row for a golden root `u`. -/
def binaryIcosahedralReducedSymmetricSquareValue
    (u : ℂ) :
    SpecialLinearTwoFiveConjugacyClass → ℂ
  | 0 => 3
  | 1 => 3
  | 2 => -1
  | 3 => 0
  | 4 => 0
  | 5 => u
  | 6 => 1 - u
  | 7 => 1 - u
  | 8 => u

/-- Reduced symmetric-cube row. -/
def binaryIcosahedralReducedSymmetricCubeValue :
    SpecialLinearTwoFiveConjugacyClass → ℂ
  | 0 => 4
  | 1 => -4
  | 2 => 0
  | 3 => -1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => -1
  | 8 => -1

/-- Reduced tensor-product row. -/
def binaryIcosahedralReducedTensorValue :
    SpecialLinearTwoFiveConjugacyClass → ℂ
  | 0 => 4
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => -1
  | 6 => -1
  | 7 => -1
  | 8 => -1

/-- Reduced fourth-symmetric-power row. -/
def binaryIcosahedralReducedSymmetricFourthPowerValue :
    SpecialLinearTwoFiveConjugacyClass → ℂ
  | 0 => 5
  | 1 => 5
  | 2 => 1
  | 3 => -1
  | 4 => -1
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0

/-- Reduced fifth-symmetric-power row. -/
def binaryIcosahedralReducedSymmetricFifthPowerValue :
    SpecialLinearTwoFiveConjugacyClass → ℂ
  | 0 => 6
  | 1 => -6
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => -1
  | 6 => -1
  | 7 => 1
  | 8 => 1

/-- Compact form of all nine symbolic rows. -/
def specialLinearTwoFiveReducedCharacterTableValue
    (t : ℂ) :
    SpecialLinearTwoFiveCharacterRow →
      SpecialLinearTwoFiveConjugacyClass → ℂ
  | .trivial, _ => 1
  | .faithful k, c =>
      binaryIcosahedralDefiningTrace
        (binaryIcosahedralGoldenRootChoice t k) c
  | .symmetricSquare k, c =>
      binaryIcosahedralReducedSymmetricSquareValue
        (binaryIcosahedralGoldenRootChoice t k) c
  | .symmetricCube, c =>
      binaryIcosahedralReducedSymmetricCubeValue c
  | .tensor, c =>
      binaryIcosahedralReducedTensorValue c
  | .symmetricFourthPower, c =>
      binaryIcosahedralReducedSymmetricFourthPowerValue c
  | .symmetricFifthPower, c =>
      binaryIcosahedralReducedSymmetricFifthPowerValue c

theorem binaryIcosahedralSymmetricSquareValue_eq_reduced
    (u : ℂ) (hu : u ^ 2 = u + 1)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    binaryIcosahedralSymmetricSquareValue u c =
      binaryIcosahedralReducedSymmetricSquareValue u c := by
  fin_cases c <;>
    simp [binaryIcosahedralSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralDefiningTrace] <;>
    ring_nf
  all_goals
    rw [hu]
    ring

theorem binaryIcosahedralSymmetricCubeValue_eq_reduced
    (u : ℂ) (hu : u ^ 2 = u + 1)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    binaryIcosahedralSymmetricCubeValue u c =
      binaryIcosahedralReducedSymmetricCubeValue c := by
  have hu3 : u ^ 3 = 2 * u + 1 := by
    calc
      u ^ 3 = u * u ^ 2 := by ring
      _ = u * (u + 1) := by rw [hu]
      _ = 2 * u + 1 := by
        linear_combination hu
  fin_cases c <;>
    simp [binaryIcosahedralSymmetricCubeValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralDefiningTrace] <;>
    ring_nf
  all_goals
    simp only [hu3, hu]
    ring

theorem binaryIcosahedralSymmetricFourthPowerValue_eq_reduced
    (u : ℂ) (hu : u ^ 2 = u + 1)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    binaryIcosahedralSymmetricFourthPowerValue u c =
      binaryIcosahedralReducedSymmetricFourthPowerValue c := by
  have hu3 : u ^ 3 = 2 * u + 1 := by
    calc
      u ^ 3 = u * u ^ 2 := by ring
      _ = u * (u + 1) := by rw [hu]
      _ = 2 * u + 1 := by
        linear_combination hu
  have hu4 : u ^ 4 = 3 * u + 2 := by
    calc
      u ^ 4 = u * u ^ 3 := by ring
      _ = u * (2 * u + 1) := by rw [hu3]
      _ = 3 * u + 2 := by
        linear_combination 2 * hu
  fin_cases c <;>
    simp [binaryIcosahedralSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralDefiningTrace] <;>
    ring_nf
  all_goals
    simp only [hu4, hu3, hu]
    ring

theorem binaryIcosahedralSymmetricFifthPowerValue_eq_reduced
    (u : ℂ) (hu : u ^ 2 = u + 1)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    binaryIcosahedralSymmetricFifthPowerValue u c =
      binaryIcosahedralReducedSymmetricFifthPowerValue c := by
  have hu3 : u ^ 3 = 2 * u + 1 := by
    calc
      u ^ 3 = u * u ^ 2 := by ring
      _ = u * (u + 1) := by rw [hu]
      _ = 2 * u + 1 := by
        linear_combination hu
  have hu4 : u ^ 4 = 3 * u + 2 := by
    calc
      u ^ 4 = u * u ^ 3 := by ring
      _ = u * (2 * u + 1) := by rw [hu3]
      _ = 3 * u + 2 := by
        linear_combination 2 * hu
  have hu5 : u ^ 5 = 5 * u + 3 := by
    calc
      u ^ 5 = u * u ^ 4 := by ring
      _ = u * (3 * u + 2) := by rw [hu4]
      _ = 5 * u + 3 := by
        linear_combination 3 * hu
  fin_cases c <;>
    simp [binaryIcosahedralSymmetricFifthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      binaryIcosahedralDefiningTrace] <;>
    ring_nf
  all_goals
    simp only [hu5, hu4, hu3, hu]
    ring

theorem binaryIcosahedralTensorValue_eq_reduced
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    binaryIcosahedralDefiningTrace t c *
        binaryIcosahedralDefiningTrace (1 - t) c =
      binaryIcosahedralReducedTensorValue c := by
  fin_cases c <;>
    simp [binaryIcosahedralDefiningTrace,
      binaryIcosahedralReducedTensorValue] <;>
    ring_nf
  all_goals
    rw [ht]
    ring

/-- Every polynomial row reduces to the compact table. -/
theorem specialLinearTwoFiveCharacterTableValue_eq_reduced
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (r : SpecialLinearTwoFiveCharacterRow)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    specialLinearTwoFiveCharacterTableValue t r c =
      specialLinearTwoFiveReducedCharacterTableValue t r c := by
  rcases r with _ | k | k | _ | _ | _ | _
  · rfl
  · rfl
  · exact
      binaryIcosahedralSymmetricSquareValue_eq_reduced
        (binaryIcosahedralGoldenRootChoice t k)
        (binaryIcosahedralGoldenRootChoice_sq t ht k) c
  · exact
      binaryIcosahedralSymmetricCubeValue_eq_reduced
        t ht c
  · exact binaryIcosahedralTensorValue_eq_reduced t ht c
  · exact
      binaryIcosahedralSymmetricFourthPowerValue_eq_reduced
        t ht c
  · exact
      binaryIcosahedralSymmetricFifthPowerValue_eq_reduced
        t ht c

/-- Weighted pairing of two rows after polynomial reduction. -/
def specialLinearTwoFiveReducedCharacterTableWeightedPairing
    (t : ℂ)
    (r s : SpecialLinearTwoFiveCharacterRow) : ℂ :=
  ∑ c : SpecialLinearTwoFiveConjugacyClass,
    (specialLinearTwoFiveConjugacyClassSize c : ℂ) *
      specialLinearTwoFiveReducedCharacterTableValue t r c *
        specialLinearTwoFiveReducedCharacterTableValue t s c

theorem specialLinearTwoFiveCharacterTableWeightedPairing_eq_reduced
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (r s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveCharacterTableWeightedPairing t r s =
      specialLinearTwoFiveReducedCharacterTableWeightedPairing t r s := by
  unfold specialLinearTwoFiveCharacterTableWeightedPairing
  unfold specialLinearTwoFiveReducedCharacterTableWeightedPairing
  apply Finset.sum_congr rfl
  intro c _
  rw [specialLinearTwoFiveCharacterTableValue_eq_reduced t ht r c,
    specialLinearTwoFiveCharacterTableValue_eq_reduced t ht s c]

private theorem reducedPairing_trivial
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing
        t .trivial s =
      if .trivial = s then 120 else 0 := by
  rcases s with _ | k | k | _ | _ | _ | _
  all_goals try fin_cases k
  all_goals
    simp [specialLinearTwoFiveReducedCharacterTableWeightedPairing,
      specialLinearTwoFiveReducedCharacterTableValue,
      specialLinearTwoFiveConjugacyClassSize,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralGoldenRootChoice,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralReducedTensorValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      Fin.sum_univ_succ] <;>
    ring

private theorem reducedPairing_faithful_zero
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing
        t (.faithful 0) s =
      if .faithful 0 = s then 120 else 0 := by
  rcases s with _ | k | k | _ | _ | _ | _
  all_goals try fin_cases k
  all_goals
    simp [specialLinearTwoFiveReducedCharacterTableWeightedPairing,
      specialLinearTwoFiveReducedCharacterTableValue,
      specialLinearTwoFiveConjugacyClassSize,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralGoldenRootChoice,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralReducedTensorValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      Fin.sum_univ_succ] <;>
    ring_nf
  all_goals
    try rw [ht]
    ring

private theorem reducedPairing_faithful_one
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing
        t (.faithful 1) s =
      if .faithful 1 = s then 120 else 0 := by
  rcases s with _ | k | k | _ | _ | _ | _
  all_goals try fin_cases k
  all_goals
    simp [specialLinearTwoFiveReducedCharacterTableWeightedPairing,
      specialLinearTwoFiveReducedCharacterTableValue,
      specialLinearTwoFiveConjugacyClassSize,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralGoldenRootChoice,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralReducedTensorValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      Fin.sum_univ_succ] <;>
    ring_nf
  all_goals
    try rw [ht]
    ring

private theorem reducedPairing_symmetricSquare_zero
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing
        t (.symmetricSquare 0) s =
      if .symmetricSquare 0 = s then 120 else 0 := by
  rcases s with _ | k | k | _ | _ | _ | _
  all_goals try fin_cases k
  all_goals
    simp [specialLinearTwoFiveReducedCharacterTableWeightedPairing,
      specialLinearTwoFiveReducedCharacterTableValue,
      specialLinearTwoFiveConjugacyClassSize,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralGoldenRootChoice,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralReducedTensorValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      Fin.sum_univ_succ] <;>
    ring_nf
  all_goals
    try rw [ht]
    ring

private theorem reducedPairing_symmetricSquare_one
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing
        t (.symmetricSquare 1) s =
      if .symmetricSquare 1 = s then 120 else 0 := by
  rcases s with _ | k | k | _ | _ | _ | _
  all_goals try fin_cases k
  all_goals
    simp [specialLinearTwoFiveReducedCharacterTableWeightedPairing,
      specialLinearTwoFiveReducedCharacterTableValue,
      specialLinearTwoFiveConjugacyClassSize,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralGoldenRootChoice,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralReducedTensorValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      Fin.sum_univ_succ] <;>
    ring_nf
  all_goals
    try rw [ht]
    ring

private theorem reducedPairing_symmetricCube
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing
        t .symmetricCube s =
      if .symmetricCube = s then 120 else 0 := by
  rcases s with _ | k | k | _ | _ | _ | _
  all_goals try fin_cases k
  all_goals
    simp [specialLinearTwoFiveReducedCharacterTableWeightedPairing,
      specialLinearTwoFiveReducedCharacterTableValue,
      specialLinearTwoFiveConjugacyClassSize,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralGoldenRootChoice,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralReducedTensorValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      Fin.sum_univ_succ] <;>
    ring

private theorem reducedPairing_tensor
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing
        t .tensor s =
      if .tensor = s then 120 else 0 := by
  rcases s with _ | k | k | _ | _ | _ | _
  all_goals try fin_cases k
  all_goals
    simp [specialLinearTwoFiveReducedCharacterTableWeightedPairing,
      specialLinearTwoFiveReducedCharacterTableValue,
      specialLinearTwoFiveConjugacyClassSize,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralGoldenRootChoice,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralReducedTensorValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      Fin.sum_univ_succ] <;>
    ring

private theorem reducedPairing_symmetricFourthPower
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing
        t .symmetricFourthPower s =
      if .symmetricFourthPower = s then 120 else 0 := by
  rcases s with _ | k | k | _ | _ | _ | _
  all_goals try fin_cases k
  all_goals
    simp [specialLinearTwoFiveReducedCharacterTableWeightedPairing,
      specialLinearTwoFiveReducedCharacterTableValue,
      specialLinearTwoFiveConjugacyClassSize,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralGoldenRootChoice,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralReducedTensorValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      Fin.sum_univ_succ] <;>
    ring

private theorem reducedPairing_symmetricFifthPower
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing
        t .symmetricFifthPower s =
      if .symmetricFifthPower = s then 120 else 0 := by
  rcases s with _ | k | k | _ | _ | _ | _
  all_goals try fin_cases k
  all_goals
    simp [specialLinearTwoFiveReducedCharacterTableWeightedPairing,
      specialLinearTwoFiveReducedCharacterTableValue,
      specialLinearTwoFiveConjugacyClassSize,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralGoldenRootChoice,
      binaryIcosahedralReducedSymmetricSquareValue,
      binaryIcosahedralReducedSymmetricCubeValue,
      binaryIcosahedralReducedTensorValue,
      binaryIcosahedralReducedSymmetricFourthPowerValue,
      binaryIcosahedralReducedSymmetricFifthPowerValue,
      Fin.sum_univ_succ] <;>
    ring

/-- The nine symbolic rows are pairwise orthogonal and each has squared
norm `120` before normalization by the group order. -/
theorem specialLinearTwoFiveReducedCharacterTableWeightedPairing_eq
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (r s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveReducedCharacterTableWeightedPairing t r s =
      if r = s then 120 else 0 := by
  rcases r with _ | k | k | _ | _ | _ | _
  · exact reducedPairing_trivial t ht s
  · fin_cases k
    · exact reducedPairing_faithful_zero t ht s
    · exact reducedPairing_faithful_one t ht s
  · fin_cases k
    · exact reducedPairing_symmetricSquare_zero t ht s
    · exact reducedPairing_symmetricSquare_one t ht s
  · exact reducedPairing_symmetricCube t ht s
  · exact reducedPairing_tensor t ht s
  · exact reducedPairing_symmetricFourthPower t ht s
  · exact reducedPairing_symmetricFifthPower t ht s

/-- Orthogonality in the original symmetric-power formulas. -/
theorem specialLinearTwoFiveCharacterTableWeightedPairing_eq
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (r s : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveCharacterTableWeightedPairing t r s =
      if r = s then 120 else 0 := by
  rw [specialLinearTwoFiveCharacterTableWeightedPairing_eq_reduced
    t ht r s]
  exact
    specialLinearTwoFiveReducedCharacterTableWeightedPairing_eq
      t ht r s

end InductiveMcKay
end McKayConjecture
