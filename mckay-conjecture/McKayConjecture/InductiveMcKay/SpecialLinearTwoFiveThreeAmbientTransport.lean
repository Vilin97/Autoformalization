/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.SpecialLinearTwoSymmetricPowers
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalForm
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveConjugacyClasses
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeAmbientRepresentations

/-!
# Transporting the binary-icosahedral representations to `SL(2, 𝔽₅)`

The exact binary-icosahedral presentation equivalence transports the two
quaternionic matrix models to the concrete finite matrix group.  This file
also records their nine-row trace table, which is the common input to all
low symmetric-power character calculations.
-/

noncomputable section

open CategoryTheory Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- A faithful complex representation of the concrete binary icosahedral
group, parameterized by a root of `T² - T - 1`. -/
def specialLinearTwoFiveComplexHom
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    SpecialLinearTwoFive →* SL(2, ℂ) :=
  (binaryIcosahedralPresentedComplexHom t ht).comp
    binaryIcosahedralPresentedGroupEquivSpecialLinearTwoFive.symm.toMonoidHom

/-- Transport commutes with evaluation on a presented word. -/
@[simp]
theorem specialLinearTwoFiveComplexHom_presentationTo
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (g : BinaryIcosahedralPresentedGroup) :
    specialLinearTwoFiveComplexHom t ht
        (binaryIcosahedralPresentationToSpecialLinearTwoFive g) =
      binaryIcosahedralPresentedComplexHom t ht g := by
  change
    binaryIcosahedralPresentedComplexHom t ht
        (binaryIcosahedralPresentedGroupEquivSpecialLinearTwoFive.symm
          (binaryIcosahedralPresentedGroupEquivSpecialLinearTwoFive g)) =
      _
  rw [MulEquiv.symm_apply_apply]

@[simp]
theorem specialLinearTwoFiveComplexHom_x
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    specialLinearTwoFiveComplexHom t ht
        specialLinearTwoFivePresentationX =
      binaryIcosahedralComplexASL *
        binaryIcosahedralComplexBSL t ht := by
  rw [← binaryIcosahedralPresentationToSpecialLinearTwoFive_x,
    specialLinearTwoFiveComplexHom_presentationTo,
    binaryIcosahedralPresentedComplexHom_x]

@[simp]
theorem specialLinearTwoFiveComplexHom_y
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    specialLinearTwoFiveComplexHom t ht
        specialLinearTwoFivePresentationY =
      binaryIcosahedralComplexASL := by
  rw [← binaryIcosahedralPresentationToSpecialLinearTwoFive_y,
    specialLinearTwoFiveComplexHom_presentationTo,
    binaryIcosahedralPresentedComplexHom_y]

theorem binaryIcosahedralPresentationToSpecialLinearTwoFive_z :
    binaryIcosahedralPresentationToSpecialLinearTwoFive
        binaryIcosahedralPresentedZ =
      specialLinearTwoFivePresentationZ := by
  simp [binaryIcosahedralPresentationToSpecialLinearTwoFive,
    binaryIcosahedralPresentedZ,
    specialLinearTwoFivePresentationGenerator]

@[simp]
theorem specialLinearTwoFiveComplexHom_z
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    specialLinearTwoFiveComplexHom t ht
        specialLinearTwoFivePresentationZ =
      binaryIcosahedralComplexBSL t ht := by
  rw [← binaryIcosahedralPresentationToSpecialLinearTwoFive_z,
    specialLinearTwoFiveComplexHom_presentationTo,
    binaryIcosahedralPresentedComplexHom_z]

/-- Trace of the defining row at the nine certified conjugacy-class
representatives. -/
theorem specialLinearTwoFiveComplexHom_trace_representative
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    Matrix.trace
        (specialLinearTwoFiveComplexHom t ht
            (specialLinearTwoFiveConjugacyRepresentative c) :
          Matrix (Fin 2) (Fin 2) ℂ) =
      ![2, -2, 0, 1, -1, t, 1 - t, t - 1, -t] c := by
  fin_cases c
  · change
      Matrix.trace
          (specialLinearTwoFiveComplexHom t ht 1 :
            Matrix (Fin 2) (Fin 2) ℂ) =
        2
    simp
  · have hcentral :
        (-1 : SpecialLinearTwoFive) =
          specialLinearTwoFivePresentationY ^ 3 := by
      decide
    change
      Matrix.trace
          (specialLinearTwoFiveComplexHom t ht (-1) :
            Matrix (Fin 2) (Fin 2) ℂ) =
        -2
    rw [hcentral, map_pow,
      specialLinearTwoFiveComplexHom_y]
    change
      Matrix.trace (binaryIcosahedralComplexA ^ 3) =
        -2
    rw [binaryIcosahedralComplexA_pow_three]
    simp [Matrix.trace_fin_two]
  · change
      Matrix.trace
          (specialLinearTwoFiveComplexHom t ht
              specialLinearTwoFivePresentationX :
            Matrix (Fin 2) (Fin 2) ℂ) =
        0
    rw [specialLinearTwoFiveComplexHom_x]
    change
      Matrix.trace
          (binaryIcosahedralComplexA *
            binaryIcosahedralComplexB t) =
        0
    exact binaryIcosahedralComplexAB_trace t
  · change
      Matrix.trace
          (specialLinearTwoFiveComplexHom t ht
              specialLinearTwoFivePresentationY :
            Matrix (Fin 2) (Fin 2) ℂ) =
        1
    rw [specialLinearTwoFiveComplexHom_y]
    exact binaryIcosahedralComplexA_trace
  · change
      Matrix.trace
          (specialLinearTwoFiveComplexHom t ht
              (specialLinearTwoFivePresentationY ^ 2) :
            Matrix (Fin 2) (Fin 2) ℂ) =
        -1
    rw [map_pow, specialLinearTwoFiveComplexHom_y]
    change
      Matrix.trace (binaryIcosahedralComplexA ^ 2) =
        -1
    rw [trace_pow_two_of_det_one
      binaryIcosahedralComplexA
      binaryIcosahedralComplexA_det,
      binaryIcosahedralComplexA_trace]
    norm_num
  · change
      Matrix.trace
          (specialLinearTwoFiveComplexHom t ht
              specialLinearTwoFivePresentationZ :
            Matrix (Fin 2) (Fin 2) ℂ) =
        t
    rw [specialLinearTwoFiveComplexHom_z]
    exact binaryIcosahedralComplexB_trace t
  · change
      Matrix.trace
          (specialLinearTwoFiveComplexHom t ht
              (specialLinearTwoFivePresentationZ ^ 3) :
            Matrix (Fin 2) (Fin 2) ℂ) =
        1 - t
    rw [map_pow, specialLinearTwoFiveComplexHom_z]
    change
      Matrix.trace (binaryIcosahedralComplexB t ^ 3) =
        1 - t
    rw [trace_pow_three_of_det_one
      (binaryIcosahedralComplexB t)
      (binaryIcosahedralComplexB_det t ht),
      binaryIcosahedralComplexB_trace]
    linear_combination (t + 1) * ht
  · change
      Matrix.trace
          (specialLinearTwoFiveComplexHom t ht
              (specialLinearTwoFivePresentationZ ^ 2) :
            Matrix (Fin 2) (Fin 2) ℂ) =
        t - 1
    rw [map_pow, specialLinearTwoFiveComplexHom_z]
    change
      Matrix.trace (binaryIcosahedralComplexB t ^ 2) =
        t - 1
    rw [trace_pow_two_of_det_one
      (binaryIcosahedralComplexB t)
      (binaryIcosahedralComplexB_det t ht),
      binaryIcosahedralComplexB_trace]
    linear_combination ht
  · change
      Matrix.trace
          (specialLinearTwoFiveComplexHom t ht
              (specialLinearTwoFivePresentationZ ^ 4) :
            Matrix (Fin 2) (Fin 2) ℂ) =
        -t
    rw [map_pow, specialLinearTwoFiveComplexHom_z]
    change
      Matrix.trace (binaryIcosahedralComplexB t ^ 4) =
        -t
    rw [trace_pow_four_of_det_one
      (binaryIcosahedralComplexB t)
      (binaryIcosahedralComplexB_det t ht),
      binaryIcosahedralComplexB_trace]
    linear_combination (t ^ 2 + t - 2) * ht

/-- The positive-root faithful embedding. -/
abbrev specialLinearTwoFiveComplexHomPlus :
    SpecialLinearTwoFive →* SL(2, ℂ) :=
  specialLinearTwoFiveComplexHom
    binaryIcosahedralGoldenRootPlus
    binaryIcosahedralGoldenRootPlus_sq

/-- The Galois-conjugate faithful embedding. -/
abbrev specialLinearTwoFiveComplexHomMinus :
    SpecialLinearTwoFive →* SL(2, ℂ) :=
  specialLinearTwoFiveComplexHom
    binaryIcosahedralGoldenRootMinus
    binaryIcosahedralGoldenRootMinus_sq

end InductiveMcKay
end McKayConjecture
