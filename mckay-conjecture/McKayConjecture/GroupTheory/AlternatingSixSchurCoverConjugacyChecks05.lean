/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyChecks04

/-!
# Checked sixfold-cover conjugacy data, states 50–59

Each theorem below is a kernel-checked finite computation against the coordinate group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Class-label invariance under `a`, state 50. -/
theorem alternatingSixSchurClassIndex_conjugateA_state050 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 50. -/
theorem alternatingSixSchurClassIndex_conjugateB_state050 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 50. -/
theorem alternatingSixSchurOrbitMiddle_state050 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 50. -/
theorem alternatingSixSchurClassConjugatorInverse_state050 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 50. -/
theorem alternatingSixSchurInverseFactor_state050 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 50. -/
theorem alternatingSixSchurOrbitPenultimate_state050 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 50. -/
theorem alternatingSixSchurOrbitFinish_state050 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 50, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 51. -/
theorem alternatingSixSchurClassIndex_conjugateA_state051 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 51. -/
theorem alternatingSixSchurClassIndex_conjugateB_state051 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 51. -/
theorem alternatingSixSchurOrbitMiddle_state051 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 51. -/
theorem alternatingSixSchurClassConjugatorInverse_state051 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 51. -/
theorem alternatingSixSchurInverseFactor_state051 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 51. -/
theorem alternatingSixSchurOrbitPenultimate_state051 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 51. -/
theorem alternatingSixSchurOrbitFinish_state051 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 51, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 52. -/
theorem alternatingSixSchurClassIndex_conjugateA_state052 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 52. -/
theorem alternatingSixSchurClassIndex_conjugateB_state052 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 52. -/
theorem alternatingSixSchurOrbitMiddle_state052 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 52. -/
theorem alternatingSixSchurClassConjugatorInverse_state052 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 52. -/
theorem alternatingSixSchurInverseFactor_state052 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 52. -/
theorem alternatingSixSchurOrbitPenultimate_state052 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 52. -/
theorem alternatingSixSchurOrbitFinish_state052 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 52, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 53. -/
theorem alternatingSixSchurClassIndex_conjugateA_state053 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 53. -/
theorem alternatingSixSchurClassIndex_conjugateB_state053 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 53. -/
theorem alternatingSixSchurOrbitMiddle_state053 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 53. -/
theorem alternatingSixSchurClassConjugatorInverse_state053 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 53. -/
theorem alternatingSixSchurInverseFactor_state053 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 53. -/
theorem alternatingSixSchurOrbitPenultimate_state053 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 53. -/
theorem alternatingSixSchurOrbitFinish_state053 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 53, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 54. -/
theorem alternatingSixSchurClassIndex_conjugateA_state054 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 54. -/
theorem alternatingSixSchurClassIndex_conjugateB_state054 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 54. -/
theorem alternatingSixSchurOrbitMiddle_state054 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 54. -/
theorem alternatingSixSchurClassConjugatorInverse_state054 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 54. -/
theorem alternatingSixSchurInverseFactor_state054 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 54. -/
theorem alternatingSixSchurOrbitPenultimate_state054 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 54. -/
theorem alternatingSixSchurOrbitFinish_state054 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 54, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 55. -/
theorem alternatingSixSchurClassIndex_conjugateA_state055 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 55. -/
theorem alternatingSixSchurClassIndex_conjugateB_state055 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 55. -/
theorem alternatingSixSchurOrbitMiddle_state055 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 55. -/
theorem alternatingSixSchurClassConjugatorInverse_state055 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 55. -/
theorem alternatingSixSchurInverseFactor_state055 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 55. -/
theorem alternatingSixSchurOrbitPenultimate_state055 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 55. -/
theorem alternatingSixSchurOrbitFinish_state055 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 55, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 56. -/
theorem alternatingSixSchurClassIndex_conjugateA_state056 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 56. -/
theorem alternatingSixSchurClassIndex_conjugateB_state056 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 56. -/
theorem alternatingSixSchurOrbitMiddle_state056 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 56. -/
theorem alternatingSixSchurClassConjugatorInverse_state056 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 56. -/
theorem alternatingSixSchurInverseFactor_state056 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 56. -/
theorem alternatingSixSchurOrbitPenultimate_state056 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 56. -/
theorem alternatingSixSchurOrbitFinish_state056 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 56, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 57. -/
theorem alternatingSixSchurClassIndex_conjugateA_state057 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 57. -/
theorem alternatingSixSchurClassIndex_conjugateB_state057 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 57. -/
theorem alternatingSixSchurOrbitMiddle_state057 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 57. -/
theorem alternatingSixSchurClassConjugatorInverse_state057 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 57. -/
theorem alternatingSixSchurInverseFactor_state057 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 57. -/
theorem alternatingSixSchurOrbitPenultimate_state057 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 57. -/
theorem alternatingSixSchurOrbitFinish_state057 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 57, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 58. -/
theorem alternatingSixSchurClassIndex_conjugateA_state058 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 58. -/
theorem alternatingSixSchurClassIndex_conjugateB_state058 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 58. -/
theorem alternatingSixSchurOrbitMiddle_state058 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 58. -/
theorem alternatingSixSchurClassConjugatorInverse_state058 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 58. -/
theorem alternatingSixSchurInverseFactor_state058 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 58. -/
theorem alternatingSixSchurOrbitPenultimate_state058 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 58. -/
theorem alternatingSixSchurOrbitFinish_state058 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 58, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 59. -/
theorem alternatingSixSchurClassIndex_conjugateA_state059 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 59. -/
theorem alternatingSixSchurClassIndex_conjugateB_state059 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 59. -/
theorem alternatingSixSchurOrbitMiddle_state059 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 59. -/
theorem alternatingSixSchurClassConjugatorInverse_state059 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 59. -/
theorem alternatingSixSchurInverseFactor_state059 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 59. -/
theorem alternatingSixSchurOrbitPenultimate_state059 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 59. -/
theorem alternatingSixSchurOrbitFinish_state059 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 59, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide


end GroupTheory
end McKayConjecture
