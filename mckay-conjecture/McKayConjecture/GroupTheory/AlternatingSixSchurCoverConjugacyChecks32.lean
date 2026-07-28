/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyChecks31

/-!
# Checked sixfold-cover conjugacy data, states 320–329

Each theorem below is a kernel-checked finite computation against the coordinate group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Class-label invariance under `a`, state 320. -/
theorem alternatingSixSchurClassIndex_conjugateA_state320 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 320. -/
theorem alternatingSixSchurClassIndex_conjugateB_state320 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 320. -/
theorem alternatingSixSchurOrbitMiddle_state320 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 320. -/
theorem alternatingSixSchurClassConjugatorInverse_state320 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 320. -/
theorem alternatingSixSchurInverseFactor_state320 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 320. -/
theorem alternatingSixSchurOrbitPenultimate_state320 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 320. -/
theorem alternatingSixSchurOrbitFinish_state320 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 320, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 321. -/
theorem alternatingSixSchurClassIndex_conjugateA_state321 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 321. -/
theorem alternatingSixSchurClassIndex_conjugateB_state321 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 321. -/
theorem alternatingSixSchurOrbitMiddle_state321 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 321. -/
theorem alternatingSixSchurClassConjugatorInverse_state321 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 321. -/
theorem alternatingSixSchurInverseFactor_state321 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 321. -/
theorem alternatingSixSchurOrbitPenultimate_state321 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 321. -/
theorem alternatingSixSchurOrbitFinish_state321 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 321, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 322. -/
theorem alternatingSixSchurClassIndex_conjugateA_state322 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 322. -/
theorem alternatingSixSchurClassIndex_conjugateB_state322 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 322. -/
theorem alternatingSixSchurOrbitMiddle_state322 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 322. -/
theorem alternatingSixSchurClassConjugatorInverse_state322 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 322. -/
theorem alternatingSixSchurInverseFactor_state322 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 322. -/
theorem alternatingSixSchurOrbitPenultimate_state322 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 322. -/
theorem alternatingSixSchurOrbitFinish_state322 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 322, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 323. -/
theorem alternatingSixSchurClassIndex_conjugateA_state323 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 323. -/
theorem alternatingSixSchurClassIndex_conjugateB_state323 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 323. -/
theorem alternatingSixSchurOrbitMiddle_state323 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 323. -/
theorem alternatingSixSchurClassConjugatorInverse_state323 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 323. -/
theorem alternatingSixSchurInverseFactor_state323 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 323. -/
theorem alternatingSixSchurOrbitPenultimate_state323 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 323. -/
theorem alternatingSixSchurOrbitFinish_state323 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 323, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 324. -/
theorem alternatingSixSchurClassIndex_conjugateA_state324 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 324. -/
theorem alternatingSixSchurClassIndex_conjugateB_state324 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 324. -/
theorem alternatingSixSchurOrbitMiddle_state324 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 324. -/
theorem alternatingSixSchurClassConjugatorInverse_state324 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 324. -/
theorem alternatingSixSchurInverseFactor_state324 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 324. -/
theorem alternatingSixSchurOrbitPenultimate_state324 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 324. -/
theorem alternatingSixSchurOrbitFinish_state324 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 324, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 325. -/
theorem alternatingSixSchurClassIndex_conjugateA_state325 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 325. -/
theorem alternatingSixSchurClassIndex_conjugateB_state325 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 325. -/
theorem alternatingSixSchurOrbitMiddle_state325 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 325. -/
theorem alternatingSixSchurClassConjugatorInverse_state325 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 325. -/
theorem alternatingSixSchurInverseFactor_state325 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 325. -/
theorem alternatingSixSchurOrbitPenultimate_state325 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 325. -/
theorem alternatingSixSchurOrbitFinish_state325 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 325, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 326. -/
theorem alternatingSixSchurClassIndex_conjugateA_state326 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 326. -/
theorem alternatingSixSchurClassIndex_conjugateB_state326 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 326. -/
theorem alternatingSixSchurOrbitMiddle_state326 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 326. -/
theorem alternatingSixSchurClassConjugatorInverse_state326 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 326. -/
theorem alternatingSixSchurInverseFactor_state326 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 326. -/
theorem alternatingSixSchurOrbitPenultimate_state326 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 326. -/
theorem alternatingSixSchurOrbitFinish_state326 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 326, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 327. -/
theorem alternatingSixSchurClassIndex_conjugateA_state327 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 327. -/
theorem alternatingSixSchurClassIndex_conjugateB_state327 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 327. -/
theorem alternatingSixSchurOrbitMiddle_state327 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 327. -/
theorem alternatingSixSchurClassConjugatorInverse_state327 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 327. -/
theorem alternatingSixSchurInverseFactor_state327 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 327. -/
theorem alternatingSixSchurOrbitPenultimate_state327 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 327. -/
theorem alternatingSixSchurOrbitFinish_state327 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 327, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 328. -/
theorem alternatingSixSchurClassIndex_conjugateA_state328 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 328. -/
theorem alternatingSixSchurClassIndex_conjugateB_state328 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 328. -/
theorem alternatingSixSchurOrbitMiddle_state328 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 328. -/
theorem alternatingSixSchurClassConjugatorInverse_state328 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 328. -/
theorem alternatingSixSchurInverseFactor_state328 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 328. -/
theorem alternatingSixSchurOrbitPenultimate_state328 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 328. -/
theorem alternatingSixSchurOrbitFinish_state328 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 328, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 329. -/
theorem alternatingSixSchurClassIndex_conjugateA_state329 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 329. -/
theorem alternatingSixSchurClassIndex_conjugateB_state329 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 329. -/
theorem alternatingSixSchurOrbitMiddle_state329 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 329. -/
theorem alternatingSixSchurClassConjugatorInverse_state329 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 329. -/
theorem alternatingSixSchurInverseFactor_state329 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 329. -/
theorem alternatingSixSchurOrbitPenultimate_state329 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 329. -/
theorem alternatingSixSchurOrbitFinish_state329 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 329, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide


end GroupTheory
end McKayConjecture
