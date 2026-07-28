/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyChecks25

/-!
# Checked sixfold-cover conjugacy data, states 260–269

Each theorem below is a kernel-checked finite computation against the coordinate group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Class-label invariance under `a`, state 260. -/
theorem alternatingSixSchurClassIndex_conjugateA_state260 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 260. -/
theorem alternatingSixSchurClassIndex_conjugateB_state260 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 260. -/
theorem alternatingSixSchurOrbitMiddle_state260 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 260. -/
theorem alternatingSixSchurClassConjugatorInverse_state260 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 260. -/
theorem alternatingSixSchurInverseFactor_state260 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 260. -/
theorem alternatingSixSchurOrbitPenultimate_state260 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 260. -/
theorem alternatingSixSchurOrbitFinish_state260 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 260, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 261. -/
theorem alternatingSixSchurClassIndex_conjugateA_state261 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 261. -/
theorem alternatingSixSchurClassIndex_conjugateB_state261 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 261. -/
theorem alternatingSixSchurOrbitMiddle_state261 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 261. -/
theorem alternatingSixSchurClassConjugatorInverse_state261 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 261. -/
theorem alternatingSixSchurInverseFactor_state261 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 261. -/
theorem alternatingSixSchurOrbitPenultimate_state261 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 261. -/
theorem alternatingSixSchurOrbitFinish_state261 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 261, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 262. -/
theorem alternatingSixSchurClassIndex_conjugateA_state262 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 262. -/
theorem alternatingSixSchurClassIndex_conjugateB_state262 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 262. -/
theorem alternatingSixSchurOrbitMiddle_state262 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 262. -/
theorem alternatingSixSchurClassConjugatorInverse_state262 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 262. -/
theorem alternatingSixSchurInverseFactor_state262 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 262. -/
theorem alternatingSixSchurOrbitPenultimate_state262 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 262. -/
theorem alternatingSixSchurOrbitFinish_state262 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 262, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 263. -/
theorem alternatingSixSchurClassIndex_conjugateA_state263 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 263. -/
theorem alternatingSixSchurClassIndex_conjugateB_state263 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 263. -/
theorem alternatingSixSchurOrbitMiddle_state263 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 263. -/
theorem alternatingSixSchurClassConjugatorInverse_state263 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 263. -/
theorem alternatingSixSchurInverseFactor_state263 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 263. -/
theorem alternatingSixSchurOrbitPenultimate_state263 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 263. -/
theorem alternatingSixSchurOrbitFinish_state263 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 263, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 264. -/
theorem alternatingSixSchurClassIndex_conjugateA_state264 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 264. -/
theorem alternatingSixSchurClassIndex_conjugateB_state264 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 264. -/
theorem alternatingSixSchurOrbitMiddle_state264 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 264. -/
theorem alternatingSixSchurClassConjugatorInverse_state264 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 264. -/
theorem alternatingSixSchurInverseFactor_state264 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 264. -/
theorem alternatingSixSchurOrbitPenultimate_state264 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 264. -/
theorem alternatingSixSchurOrbitFinish_state264 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 264, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 265. -/
theorem alternatingSixSchurClassIndex_conjugateA_state265 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 265. -/
theorem alternatingSixSchurClassIndex_conjugateB_state265 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 265. -/
theorem alternatingSixSchurOrbitMiddle_state265 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 265. -/
theorem alternatingSixSchurClassConjugatorInverse_state265 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 265. -/
theorem alternatingSixSchurInverseFactor_state265 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 265. -/
theorem alternatingSixSchurOrbitPenultimate_state265 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 265. -/
theorem alternatingSixSchurOrbitFinish_state265 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 265, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 266. -/
theorem alternatingSixSchurClassIndex_conjugateA_state266 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 266. -/
theorem alternatingSixSchurClassIndex_conjugateB_state266 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 266. -/
theorem alternatingSixSchurOrbitMiddle_state266 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 266. -/
theorem alternatingSixSchurClassConjugatorInverse_state266 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 266. -/
theorem alternatingSixSchurInverseFactor_state266 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 266. -/
theorem alternatingSixSchurOrbitPenultimate_state266 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 266. -/
theorem alternatingSixSchurOrbitFinish_state266 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 266, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 267. -/
theorem alternatingSixSchurClassIndex_conjugateA_state267 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 267. -/
theorem alternatingSixSchurClassIndex_conjugateB_state267 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 267. -/
theorem alternatingSixSchurOrbitMiddle_state267 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 267. -/
theorem alternatingSixSchurClassConjugatorInverse_state267 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 267. -/
theorem alternatingSixSchurInverseFactor_state267 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 267. -/
theorem alternatingSixSchurOrbitPenultimate_state267 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 267. -/
theorem alternatingSixSchurOrbitFinish_state267 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 267, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 268. -/
theorem alternatingSixSchurClassIndex_conjugateA_state268 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 268. -/
theorem alternatingSixSchurClassIndex_conjugateB_state268 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 268. -/
theorem alternatingSixSchurOrbitMiddle_state268 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 268. -/
theorem alternatingSixSchurClassConjugatorInverse_state268 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 268. -/
theorem alternatingSixSchurInverseFactor_state268 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 268. -/
theorem alternatingSixSchurOrbitPenultimate_state268 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 268. -/
theorem alternatingSixSchurOrbitFinish_state268 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 268, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 269. -/
theorem alternatingSixSchurClassIndex_conjugateA_state269 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 269. -/
theorem alternatingSixSchurClassIndex_conjugateB_state269 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 269. -/
theorem alternatingSixSchurOrbitMiddle_state269 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 269. -/
theorem alternatingSixSchurClassConjugatorInverse_state269 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 269. -/
theorem alternatingSixSchurInverseFactor_state269 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 269. -/
theorem alternatingSixSchurOrbitPenultimate_state269 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 269. -/
theorem alternatingSixSchurOrbitFinish_state269 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 269, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide


end GroupTheory
end McKayConjecture
