/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyChecks01

/-!
# Checked sixfold-cover conjugacy data, states 20–29

Each theorem below is a kernel-checked finite computation against the coordinate group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Class-label invariance under `a`, state 20. -/
theorem alternatingSixSchurClassIndex_conjugateA_state020 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 20. -/
theorem alternatingSixSchurClassIndex_conjugateB_state020 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 20. -/
theorem alternatingSixSchurOrbitMiddle_state020 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 20. -/
theorem alternatingSixSchurClassConjugatorInverse_state020 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 20. -/
theorem alternatingSixSchurInverseFactor_state020 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 20. -/
theorem alternatingSixSchurOrbitPenultimate_state020 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 20. -/
theorem alternatingSixSchurOrbitFinish_state020 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 20, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 21. -/
theorem alternatingSixSchurClassIndex_conjugateA_state021 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 21. -/
theorem alternatingSixSchurClassIndex_conjugateB_state021 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 21. -/
theorem alternatingSixSchurOrbitMiddle_state021 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 21. -/
theorem alternatingSixSchurClassConjugatorInverse_state021 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 21. -/
theorem alternatingSixSchurInverseFactor_state021 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 21. -/
theorem alternatingSixSchurOrbitPenultimate_state021 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 21. -/
theorem alternatingSixSchurOrbitFinish_state021 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 21, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 22. -/
theorem alternatingSixSchurClassIndex_conjugateA_state022 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 22. -/
theorem alternatingSixSchurClassIndex_conjugateB_state022 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 22. -/
theorem alternatingSixSchurOrbitMiddle_state022 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 22. -/
theorem alternatingSixSchurClassConjugatorInverse_state022 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 22. -/
theorem alternatingSixSchurInverseFactor_state022 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 22. -/
theorem alternatingSixSchurOrbitPenultimate_state022 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 22. -/
theorem alternatingSixSchurOrbitFinish_state022 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 22, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 23. -/
theorem alternatingSixSchurClassIndex_conjugateA_state023 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 23. -/
theorem alternatingSixSchurClassIndex_conjugateB_state023 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 23. -/
theorem alternatingSixSchurOrbitMiddle_state023 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 23. -/
theorem alternatingSixSchurClassConjugatorInverse_state023 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 23. -/
theorem alternatingSixSchurInverseFactor_state023 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 23. -/
theorem alternatingSixSchurOrbitPenultimate_state023 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 23. -/
theorem alternatingSixSchurOrbitFinish_state023 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 23, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 24. -/
theorem alternatingSixSchurClassIndex_conjugateA_state024 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 24. -/
theorem alternatingSixSchurClassIndex_conjugateB_state024 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 24. -/
theorem alternatingSixSchurOrbitMiddle_state024 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 24. -/
theorem alternatingSixSchurClassConjugatorInverse_state024 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 24. -/
theorem alternatingSixSchurInverseFactor_state024 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 24. -/
theorem alternatingSixSchurOrbitPenultimate_state024 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 24. -/
theorem alternatingSixSchurOrbitFinish_state024 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 24, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 25. -/
theorem alternatingSixSchurClassIndex_conjugateA_state025 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 25. -/
theorem alternatingSixSchurClassIndex_conjugateB_state025 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 25. -/
theorem alternatingSixSchurOrbitMiddle_state025 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 25. -/
theorem alternatingSixSchurClassConjugatorInverse_state025 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 25. -/
theorem alternatingSixSchurInverseFactor_state025 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 25. -/
theorem alternatingSixSchurOrbitPenultimate_state025 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 25. -/
theorem alternatingSixSchurOrbitFinish_state025 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 25, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 26. -/
theorem alternatingSixSchurClassIndex_conjugateA_state026 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 26. -/
theorem alternatingSixSchurClassIndex_conjugateB_state026 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 26. -/
theorem alternatingSixSchurOrbitMiddle_state026 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 26. -/
theorem alternatingSixSchurClassConjugatorInverse_state026 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 26. -/
theorem alternatingSixSchurInverseFactor_state026 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 26. -/
theorem alternatingSixSchurOrbitPenultimate_state026 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 26. -/
theorem alternatingSixSchurOrbitFinish_state026 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 26, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 27. -/
theorem alternatingSixSchurClassIndex_conjugateA_state027 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 27. -/
theorem alternatingSixSchurClassIndex_conjugateB_state027 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 27. -/
theorem alternatingSixSchurOrbitMiddle_state027 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 27. -/
theorem alternatingSixSchurClassConjugatorInverse_state027 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 27. -/
theorem alternatingSixSchurInverseFactor_state027 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 27. -/
theorem alternatingSixSchurOrbitPenultimate_state027 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 27. -/
theorem alternatingSixSchurOrbitFinish_state027 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 27, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 28. -/
theorem alternatingSixSchurClassIndex_conjugateA_state028 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 28. -/
theorem alternatingSixSchurClassIndex_conjugateB_state028 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 28. -/
theorem alternatingSixSchurOrbitMiddle_state028 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 28. -/
theorem alternatingSixSchurClassConjugatorInverse_state028 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 28. -/
theorem alternatingSixSchurInverseFactor_state028 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 28. -/
theorem alternatingSixSchurOrbitPenultimate_state028 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 28. -/
theorem alternatingSixSchurOrbitFinish_state028 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 28, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 29. -/
theorem alternatingSixSchurClassIndex_conjugateA_state029 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 29. -/
theorem alternatingSixSchurClassIndex_conjugateB_state029 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 29. -/
theorem alternatingSixSchurOrbitMiddle_state029 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 29. -/
theorem alternatingSixSchurClassConjugatorInverse_state029 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 29. -/
theorem alternatingSixSchurInverseFactor_state029 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 29. -/
theorem alternatingSixSchurOrbitPenultimate_state029 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 29. -/
theorem alternatingSixSchurOrbitFinish_state029 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 29, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide


end GroupTheory
end McKayConjecture
