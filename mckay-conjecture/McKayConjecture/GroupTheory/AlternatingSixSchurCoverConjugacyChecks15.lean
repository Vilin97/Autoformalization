/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyChecks14

/-!
# Checked sixfold-cover conjugacy data, states 150–159

Each theorem below is a kernel-checked finite computation against the coordinate group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Class-label invariance under `a`, state 150. -/
theorem alternatingSixSchurClassIndex_conjugateA_state150 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 150. -/
theorem alternatingSixSchurClassIndex_conjugateB_state150 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 150. -/
theorem alternatingSixSchurOrbitMiddle_state150 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 150. -/
theorem alternatingSixSchurClassConjugatorInverse_state150 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 150. -/
theorem alternatingSixSchurInverseFactor_state150 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 150. -/
theorem alternatingSixSchurOrbitPenultimate_state150 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 150. -/
theorem alternatingSixSchurOrbitFinish_state150 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 150, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 151. -/
theorem alternatingSixSchurClassIndex_conjugateA_state151 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 151. -/
theorem alternatingSixSchurClassIndex_conjugateB_state151 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 151. -/
theorem alternatingSixSchurOrbitMiddle_state151 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 151. -/
theorem alternatingSixSchurClassConjugatorInverse_state151 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 151. -/
theorem alternatingSixSchurInverseFactor_state151 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 151. -/
theorem alternatingSixSchurOrbitPenultimate_state151 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 151. -/
theorem alternatingSixSchurOrbitFinish_state151 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 151, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 152. -/
theorem alternatingSixSchurClassIndex_conjugateA_state152 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 152. -/
theorem alternatingSixSchurClassIndex_conjugateB_state152 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 152. -/
theorem alternatingSixSchurOrbitMiddle_state152 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 152. -/
theorem alternatingSixSchurClassConjugatorInverse_state152 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 152. -/
theorem alternatingSixSchurInverseFactor_state152 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 152. -/
theorem alternatingSixSchurOrbitPenultimate_state152 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 152. -/
theorem alternatingSixSchurOrbitFinish_state152 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 152, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 153. -/
theorem alternatingSixSchurClassIndex_conjugateA_state153 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 153. -/
theorem alternatingSixSchurClassIndex_conjugateB_state153 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 153. -/
theorem alternatingSixSchurOrbitMiddle_state153 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 153. -/
theorem alternatingSixSchurClassConjugatorInverse_state153 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 153. -/
theorem alternatingSixSchurInverseFactor_state153 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 153. -/
theorem alternatingSixSchurOrbitPenultimate_state153 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 153. -/
theorem alternatingSixSchurOrbitFinish_state153 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 153, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 154. -/
theorem alternatingSixSchurClassIndex_conjugateA_state154 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 154. -/
theorem alternatingSixSchurClassIndex_conjugateB_state154 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 154. -/
theorem alternatingSixSchurOrbitMiddle_state154 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 154. -/
theorem alternatingSixSchurClassConjugatorInverse_state154 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 154. -/
theorem alternatingSixSchurInverseFactor_state154 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 154. -/
theorem alternatingSixSchurOrbitPenultimate_state154 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 154. -/
theorem alternatingSixSchurOrbitFinish_state154 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 154, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 155. -/
theorem alternatingSixSchurClassIndex_conjugateA_state155 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 155. -/
theorem alternatingSixSchurClassIndex_conjugateB_state155 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 155. -/
theorem alternatingSixSchurOrbitMiddle_state155 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 155. -/
theorem alternatingSixSchurClassConjugatorInverse_state155 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 155. -/
theorem alternatingSixSchurInverseFactor_state155 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 155. -/
theorem alternatingSixSchurOrbitPenultimate_state155 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 155. -/
theorem alternatingSixSchurOrbitFinish_state155 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 155, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 156. -/
theorem alternatingSixSchurClassIndex_conjugateA_state156 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 156. -/
theorem alternatingSixSchurClassIndex_conjugateB_state156 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 156. -/
theorem alternatingSixSchurOrbitMiddle_state156 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 156. -/
theorem alternatingSixSchurClassConjugatorInverse_state156 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 156. -/
theorem alternatingSixSchurInverseFactor_state156 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 156. -/
theorem alternatingSixSchurOrbitPenultimate_state156 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 156. -/
theorem alternatingSixSchurOrbitFinish_state156 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 156, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 157. -/
theorem alternatingSixSchurClassIndex_conjugateA_state157 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 157. -/
theorem alternatingSixSchurClassIndex_conjugateB_state157 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 157. -/
theorem alternatingSixSchurOrbitMiddle_state157 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 157. -/
theorem alternatingSixSchurClassConjugatorInverse_state157 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 157. -/
theorem alternatingSixSchurInverseFactor_state157 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 157. -/
theorem alternatingSixSchurOrbitPenultimate_state157 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 157. -/
theorem alternatingSixSchurOrbitFinish_state157 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 157, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 158. -/
theorem alternatingSixSchurClassIndex_conjugateA_state158 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 158. -/
theorem alternatingSixSchurClassIndex_conjugateB_state158 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 158. -/
theorem alternatingSixSchurOrbitMiddle_state158 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 158. -/
theorem alternatingSixSchurClassConjugatorInverse_state158 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 158. -/
theorem alternatingSixSchurInverseFactor_state158 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 158. -/
theorem alternatingSixSchurOrbitPenultimate_state158 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 158. -/
theorem alternatingSixSchurOrbitFinish_state158 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 158, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `a`, state 159. -/
theorem alternatingSixSchurClassIndex_conjugateA_state159 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA *
          ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Class-label invariance under `b`, state 159. -/
theorem alternatingSixSchurClassIndex_conjugateB_state159 (central : Fin 6) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB *
          ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- First orbit-witness multiplication above state 159. -/
theorem alternatingSixSchurOrbitMiddle_state159 (central : Fin 6) :
    alternatingSixSchurClassConjugator ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates)) =
      alternatingSixSchurOrbitMiddle ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Conjugator inversion above state 159. -/
theorem alternatingSixSchurClassConjugatorInverse_state159 (central : Fin 6) :
    (alternatingSixSchurClassConjugator ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates))⁻¹ =
      alternatingSixSchurClassConjugatorInverse ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Short inverse factorization above state 159. -/
theorem alternatingSixSchurInverseFactor_state159 (central : Fin 6) :
    alternatingSixSchurInverseFactorLeft ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurClassConjugatorInverse ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Penultimate orbit multiplication above state 159. -/
theorem alternatingSixSchurOrbitPenultimate_state159 (central : Fin 6) :
    alternatingSixSchurOrbitMiddle ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorLeft ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      alternatingSixSchurOrbitPenultimate ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide

/-- Final orbit-witness multiplication above state 159. -/
theorem alternatingSixSchurOrbitFinish_state159 (central : Fin 6) :
    alternatingSixSchurOrbitPenultimate ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) *
        alternatingSixSchurInverseFactorRight ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) =
      ({ state := 159, central := (ZMod.finEquiv 6) central } : AlternatingSixSchurCoordinates) := by
  fin_cases central <;> decide


end GroupTheory
end McKayConjecture
