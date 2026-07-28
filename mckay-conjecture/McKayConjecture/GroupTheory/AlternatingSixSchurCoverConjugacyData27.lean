/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 270–279

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 270. -/
def alternatingSixSchurConjugacyDatumRow270 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 12, conjugatorState := 148, orbitMiddleState := 202, orbitMiddleCentral := 3, conjugatorInverseState := 120, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 182, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 148, orbitMiddleState := 202, orbitMiddleCentral := 4, conjugatorInverseState := 120, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 182, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 148, orbitMiddleState := 202, orbitMiddleCentral := 5, conjugatorInverseState := 120, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 182, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 148, orbitMiddleState := 202, orbitMiddleCentral := 0, conjugatorInverseState := 120, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 182, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 148, orbitMiddleState := 202, orbitMiddleCentral := 1, conjugatorInverseState := 120, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 182, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 148, orbitMiddleState := 202, orbitMiddleCentral := 2, conjugatorInverseState := 120, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 182, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 271. -/
def alternatingSixSchurConjugacyDatumRow271 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 52, orbitMiddleState := 228, orbitMiddleCentral := 3, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 224, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 52, orbitMiddleState := 228, orbitMiddleCentral := 4, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 224, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 208, orbitMiddleState := 351, orbitMiddleCentral := 1, conjugatorInverseState := 202, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 199, orbitPenultimateCentral := 5 },
    { classIndex := 28, conjugatorState := 208, orbitMiddleState := 351, orbitMiddleCentral := 2, conjugatorInverseState := 202, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 199, orbitPenultimateCentral := 0 },
    { classIndex := 27, conjugatorState := 38, orbitMiddleState := 253, orbitMiddleCentral := 4, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 238, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 38, orbitMiddleState := 253, orbitMiddleCentral := 5, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 238, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 272. -/
def alternatingSixSchurConjugacyDatumRow272 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 35, orbitMiddleState := 56, orbitMiddleCentral := 0, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 123, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 35, orbitMiddleState := 56, orbitMiddleCentral := 1, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 123, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 35, orbitMiddleState := 56, orbitMiddleCentral := 2, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 123, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 35, orbitMiddleState := 56, orbitMiddleCentral := 3, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 123, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 35, orbitMiddleState := 56, orbitMiddleCentral := 4, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 123, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 35, orbitMiddleState := 56, orbitMiddleCentral := 5, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 123, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 273. -/
def alternatingSixSchurConjugacyDatumRow273 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 113, orbitMiddleState := 216, orbitMiddleCentral := 2, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 113, orbitMiddleState := 216, orbitMiddleCentral := 3, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 113, orbitMiddleState := 216, orbitMiddleCentral := 4, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 113, orbitMiddleState := 216, orbitMiddleCentral := 5, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 113, orbitMiddleState := 216, orbitMiddleCentral := 0, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 113, orbitMiddleState := 216, orbitMiddleCentral := 1, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 274. -/
def alternatingSixSchurConjugacyDatumRow274 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 9, orbitMiddleState := 123, orbitMiddleCentral := 2, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 172, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 138, orbitMiddleState := 324, orbitMiddleCentral := 3, conjugatorInverseState := 147, conjugatorInverseCentral := 0, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 348, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 138, orbitMiddleState := 324, orbitMiddleCentral := 4, conjugatorInverseState := 147, conjugatorInverseCentral := 0, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 348, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 72, orbitMiddleState := 252, orbitMiddleCentral := 1, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 124, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 72, orbitMiddleState := 252, orbitMiddleCentral := 2, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 124, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 9, orbitMiddleState := 123, orbitMiddleCentral := 1, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 172, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 275. -/
def alternatingSixSchurConjugacyDatumRow275 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 38, orbitMiddleState := 90, orbitMiddleCentral := 1, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 184, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 38, orbitMiddleState := 90, orbitMiddleCentral := 2, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 184, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 38, orbitMiddleState := 90, orbitMiddleCentral := 3, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 184, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 38, orbitMiddleState := 90, orbitMiddleCentral := 4, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 184, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 38, orbitMiddleState := 90, orbitMiddleCentral := 5, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 184, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 38, orbitMiddleState := 90, orbitMiddleCentral := 0, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 184, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 276. -/
def alternatingSixSchurConjugacyDatumRow276 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 69, orbitMiddleState := 112, orbitMiddleCentral := 0, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 171, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 69, orbitMiddleState := 112, orbitMiddleCentral := 1, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 171, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 167, orbitMiddleState := 266, orbitMiddleCentral := 3, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 352, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 167, orbitMiddleState := 266, orbitMiddleCentral := 4, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 352, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 36, orbitMiddleState := 312, orbitMiddleCentral := 2, conjugatorInverseState := 42, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 1, orbitPenultimateState := 311, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 36, orbitMiddleState := 312, orbitMiddleCentral := 3, conjugatorInverseState := 42, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 1, orbitPenultimateState := 311, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 277. -/
def alternatingSixSchurConjugacyDatumRow277 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 12, conjugatorState := 141, orbitMiddleState := 193, orbitMiddleCentral := 3, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 287, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 141, orbitMiddleState := 193, orbitMiddleCentral := 4, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 287, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 141, orbitMiddleState := 193, orbitMiddleCentral := 5, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 287, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 141, orbitMiddleState := 193, orbitMiddleCentral := 0, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 287, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 141, orbitMiddleState := 193, orbitMiddleCentral := 1, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 287, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 141, orbitMiddleState := 193, orbitMiddleCentral := 2, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 287, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 278. -/
def alternatingSixSchurConjugacyDatumRow278 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 34, orbitMiddleState := 214, orbitMiddleCentral := 3, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 300, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 34, orbitMiddleState := 214, orbitMiddleCentral := 4, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 300, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 102, orbitMiddleState := 256, orbitMiddleCentral := 5, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 216, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 102, orbitMiddleState := 256, orbitMiddleCentral := 0, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 216, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 59, orbitMiddleState := 321, orbitMiddleCentral := 0, conjugatorInverseState := 69, conjugatorInverseCentral := 3, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 236, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 59, orbitMiddleState := 321, orbitMiddleCentral := 1, conjugatorInverseState := 69, conjugatorInverseCentral := 3, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 236, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 279. -/
def alternatingSixSchurConjugacyDatumRow279 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 19, orbitMiddleState := 88, orbitMiddleCentral := 5, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 178, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 70, orbitMiddleState := 352, orbitMiddleCentral := 5, conjugatorInverseState := 68, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 1, orbitPenultimateState := 288, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 70, orbitMiddleState := 352, orbitMiddleCentral := 0, conjugatorInverseState := 68, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 1, orbitPenultimateState := 288, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 95, orbitMiddleState := 135, orbitMiddleCentral := 1, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 282, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 95, orbitMiddleState := 135, orbitMiddleCentral := 2, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 282, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 19, orbitMiddleState := 88, orbitMiddleCentral := 4, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 178, orbitPenultimateCentral := 4 }
  ]


end GroupTheory
end McKayConjecture
