/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 320–329

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 320. -/
def alternatingSixSchurConjugacyDatumRow320 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 210, orbitMiddleState := 211, orbitMiddleCentral := 5, conjugatorInverseState := 173, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 306, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 210, orbitMiddleState := 211, orbitMiddleCentral := 0, conjugatorInverseState := 173, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 306, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 210, orbitMiddleState := 211, orbitMiddleCentral := 1, conjugatorInverseState := 173, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 306, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 210, orbitMiddleState := 211, orbitMiddleCentral := 2, conjugatorInverseState := 173, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 306, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 210, orbitMiddleState := 211, orbitMiddleCentral := 3, conjugatorInverseState := 173, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 306, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 210, orbitMiddleState := 211, orbitMiddleCentral := 4, conjugatorInverseState := 173, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 306, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 321. -/
def alternatingSixSchurConjugacyDatumRow321 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 63, orbitMiddleState := 64, orbitMiddleCentral := 3, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 192, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 63, orbitMiddleState := 64, orbitMiddleCentral := 4, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 192, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 63, orbitMiddleState := 64, orbitMiddleCentral := 5, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 192, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 63, orbitMiddleState := 64, orbitMiddleCentral := 0, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 192, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 63, orbitMiddleState := 64, orbitMiddleCentral := 1, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 192, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 63, orbitMiddleState := 64, orbitMiddleCentral := 2, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 192, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 322. -/
def alternatingSixSchurConjugacyDatumRow322 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 35, orbitMiddleState := 236, orbitMiddleCentral := 2, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 287, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 70, orbitMiddleState := 301, orbitMiddleCentral := 2, conjugatorInverseState := 68, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 1, orbitPenultimateState := 256, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 70, orbitMiddleState := 301, orbitMiddleCentral := 3, conjugatorInverseState := 68, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 1, orbitPenultimateState := 256, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 101, orbitMiddleState := 220, orbitMiddleCentral := 5, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 338, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 101, orbitMiddleState := 220, orbitMiddleCentral := 0, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 338, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 35, orbitMiddleState := 236, orbitMiddleCentral := 1, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 287, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 323. -/
def alternatingSixSchurConjugacyDatumRow323 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 12, conjugatorState := 124, orbitMiddleState := 173, orbitMiddleCentral := 3, conjugatorInverseState := 122, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 341, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 124, orbitMiddleState := 173, orbitMiddleCentral := 4, conjugatorInverseState := 122, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 341, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 124, orbitMiddleState := 173, orbitMiddleCentral := 5, conjugatorInverseState := 122, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 341, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 124, orbitMiddleState := 173, orbitMiddleCentral := 0, conjugatorInverseState := 122, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 341, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 124, orbitMiddleState := 173, orbitMiddleCentral := 1, conjugatorInverseState := 122, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 341, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 124, orbitMiddleState := 173, orbitMiddleCentral := 2, conjugatorInverseState := 122, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 341, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 324. -/
def alternatingSixSchurConjugacyDatumRow324 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 57, orbitMiddleState := 125, orbitMiddleCentral := 1, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 276, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 57, orbitMiddleState := 125, orbitMiddleCentral := 2, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 276, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 57, orbitMiddleState := 125, orbitMiddleCentral := 3, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 276, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 57, orbitMiddleState := 125, orbitMiddleCentral := 4, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 276, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 57, orbitMiddleState := 125, orbitMiddleCentral := 5, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 276, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 57, orbitMiddleState := 125, orbitMiddleCentral := 0, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 276, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 325. -/
def alternatingSixSchurConjugacyDatumRow325 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 235, orbitMiddleState := 236, orbitMiddleCentral := 3, conjugatorInverseState := 230, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 322, orbitPenultimateCentral := 4 },
    { classIndex := 18, conjugatorState := 235, orbitMiddleState := 236, orbitMiddleCentral := 4, conjugatorInverseState := 230, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 322, orbitPenultimateCentral := 5 },
    { classIndex := 19, conjugatorState := 235, orbitMiddleState := 236, orbitMiddleCentral := 5, conjugatorInverseState := 230, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 322, orbitPenultimateCentral := 0 },
    { classIndex := 20, conjugatorState := 235, orbitMiddleState := 236, orbitMiddleCentral := 0, conjugatorInverseState := 230, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 322, orbitPenultimateCentral := 1 },
    { classIndex := 15, conjugatorState := 235, orbitMiddleState := 236, orbitMiddleCentral := 1, conjugatorInverseState := 230, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 322, orbitPenultimateCentral := 2 },
    { classIndex := 16, conjugatorState := 235, orbitMiddleState := 236, orbitMiddleCentral := 2, conjugatorInverseState := 230, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 322, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 326. -/
def alternatingSixSchurConjugacyDatumRow326 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 86, orbitMiddleState := 125, orbitMiddleCentral := 2, conjugatorInverseState := 78, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 207, orbitPenultimateCentral := 0 },
    { classIndex := 12, conjugatorState := 86, orbitMiddleState := 125, orbitMiddleCentral := 3, conjugatorInverseState := 78, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 207, orbitPenultimateCentral := 1 },
    { classIndex := 13, conjugatorState := 86, orbitMiddleState := 125, orbitMiddleCentral := 4, conjugatorInverseState := 78, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 207, orbitPenultimateCentral := 2 },
    { classIndex := 14, conjugatorState := 86, orbitMiddleState := 125, orbitMiddleCentral := 5, conjugatorInverseState := 78, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 207, orbitPenultimateCentral := 3 },
    { classIndex := 9, conjugatorState := 86, orbitMiddleState := 125, orbitMiddleCentral := 0, conjugatorInverseState := 78, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 207, orbitPenultimateCentral := 4 },
    { classIndex := 10, conjugatorState := 86, orbitMiddleState := 125, orbitMiddleCentral := 1, conjugatorInverseState := 78, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 207, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 327. -/
def alternatingSixSchurConjugacyDatumRow327 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 39, orbitMiddleState := 140, orbitMiddleCentral := 5, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 244, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 31, orbitMiddleState := 301, orbitMiddleCentral := 2, conjugatorInverseState := 44, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 1, orbitPenultimateState := 294, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 31, orbitMiddleState := 301, orbitMiddleCentral := 3, conjugatorInverseState := 44, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 1, orbitPenultimateState := 294, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 125, orbitMiddleState := 146, orbitMiddleCentral := 0, conjugatorInverseState := 125, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 325, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 125, orbitMiddleState := 146, orbitMiddleCentral := 1, conjugatorInverseState := 125, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 325, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 39, orbitMiddleState := 140, orbitMiddleCentral := 4, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 244, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 328. -/
def alternatingSixSchurConjugacyDatumRow328 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 135, orbitMiddleState := 240, orbitMiddleCentral := 4, conjugatorInverseState := 140, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 346, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 135, orbitMiddleState := 240, orbitMiddleCentral := 5, conjugatorInverseState := 140, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 346, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 135, orbitMiddleState := 240, orbitMiddleCentral := 0, conjugatorInverseState := 140, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 346, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 135, orbitMiddleState := 240, orbitMiddleCentral := 1, conjugatorInverseState := 140, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 346, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 135, orbitMiddleState := 240, orbitMiddleCentral := 2, conjugatorInverseState := 140, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 346, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 135, orbitMiddleState := 240, orbitMiddleCentral := 3, conjugatorInverseState := 140, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 346, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 329. -/
def alternatingSixSchurConjugacyDatumRow329 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 46, orbitMiddleState := 105, orbitMiddleCentral := 2, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 207, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 46, orbitMiddleState := 105, orbitMiddleCentral := 3, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 207, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 46, orbitMiddleState := 105, orbitMiddleCentral := 4, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 207, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 46, orbitMiddleState := 105, orbitMiddleCentral := 5, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 207, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 46, orbitMiddleState := 105, orbitMiddleCentral := 0, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 207, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 46, orbitMiddleState := 105, orbitMiddleCentral := 1, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 207, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
