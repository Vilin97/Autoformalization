/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 350–359

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 350. -/
def alternatingSixSchurConjugacyDatumRow350 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 67, orbitMiddleState := 100, orbitMiddleCentral := 0, conjugatorInverseState := 54, conjugatorInverseCentral := 4, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 4, orbitPenultimateState := 250, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 67, orbitMiddleState := 100, orbitMiddleCentral := 1, conjugatorInverseState := 54, conjugatorInverseCentral := 4, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 4, orbitPenultimateState := 250, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 67, orbitMiddleState := 100, orbitMiddleCentral := 2, conjugatorInverseState := 54, conjugatorInverseCentral := 4, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 4, orbitPenultimateState := 250, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 67, orbitMiddleState := 100, orbitMiddleCentral := 3, conjugatorInverseState := 54, conjugatorInverseCentral := 4, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 4, orbitPenultimateState := 250, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 67, orbitMiddleState := 100, orbitMiddleCentral := 4, conjugatorInverseState := 54, conjugatorInverseCentral := 4, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 4, orbitPenultimateState := 250, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 67, orbitMiddleState := 100, orbitMiddleCentral := 5, conjugatorInverseState := 54, conjugatorInverseCentral := 4, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 4, orbitPenultimateState := 250, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 351. -/
def alternatingSixSchurConjugacyDatumRow351 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 187, orbitMiddleState := 209, orbitMiddleCentral := 0, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 296, orbitPenultimateCentral := 0 },
    { classIndex := 12, conjugatorState := 187, orbitMiddleState := 209, orbitMiddleCentral := 1, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 296, orbitPenultimateCentral := 1 },
    { classIndex := 13, conjugatorState := 187, orbitMiddleState := 209, orbitMiddleCentral := 2, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 296, orbitPenultimateCentral := 2 },
    { classIndex := 14, conjugatorState := 187, orbitMiddleState := 209, orbitMiddleCentral := 3, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 296, orbitPenultimateCentral := 3 },
    { classIndex := 9, conjugatorState := 187, orbitMiddleState := 209, orbitMiddleCentral := 4, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 296, orbitPenultimateCentral := 4 },
    { classIndex := 10, conjugatorState := 187, orbitMiddleState := 209, orbitMiddleCentral := 5, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 296, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 352. -/
def alternatingSixSchurConjugacyDatumRow352 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 81, orbitMiddleState := 168, orbitMiddleCentral := 5, conjugatorInverseState := 97, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 81, orbitMiddleState := 168, orbitMiddleCentral := 0, conjugatorInverseState := 97, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 81, orbitMiddleState := 168, orbitMiddleCentral := 1, conjugatorInverseState := 97, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 81, orbitMiddleState := 168, orbitMiddleCentral := 2, conjugatorInverseState := 97, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 81, orbitMiddleState := 168, orbitMiddleCentral := 3, conjugatorInverseState := 97, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 81, orbitMiddleState := 168, orbitMiddleCentral := 4, conjugatorInverseState := 97, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 353. -/
def alternatingSixSchurConjugacyDatumRow353 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 122, orbitMiddleState := 123, orbitMiddleCentral := 0, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 309, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 122, orbitMiddleState := 123, orbitMiddleCentral := 1, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 309, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 122, orbitMiddleState := 123, orbitMiddleCentral := 2, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 309, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 122, orbitMiddleState := 123, orbitMiddleCentral := 3, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 309, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 122, orbitMiddleState := 123, orbitMiddleCentral := 4, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 309, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 122, orbitMiddleState := 123, orbitMiddleCentral := 5, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 309, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 354. -/
def alternatingSixSchurConjugacyDatumRow354 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 120, orbitMiddleState := 167, orbitMiddleCentral := 2, conjugatorInverseState := 148, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 228, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 76, orbitMiddleState := 114, orbitMiddleCentral := 0, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 264, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 76, orbitMiddleState := 114, orbitMiddleCentral := 1, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 264, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 76, orbitMiddleState := 114, orbitMiddleCentral := 2, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 264, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 120, orbitMiddleState := 167, orbitMiddleCentral := 0, conjugatorInverseState := 148, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 228, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 120, orbitMiddleState := 167, orbitMiddleCentral := 1, conjugatorInverseState := 148, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 228, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 355. -/
def alternatingSixSchurConjugacyDatumRow355 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 123, orbitMiddleState := 172, orbitMiddleCentral := 0, conjugatorInverseState := 141, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 278, orbitPenultimateCentral := 1 },
    { classIndex := 7, conjugatorState := 123, orbitMiddleState := 172, orbitMiddleCentral := 1, conjugatorInverseState := 141, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 278, orbitPenultimateCentral := 2 },
    { classIndex := 8, conjugatorState := 123, orbitMiddleState := 172, orbitMiddleCentral := 2, conjugatorInverseState := 141, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 278, orbitPenultimateCentral := 3 },
    { classIndex := 6, conjugatorState := 88, orbitMiddleState := 129, orbitMiddleCentral := 0, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 217, orbitPenultimateCentral := 1 },
    { classIndex := 7, conjugatorState := 88, orbitMiddleState := 129, orbitMiddleCentral := 1, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 217, orbitPenultimateCentral := 2 },
    { classIndex := 8, conjugatorState := 88, orbitMiddleState := 129, orbitMiddleCentral := 2, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 217, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 356. -/
def alternatingSixSchurConjugacyDatumRow356 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 113, orbitMiddleState := 160, orbitMiddleCentral := 0, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 256, orbitPenultimateCentral := 2 },
    { classIndex := 7, conjugatorState := 113, orbitMiddleState := 160, orbitMiddleCentral := 1, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 256, orbitPenultimateCentral := 3 },
    { classIndex := 8, conjugatorState := 113, orbitMiddleState := 160, orbitMiddleCentral := 2, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 256, orbitPenultimateCentral := 4 },
    { classIndex := 6, conjugatorState := 126, orbitMiddleState := 176, orbitMiddleCentral := 0, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 343, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 126, orbitMiddleState := 176, orbitMiddleCentral := 1, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 343, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 126, orbitMiddleState := 176, orbitMiddleCentral := 2, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 343, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 357. -/
def alternatingSixSchurConjugacyDatumRow357 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 110, orbitMiddleState := 155, orbitMiddleCentral := 0, conjugatorInverseState := 110, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 299, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 110, orbitMiddleState := 155, orbitMiddleCentral := 1, conjugatorInverseState := 110, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 299, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 110, orbitMiddleState := 155, orbitMiddleCentral := 2, conjugatorInverseState := 110, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 299, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 95, orbitMiddleState := 137, orbitMiddleCentral := 0, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 285, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 95, orbitMiddleState := 137, orbitMiddleCentral := 1, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 285, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 95, orbitMiddleState := 137, orbitMiddleCentral := 2, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 285, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 358. -/
def alternatingSixSchurConjugacyDatumRow358 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 91, orbitMiddleState := 134, orbitMiddleCentral := 0, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 281, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 91, orbitMiddleState := 134, orbitMiddleCentral := 1, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 281, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 91, orbitMiddleState := 134, orbitMiddleCentral := 2, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 281, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 106, orbitMiddleState := 152, orbitMiddleCentral := 0, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 296, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 106, orbitMiddleState := 152, orbitMiddleCentral := 1, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 296, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 106, orbitMiddleState := 152, orbitMiddleCentral := 2, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 296, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 359. -/
def alternatingSixSchurConjugacyDatumRow359 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 130, orbitMiddleState := 179, orbitMiddleCentral := 0, conjugatorInverseState := 155, conjugatorInverseCentral := 2, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 321, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 130, orbitMiddleState := 179, orbitMiddleCentral := 1, conjugatorInverseState := 155, conjugatorInverseCentral := 2, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 321, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 130, orbitMiddleState := 179, orbitMiddleCentral := 2, conjugatorInverseState := 155, conjugatorInverseCentral := 2, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 321, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 117, orbitMiddleState := 163, orbitMiddleCentral := 0, conjugatorInverseState := 157, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 338, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 117, orbitMiddleState := 163, orbitMiddleCentral := 1, conjugatorInverseState := 157, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 338, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 117, orbitMiddleState := 163, orbitMiddleCentral := 2, conjugatorInverseState := 157, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 338, orbitPenultimateCentral := 5 }
  ]


end GroupTheory
end McKayConjecture
