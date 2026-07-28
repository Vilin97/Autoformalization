/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 340–349

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 340. -/
def alternatingSixSchurConjugacyDatumRow340 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 52, orbitMiddleState := 80, orbitMiddleCentral := 0, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 223, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 52, orbitMiddleState := 80, orbitMiddleCentral := 1, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 223, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 52, orbitMiddleState := 80, orbitMiddleCentral := 2, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 223, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 143, orbitMiddleState := 197, orbitMiddleCentral := 0, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 320, orbitPenultimateCentral := 1 },
    { classIndex := 7, conjugatorState := 143, orbitMiddleState := 197, orbitMiddleCentral := 1, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 320, orbitPenultimateCentral := 2 },
    { classIndex := 8, conjugatorState := 143, orbitMiddleState := 197, orbitMiddleCentral := 2, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 320, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 341. -/
def alternatingSixSchurConjugacyDatumRow341 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 56, orbitMiddleState := 84, orbitMiddleCentral := 0, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 229, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 56, orbitMiddleState := 84, orbitMiddleCentral := 1, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 229, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 56, orbitMiddleState := 84, orbitMiddleCentral := 2, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 229, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 146, orbitMiddleState := 200, orbitMiddleCentral := 0, conjugatorInverseState := 156, conjugatorInverseCentral := 0, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 329, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 146, orbitMiddleState := 200, orbitMiddleCentral := 1, conjugatorInverseState := 156, conjugatorInverseCentral := 0, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 329, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 146, orbitMiddleState := 200, orbitMiddleCentral := 2, conjugatorInverseState := 156, conjugatorInverseCentral := 0, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 329, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 342. -/
def alternatingSixSchurConjugacyDatumRow342 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 71, orbitMiddleState := 105, orbitMiddleCentral := 0, conjugatorInverseState := 51, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 232, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 71, orbitMiddleState := 105, orbitMiddleCentral := 1, conjugatorInverseState := 51, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 232, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 71, orbitMiddleState := 105, orbitMiddleCentral := 2, conjugatorInverseState := 51, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 232, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 71, orbitMiddleState := 105, orbitMiddleCentral := 3, conjugatorInverseState := 51, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 232, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 71, orbitMiddleState := 105, orbitMiddleCentral := 4, conjugatorInverseState := 51, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 232, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 71, orbitMiddleState := 105, orbitMiddleCentral := 5, conjugatorInverseState := 51, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 232, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 343. -/
def alternatingSixSchurConjugacyDatumRow343 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 13, conjugatorState := 58, orbitMiddleState := 87, orbitMiddleCentral := 4, conjugatorInverseState := 53, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 0, orbitPenultimateState := 233, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 58, orbitMiddleState := 87, orbitMiddleCentral := 5, conjugatorInverseState := 53, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 0, orbitPenultimateState := 233, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 58, orbitMiddleState := 87, orbitMiddleCentral := 0, conjugatorInverseState := 53, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 0, orbitPenultimateState := 233, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 58, orbitMiddleState := 87, orbitMiddleCentral := 1, conjugatorInverseState := 53, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 0, orbitPenultimateState := 233, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 58, orbitMiddleState := 87, orbitMiddleCentral := 2, conjugatorInverseState := 53, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 0, orbitPenultimateState := 233, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 58, orbitMiddleState := 87, orbitMiddleCentral := 3, conjugatorInverseState := 53, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 0, orbitPenultimateState := 233, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 344. -/
def alternatingSixSchurConjugacyDatumRow344 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 63, orbitMiddleState := 95, orbitMiddleCentral := 5, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 241, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 63, orbitMiddleState := 95, orbitMiddleCentral := 0, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 241, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 63, orbitMiddleState := 95, orbitMiddleCentral := 1, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 241, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 63, orbitMiddleState := 95, orbitMiddleCentral := 2, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 241, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 63, orbitMiddleState := 95, orbitMiddleCentral := 3, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 241, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 63, orbitMiddleState := 95, orbitMiddleCentral := 4, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 241, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 345. -/
def alternatingSixSchurConjugacyDatumRow345 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 99, orbitMiddleState := 142, orbitMiddleCentral := 0, conjugatorInverseState := 79, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 289, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 99, orbitMiddleState := 142, orbitMiddleCentral := 1, conjugatorInverseState := 79, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 289, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 99, orbitMiddleState := 142, orbitMiddleCentral := 2, conjugatorInverseState := 79, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 289, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 99, orbitMiddleState := 142, orbitMiddleCentral := 3, conjugatorInverseState := 79, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 289, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 99, orbitMiddleState := 142, orbitMiddleCentral := 4, conjugatorInverseState := 79, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 289, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 99, orbitMiddleState := 142, orbitMiddleCentral := 5, conjugatorInverseState := 79, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 289, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 346. -/
def alternatingSixSchurConjugacyDatumRow346 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 74, orbitMiddleState := 110, orbitMiddleCentral := 5, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 261, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 74, orbitMiddleState := 110, orbitMiddleCentral := 0, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 261, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 74, orbitMiddleState := 110, orbitMiddleCentral := 1, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 261, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 74, orbitMiddleState := 110, orbitMiddleCentral := 2, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 261, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 74, orbitMiddleState := 110, orbitMiddleCentral := 3, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 261, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 74, orbitMiddleState := 110, orbitMiddleCentral := 4, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 261, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 347. -/
def alternatingSixSchurConjugacyDatumRow347 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 12, conjugatorState := 75, orbitMiddleState := 112, orbitMiddleCentral := 3, conjugatorInverseState := 80, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 213, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 75, orbitMiddleState := 112, orbitMiddleCentral := 4, conjugatorInverseState := 80, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 213, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 75, orbitMiddleState := 112, orbitMiddleCentral := 5, conjugatorInverseState := 80, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 213, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 75, orbitMiddleState := 112, orbitMiddleCentral := 0, conjugatorInverseState := 80, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 213, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 75, orbitMiddleState := 112, orbitMiddleCentral := 1, conjugatorInverseState := 80, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 213, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 75, orbitMiddleState := 112, orbitMiddleCentral := 2, conjugatorInverseState := 80, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 213, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 348. -/
def alternatingSixSchurConjugacyDatumRow348 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 66, orbitMiddleState := 142, orbitMiddleCentral := 5, conjugatorInverseState := 64, conjugatorInverseCentral := 1, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 242, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 66, orbitMiddleState := 142, orbitMiddleCentral := 0, conjugatorInverseState := 64, conjugatorInverseCentral := 1, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 242, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 66, orbitMiddleState := 142, orbitMiddleCentral := 1, conjugatorInverseState := 64, conjugatorInverseCentral := 1, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 242, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 66, orbitMiddleState := 142, orbitMiddleCentral := 2, conjugatorInverseState := 64, conjugatorInverseCentral := 1, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 242, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 66, orbitMiddleState := 142, orbitMiddleCentral := 3, conjugatorInverseState := 64, conjugatorInverseCentral := 1, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 242, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 66, orbitMiddleState := 142, orbitMiddleCentral := 4, conjugatorInverseState := 64, conjugatorInverseCentral := 1, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 242, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 349. -/
def alternatingSixSchurConjugacyDatumRow349 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 102, orbitMiddleState := 103, orbitMiddleCentral := 0, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 255, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 102, orbitMiddleState := 103, orbitMiddleCentral := 1, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 255, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 102, orbitMiddleState := 103, orbitMiddleCentral := 2, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 255, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 102, orbitMiddleState := 103, orbitMiddleCentral := 3, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 255, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 102, orbitMiddleState := 103, orbitMiddleCentral := 4, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 255, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 102, orbitMiddleState := 103, orbitMiddleCentral := 5, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 255, orbitPenultimateCentral := 5 }
  ]


end GroupTheory
end McKayConjecture
