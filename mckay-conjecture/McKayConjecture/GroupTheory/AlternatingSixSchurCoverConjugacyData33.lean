/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 330–339

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 330. -/
def alternatingSixSchurConjugacyDatumRow330 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 61, orbitMiddleState := 124, orbitMiddleCentral := 4, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 252, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 61, orbitMiddleState := 124, orbitMiddleCentral := 5, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 252, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 42, orbitMiddleState := 251, orbitMiddleCentral := 1, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 326, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 42, orbitMiddleState := 251, orbitMiddleCentral := 2, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 326, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 156, orbitMiddleState := 224, orbitMiddleCentral := 3, conjugatorInverseState := 146, conjugatorInverseCentral := 0, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 0, orbitPenultimateState := 306, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 156, orbitMiddleState := 224, orbitMiddleCentral := 4, conjugatorInverseState := 146, conjugatorInverseCentral := 0, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 0, orbitPenultimateState := 306, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 331. -/
def alternatingSixSchurConjugacyDatumRow331 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 78, orbitMiddleState := 79, orbitMiddleCentral := 2, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 222, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 78, orbitMiddleState := 79, orbitMiddleCentral := 3, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 222, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 78, orbitMiddleState := 79, orbitMiddleCentral := 4, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 222, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 78, orbitMiddleState := 79, orbitMiddleCentral := 5, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 222, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 78, orbitMiddleState := 79, orbitMiddleCentral := 0, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 222, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 78, orbitMiddleState := 79, orbitMiddleCentral := 1, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 222, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 332. -/
def alternatingSixSchurConjugacyDatumRow332 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 89, orbitMiddleState := 135, orbitMiddleCentral := 4, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 260, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 120, orbitMiddleState := 358, orbitMiddleCentral := 0, conjugatorInverseState := 148, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 267, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 120, orbitMiddleState := 358, orbitMiddleCentral := 1, conjugatorInverseState := 148, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 267, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 77, orbitMiddleState := 152, orbitMiddleCentral := 0, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 296, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 77, orbitMiddleState := 152, orbitMiddleCentral := 1, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 296, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 89, orbitMiddleState := 135, orbitMiddleCentral := 3, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 260, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 333. -/
def alternatingSixSchurConjugacyDatumRow333 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 78, orbitMiddleState := 117, orbitMiddleCentral := 2, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 265, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 78, orbitMiddleState := 117, orbitMiddleCentral := 3, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 265, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 78, orbitMiddleState := 117, orbitMiddleCentral := 4, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 265, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 78, orbitMiddleState := 117, orbitMiddleCentral := 5, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 265, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 78, orbitMiddleState := 117, orbitMiddleCentral := 0, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 265, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 78, orbitMiddleState := 117, orbitMiddleCentral := 1, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 265, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 334. -/
def alternatingSixSchurConjugacyDatumRow334 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 89, orbitMiddleState := 130, orbitMiddleCentral := 5, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 178, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 89, orbitMiddleState := 130, orbitMiddleCentral := 0, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 178, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 89, orbitMiddleState := 130, orbitMiddleCentral := 1, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 178, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 89, orbitMiddleState := 130, orbitMiddleCentral := 2, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 178, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 89, orbitMiddleState := 130, orbitMiddleCentral := 3, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 178, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 89, orbitMiddleState := 130, orbitMiddleCentral := 4, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 178, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 335. -/
def alternatingSixSchurConjugacyDatumRow335 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 13, conjugatorState := 50, orbitMiddleState := 76, orbitMiddleCentral := 4, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 216, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 50, orbitMiddleState := 76, orbitMiddleCentral := 5, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 216, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 50, orbitMiddleState := 76, orbitMiddleCentral := 0, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 216, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 50, orbitMiddleState := 76, orbitMiddleCentral := 1, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 216, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 50, orbitMiddleState := 76, orbitMiddleCentral := 2, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 216, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 50, orbitMiddleState := 76, orbitMiddleCentral := 3, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 216, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 336. -/
def alternatingSixSchurConjugacyDatumRow336 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 60, orbitMiddleState := 90, orbitMiddleCentral := 5, conjugatorInverseState := 52, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 237, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 60, orbitMiddleState := 90, orbitMiddleCentral := 0, conjugatorInverseState := 52, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 237, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 60, orbitMiddleState := 90, orbitMiddleCentral := 1, conjugatorInverseState := 52, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 237, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 60, orbitMiddleState := 90, orbitMiddleCentral := 2, conjugatorInverseState := 52, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 237, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 60, orbitMiddleState := 90, orbitMiddleCentral := 3, conjugatorInverseState := 52, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 237, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 60, orbitMiddleState := 90, orbitMiddleCentral := 4, conjugatorInverseState := 52, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 237, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 337. -/
def alternatingSixSchurConjugacyDatumRow337 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 97, orbitMiddleState := 139, orbitMiddleCentral := 1, conjugatorInverseState := 81, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 97, orbitMiddleState := 139, orbitMiddleCentral := 2, conjugatorInverseState := 81, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 97, orbitMiddleState := 139, orbitMiddleCentral := 3, conjugatorInverseState := 81, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 97, orbitMiddleState := 139, orbitMiddleCentral := 4, conjugatorInverseState := 81, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 97, orbitMiddleState := 139, orbitMiddleCentral := 5, conjugatorInverseState := 81, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 97, orbitMiddleState := 139, orbitMiddleCentral := 0, conjugatorInverseState := 81, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 266, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 338. -/
def alternatingSixSchurConjugacyDatumRow338 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 102, orbitMiddleState := 146, orbitMiddleCentral := 0, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 291, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 102, orbitMiddleState := 146, orbitMiddleCentral := 1, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 291, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 102, orbitMiddleState := 146, orbitMiddleCentral := 2, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 291, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 102, orbitMiddleState := 146, orbitMiddleCentral := 3, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 291, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 102, orbitMiddleState := 146, orbitMiddleCentral := 4, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 291, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 102, orbitMiddleState := 146, orbitMiddleCentral := 5, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 291, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 339. -/
def alternatingSixSchurConjugacyDatumRow339 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 12, conjugatorState := 104, orbitMiddleState := 149, orbitMiddleCentral := 3, conjugatorInverseState := 83, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 293, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 104, orbitMiddleState := 149, orbitMiddleCentral := 4, conjugatorInverseState := 83, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 293, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 104, orbitMiddleState := 149, orbitMiddleCentral := 5, conjugatorInverseState := 83, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 293, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 104, orbitMiddleState := 149, orbitMiddleCentral := 0, conjugatorInverseState := 83, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 293, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 104, orbitMiddleState := 149, orbitMiddleCentral := 1, conjugatorInverseState := 83, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 293, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 104, orbitMiddleState := 149, orbitMiddleCentral := 2, conjugatorInverseState := 83, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 293, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
