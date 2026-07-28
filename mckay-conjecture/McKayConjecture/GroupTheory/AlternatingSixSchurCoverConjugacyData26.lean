/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 260–269

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 260. -/
def alternatingSixSchurConjugacyDatumRow260 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 167, orbitMiddleState := 200, orbitMiddleCentral := 2, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 183, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 167, orbitMiddleState := 200, orbitMiddleCentral := 3, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 183, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 127, orbitMiddleState := 216, orbitMiddleCentral := 5, conjugatorInverseState := 127, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 332, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 127, orbitMiddleState := 216, orbitMiddleCentral := 0, conjugatorInverseState := 127, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 332, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 65, orbitMiddleState := 93, orbitMiddleCentral := 5, conjugatorInverseState := 49, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 109, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 65, orbitMiddleState := 93, orbitMiddleCentral := 0, conjugatorInverseState := 49, conjugatorInverseCentral := 3, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 109, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 261. -/
def alternatingSixSchurConjugacyDatumRow261 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 287, orbitMiddleState := 288, orbitMiddleCentral := 0, conjugatorInverseState := 275, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 4, orbitPenultimateState := 294, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 287, orbitMiddleState := 288, orbitMiddleCentral := 1, conjugatorInverseState := 275, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 4, orbitPenultimateState := 294, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 287, orbitMiddleState := 288, orbitMiddleCentral := 2, conjugatorInverseState := 275, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 4, orbitPenultimateState := 294, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 287, orbitMiddleState := 288, orbitMiddleCentral := 3, conjugatorInverseState := 275, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 4, orbitPenultimateState := 294, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 287, orbitMiddleState := 288, orbitMiddleCentral := 4, conjugatorInverseState := 275, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 4, orbitPenultimateState := 294, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 287, orbitMiddleState := 288, orbitMiddleCentral := 5, conjugatorInverseState := 275, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 4, orbitPenultimateState := 294, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 262. -/
def alternatingSixSchurConjugacyDatumRow262 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 16, orbitMiddleState := 248, orbitMiddleCentral := 0, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 213, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 16, orbitMiddleState := 248, orbitMiddleCentral := 1, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 213, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 187, orbitMiddleState := 320, orbitMiddleCentral := 5, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 198, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 187, orbitMiddleState := 320, orbitMiddleCentral := 0, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 198, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 20, orbitMiddleState := 273, orbitMiddleCentral := 3, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 272, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 20, orbitMiddleState := 273, orbitMiddleCentral := 4, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 272, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 263. -/
def alternatingSixSchurConjugacyDatumRow263 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 73, orbitMiddleState := 280, orbitMiddleCentral := 2, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 355, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 73, orbitMiddleState := 280, orbitMiddleCentral := 3, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 355, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 63, orbitMiddleState := 288, orbitMiddleCentral := 1, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 293, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 63, orbitMiddleState := 288, orbitMiddleCentral := 2, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 293, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 31, orbitMiddleState := 278, orbitMiddleCentral := 2, conjugatorInverseState := 44, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 1, orbitPenultimateState := 217, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 31, orbitMiddleState := 278, orbitMiddleCentral := 3, conjugatorInverseState := 44, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 1, orbitPenultimateState := 217, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 264. -/
def alternatingSixSchurConjugacyDatumRow264 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 47, orbitMiddleState := 113, orbitMiddleCentral := 4, conjugatorInverseState := 33, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 216, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 47, orbitMiddleState := 113, orbitMiddleCentral := 5, conjugatorInverseState := 33, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 216, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 98, orbitMiddleState := 321, orbitMiddleCentral := 0, conjugatorInverseState := 103, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 236, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 98, orbitMiddleState := 321, orbitMiddleCentral := 1, conjugatorInverseState := 103, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 236, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 56, orbitMiddleState := 81, orbitMiddleCentral := 1, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 224, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 56, orbitMiddleState := 81, orbitMiddleCentral := 2, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 224, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 265. -/
def alternatingSixSchurConjugacyDatumRow265 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 32, orbitMiddleState := 51, orbitMiddleCentral := 0, conjugatorInverseState := 32, conjugatorInverseCentral := 3, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 117, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 32, orbitMiddleState := 51, orbitMiddleCentral := 1, conjugatorInverseState := 32, conjugatorInverseCentral := 3, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 117, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 32, orbitMiddleState := 51, orbitMiddleCentral := 2, conjugatorInverseState := 32, conjugatorInverseCentral := 3, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 117, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 32, orbitMiddleState := 51, orbitMiddleCentral := 3, conjugatorInverseState := 32, conjugatorInverseCentral := 3, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 117, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 32, orbitMiddleState := 51, orbitMiddleCentral := 4, conjugatorInverseState := 32, conjugatorInverseCentral := 3, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 117, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 32, orbitMiddleState := 51, orbitMiddleCentral := 5, conjugatorInverseState := 32, conjugatorInverseCentral := 3, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 117, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 266. -/
def alternatingSixSchurConjugacyDatumRow266 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 30, orbitMiddleState := 219, orbitMiddleCentral := 1, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 304, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 30, orbitMiddleState := 219, orbitMiddleCentral := 2, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 304, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 227, orbitMiddleState := 312, orbitMiddleCentral := 0, conjugatorInverseState := 252, conjugatorInverseCentral := 2, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 39, inverseFactorRightCentral := 2, orbitPenultimateState := 349, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 227, orbitMiddleState := 312, orbitMiddleCentral := 1, conjugatorInverseState := 252, conjugatorInverseCentral := 2, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 39, inverseFactorRightCentral := 2, orbitPenultimateState := 349, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 25, orbitMiddleState := 191, orbitMiddleCentral := 0, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 190, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 25, orbitMiddleState := 191, orbitMiddleCentral := 1, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 190, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 267. -/
def alternatingSixSchurConjugacyDatumRow267 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 177, orbitMiddleState := 187, orbitMiddleCentral := 3, conjugatorInverseState := 190, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 5, orbitPenultimateState := 259, orbitPenultimateCentral := 1 },
    { classIndex := 15, conjugatorState := 177, orbitMiddleState := 187, orbitMiddleCentral := 4, conjugatorInverseState := 190, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 5, orbitPenultimateState := 259, orbitPenultimateCentral := 2 },
    { classIndex := 16, conjugatorState := 177, orbitMiddleState := 187, orbitMiddleCentral := 5, conjugatorInverseState := 190, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 5, orbitPenultimateState := 259, orbitPenultimateCentral := 3 },
    { classIndex := 17, conjugatorState := 177, orbitMiddleState := 187, orbitMiddleCentral := 0, conjugatorInverseState := 190, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 5, orbitPenultimateState := 259, orbitPenultimateCentral := 4 },
    { classIndex := 18, conjugatorState := 177, orbitMiddleState := 187, orbitMiddleCentral := 1, conjugatorInverseState := 190, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 5, orbitPenultimateState := 259, orbitPenultimateCentral := 5 },
    { classIndex := 19, conjugatorState := 177, orbitMiddleState := 187, orbitMiddleCentral := 2, conjugatorInverseState := 190, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 5, orbitPenultimateState := 259, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 268. -/
def alternatingSixSchurConjugacyDatumRow268 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 137, orbitMiddleState := 142, orbitMiddleCentral := 1, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 156, orbitPenultimateCentral := 5 },
    { classIndex := 28, conjugatorState := 137, orbitMiddleState := 142, orbitMiddleCentral := 2, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 156, orbitPenultimateCentral := 0 },
    { classIndex := 27, conjugatorState := 104, orbitMiddleState := 258, orbitMiddleCentral := 4, conjugatorInverseState := 83, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 353, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 104, orbitMiddleState := 258, orbitMiddleCentral := 5, conjugatorInverseState := 83, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 353, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 10, orbitMiddleState := 224, orbitMiddleCentral := 2, conjugatorInverseState := 14, conjugatorInverseCentral := 2, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 2, orbitPenultimateState := 167, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 10, orbitMiddleState := 224, orbitMiddleCentral := 3, conjugatorInverseState := 14, conjugatorInverseCentral := 2, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 2, orbitPenultimateState := 167, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 269. -/
def alternatingSixSchurConjugacyDatumRow269 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 34, orbitMiddleState := 83, orbitMiddleCentral := 1, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 172, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 34, orbitMiddleState := 83, orbitMiddleCentral := 2, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 172, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 34, orbitMiddleState := 83, orbitMiddleCentral := 3, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 172, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 34, orbitMiddleState := 83, orbitMiddleCentral := 4, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 172, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 34, orbitMiddleState := 83, orbitMiddleCentral := 5, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 172, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 34, orbitMiddleState := 83, orbitMiddleCentral := 0, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 172, orbitPenultimateCentral := 0 }
  ]


end GroupTheory
end McKayConjecture
