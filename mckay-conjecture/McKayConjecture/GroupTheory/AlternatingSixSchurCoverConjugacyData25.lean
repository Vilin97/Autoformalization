/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 250–259

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 250. -/
def alternatingSixSchurConjugacyDatumRow250 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 155, orbitMiddleState := 156, orbitMiddleCentral := 5, conjugatorInverseState := 130, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 249, orbitPenultimateCentral := 0 },
    { classIndex := 20, conjugatorState := 155, orbitMiddleState := 156, orbitMiddleCentral := 0, conjugatorInverseState := 130, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 249, orbitPenultimateCentral := 1 },
    { classIndex := 15, conjugatorState := 155, orbitMiddleState := 156, orbitMiddleCentral := 1, conjugatorInverseState := 130, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 249, orbitPenultimateCentral := 2 },
    { classIndex := 16, conjugatorState := 155, orbitMiddleState := 156, orbitMiddleCentral := 2, conjugatorInverseState := 130, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 249, orbitPenultimateCentral := 3 },
    { classIndex := 17, conjugatorState := 155, orbitMiddleState := 156, orbitMiddleCentral := 3, conjugatorInverseState := 130, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 249, orbitPenultimateCentral := 4 },
    { classIndex := 18, conjugatorState := 155, orbitMiddleState := 156, orbitMiddleCentral := 4, conjugatorInverseState := 130, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 249, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 251. -/
def alternatingSixSchurConjugacyDatumRow251 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 42, orbitMiddleState := 43, orbitMiddleCentral := 5, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 101, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 42, orbitMiddleState := 43, orbitMiddleCentral := 0, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 101, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 42, orbitMiddleState := 43, orbitMiddleCentral := 1, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 101, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 42, orbitMiddleState := 43, orbitMiddleCentral := 2, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 101, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 42, orbitMiddleState := 43, orbitMiddleCentral := 3, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 101, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 42, orbitMiddleState := 43, orbitMiddleCentral := 4, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 101, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 252. -/
def alternatingSixSchurConjugacyDatumRow252 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 154, orbitMiddleState := 315, orbitMiddleCentral := 2, conjugatorInverseState := 149, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 173, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 46, orbitMiddleState := 56, orbitMiddleCentral := 4, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 124, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 46, orbitMiddleState := 56, orbitMiddleCentral := 5, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 124, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 179, orbitMiddleState := 266, orbitMiddleCentral := 0, conjugatorInverseState := 179, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 1, orbitPenultimateState := 351, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 179, orbitMiddleState := 266, orbitMiddleCentral := 1, conjugatorInverseState := 179, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 1, orbitPenultimateState := 351, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 154, orbitMiddleState := 315, orbitMiddleCentral := 1, conjugatorInverseState := 149, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 173, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 253. -/
def alternatingSixSchurConjugacyDatumRow253 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 158, orbitMiddleState := 214, orbitMiddleCentral := 2, conjugatorInverseState := 176, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 1, orbitPenultimateState := 247, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 158, orbitMiddleState := 214, orbitMiddleCentral := 3, conjugatorInverseState := 176, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 1, orbitPenultimateState := 247, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 158, orbitMiddleState := 214, orbitMiddleCentral := 4, conjugatorInverseState := 176, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 1, orbitPenultimateState := 247, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 158, orbitMiddleState := 214, orbitMiddleCentral := 5, conjugatorInverseState := 176, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 1, orbitPenultimateState := 247, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 158, orbitMiddleState := 214, orbitMiddleCentral := 0, conjugatorInverseState := 176, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 1, orbitPenultimateState := 247, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 158, orbitMiddleState := 214, orbitMiddleCentral := 1, conjugatorInverseState := 176, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 1, orbitPenultimateState := 247, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 254. -/
def alternatingSixSchurConjugacyDatumRow254 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 26, orbitMiddleState := 68, orbitMiddleCentral := 4, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 148, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 26, orbitMiddleState := 68, orbitMiddleCentral := 5, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 148, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 26, orbitMiddleState := 68, orbitMiddleCentral := 0, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 148, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 26, orbitMiddleState := 68, orbitMiddleCentral := 1, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 148, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 26, orbitMiddleState := 68, orbitMiddleCentral := 2, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 148, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 26, orbitMiddleState := 68, orbitMiddleCentral := 3, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 148, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 255. -/
def alternatingSixSchurConjugacyDatumRow255 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 275, orbitMiddleState := 315, orbitMiddleCentral := 5, conjugatorInverseState := 287, conjugatorInverseCentral := 4, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 4, orbitPenultimateState := 289, orbitPenultimateCentral := 4 },
    { classIndex := 15, conjugatorState := 275, orbitMiddleState := 315, orbitMiddleCentral := 0, conjugatorInverseState := 287, conjugatorInverseCentral := 4, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 4, orbitPenultimateState := 289, orbitPenultimateCentral := 5 },
    { classIndex := 16, conjugatorState := 275, orbitMiddleState := 315, orbitMiddleCentral := 1, conjugatorInverseState := 287, conjugatorInverseCentral := 4, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 4, orbitPenultimateState := 289, orbitPenultimateCentral := 0 },
    { classIndex := 17, conjugatorState := 275, orbitMiddleState := 315, orbitMiddleCentral := 2, conjugatorInverseState := 287, conjugatorInverseCentral := 4, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 4, orbitPenultimateState := 289, orbitPenultimateCentral := 1 },
    { classIndex := 18, conjugatorState := 275, orbitMiddleState := 315, orbitMiddleCentral := 3, conjugatorInverseState := 287, conjugatorInverseCentral := 4, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 4, orbitPenultimateState := 289, orbitPenultimateCentral := 2 },
    { classIndex := 19, conjugatorState := 275, orbitMiddleState := 315, orbitMiddleCentral := 4, conjugatorInverseState := 287, conjugatorInverseCentral := 4, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 4, orbitPenultimateState := 289, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 256. -/
def alternatingSixSchurConjugacyDatumRow256 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 15, conjugatorState := 77, orbitMiddleState := 162, orbitMiddleCentral := 0, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 303, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 77, orbitMiddleState := 162, orbitMiddleCentral := 1, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 303, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 77, orbitMiddleState := 162, orbitMiddleCentral := 2, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 303, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 77, orbitMiddleState := 162, orbitMiddleCentral := 3, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 303, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 77, orbitMiddleState := 162, orbitMiddleCentral := 4, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 303, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 77, orbitMiddleState := 162, orbitMiddleCentral := 5, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 303, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 257. -/
def alternatingSixSchurConjugacyDatumRow257 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 49, orbitMiddleState := 75, orbitMiddleCentral := 0, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 215, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 49, orbitMiddleState := 75, orbitMiddleCentral := 1, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 215, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 49, orbitMiddleState := 75, orbitMiddleCentral := 2, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 215, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 34, orbitMiddleState := 55, orbitMiddleCentral := 0, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 122, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 34, orbitMiddleState := 55, orbitMiddleCentral := 1, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 122, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 34, orbitMiddleState := 55, orbitMiddleCentral := 2, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 122, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 258. -/
def alternatingSixSchurConjugacyDatumRow258 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 122, orbitMiddleState := 223, orbitMiddleCentral := 5, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 357, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 122, orbitMiddleState := 223, orbitMiddleCentral := 0, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 357, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 128, orbitMiddleState := 304, orbitMiddleCentral := 5, conjugatorInverseState := 144, conjugatorInverseCentral := 3, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 3, orbitPenultimateState := 259, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 128, orbitMiddleState := 304, orbitMiddleCentral := 0, conjugatorInverseState := 144, conjugatorInverseCentral := 3, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 3, orbitPenultimateState := 259, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 15, orbitMiddleState := 147, orbitMiddleCentral := 0, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 201, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 15, orbitMiddleState := 147, orbitMiddleCentral := 1, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 201, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 259. -/
def alternatingSixSchurConjugacyDatumRow259 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 189, orbitMiddleState := 242, orbitMiddleCentral := 0, conjugatorInverseState := 171, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 358, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 189, orbitMiddleState := 242, orbitMiddleCentral := 1, conjugatorInverseState := 171, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 358, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 189, orbitMiddleState := 242, orbitMiddleCentral := 2, conjugatorInverseState := 171, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 358, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 189, orbitMiddleState := 242, orbitMiddleCentral := 3, conjugatorInverseState := 171, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 358, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 189, orbitMiddleState := 242, orbitMiddleCentral := 4, conjugatorInverseState := 171, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 358, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 189, orbitMiddleState := 242, orbitMiddleCentral := 5, conjugatorInverseState := 171, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 358, orbitPenultimateCentral := 4 }
  ]


end GroupTheory
end McKayConjecture
