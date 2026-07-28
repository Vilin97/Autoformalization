/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 310–319

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 310. -/
def alternatingSixSchurConjugacyDatumRow310 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 102, orbitMiddleState := 193, orbitMiddleCentral := 0, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 322, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 108, orbitMiddleState := 285, orbitMiddleCentral := 5, conjugatorInverseState := 100, conjugatorInverseCentral := 4, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 4, orbitPenultimateState := 312, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 108, orbitMiddleState := 285, orbitMiddleCentral := 0, conjugatorInverseState := 100, conjugatorInverseCentral := 4, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 4, orbitPenultimateState := 312, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 20, orbitMiddleState := 171, orbitMiddleCentral := 0, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 257, orbitPenultimateCentral := 5 },
    { classIndex := 28, conjugatorState := 20, orbitMiddleState := 171, orbitMiddleCentral := 1, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 257, orbitPenultimateCentral := 0 },
    { classIndex := 27, conjugatorState := 102, orbitMiddleState := 193, orbitMiddleCentral := 5, conjugatorInverseState := 85, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 322, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 311. -/
def alternatingSixSchurConjugacyDatumRow311 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 76, orbitMiddleState := 104, orbitMiddleCentral := 5, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 257, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 76, orbitMiddleState := 104, orbitMiddleCentral := 0, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 257, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 53, orbitMiddleState := 250, orbitMiddleCentral := 5, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 342, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 53, orbitMiddleState := 250, orbitMiddleCentral := 0, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 342, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 134, orbitMiddleState := 180, orbitMiddleCentral := 1, conjugatorInverseState := 113, conjugatorInverseCentral := 2, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 244, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 134, orbitMiddleState := 180, orbitMiddleCentral := 2, conjugatorInverseState := 113, conjugatorInverseCentral := 2, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 244, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 312. -/
def alternatingSixSchurConjugacyDatumRow312 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 203, orbitMiddleState := 255, orbitMiddleCentral := 2, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 288, orbitPenultimateCentral := 3 },
    { classIndex := 6, conjugatorState := 213, orbitMiddleState := 214, orbitMiddleCentral := 4, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 354, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 213, orbitMiddleState := 214, orbitMiddleCentral := 5, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 354, orbitPenultimateCentral := 5 },
    { classIndex := 8, conjugatorState := 213, orbitMiddleState := 214, orbitMiddleCentral := 0, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 354, orbitPenultimateCentral := 0 },
    { classIndex := 6, conjugatorState := 203, orbitMiddleState := 255, orbitMiddleCentral := 0, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 288, orbitPenultimateCentral := 1 },
    { classIndex := 7, conjugatorState := 203, orbitMiddleState := 255, orbitMiddleCentral := 1, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 288, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 313. -/
def alternatingSixSchurConjugacyDatumRow313 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 74, orbitMiddleState := 161, orbitMiddleCentral := 3, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 178, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 98, orbitMiddleState := 352, orbitMiddleCentral := 0, conjugatorInverseState := 103, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 288, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 98, orbitMiddleState := 352, orbitMiddleCentral := 1, conjugatorInverseState := 103, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 288, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 62, orbitMiddleState := 176, orbitMiddleCentral := 5, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 311, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 62, orbitMiddleState := 176, orbitMiddleCentral := 0, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 311, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 74, orbitMiddleState := 161, orbitMiddleCentral := 2, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 178, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 314. -/
def alternatingSixSchurConjugacyDatumRow314 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 98, orbitMiddleState := 141, orbitMiddleCentral := 1, conjugatorInverseState := 103, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 254, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 98, orbitMiddleState := 141, orbitMiddleCentral := 2, conjugatorInverseState := 103, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 254, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 61, orbitMiddleState := 92, orbitMiddleCentral := 0, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 240, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 61, orbitMiddleState := 92, orbitMiddleCentral := 1, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 240, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 61, orbitMiddleState := 92, orbitMiddleCentral := 2, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 240, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 98, orbitMiddleState := 141, orbitMiddleCentral := 0, conjugatorInverseState := 103, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 254, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 315. -/
def alternatingSixSchurConjugacyDatumRow315 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 12, conjugatorState := 119, orbitMiddleState := 165, orbitMiddleCentral := 3, conjugatorInverseState := 121, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 286, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 119, orbitMiddleState := 165, orbitMiddleCentral := 4, conjugatorInverseState := 121, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 286, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 119, orbitMiddleState := 165, orbitMiddleCentral := 5, conjugatorInverseState := 121, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 286, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 119, orbitMiddleState := 165, orbitMiddleCentral := 0, conjugatorInverseState := 121, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 286, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 119, orbitMiddleState := 165, orbitMiddleCentral := 1, conjugatorInverseState := 121, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 286, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 119, orbitMiddleState := 165, orbitMiddleCentral := 2, conjugatorInverseState := 121, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 286, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 316. -/
def alternatingSixSchurConjugacyDatumRow316 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 63, orbitMiddleState := 130, orbitMiddleCentral := 5, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 279, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 63, orbitMiddleState := 130, orbitMiddleCentral := 0, conjugatorInverseState := 57, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 3, orbitPenultimateState := 279, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 82, orbitMiddleState := 229, orbitMiddleCentral := 4, conjugatorInverseState := 82, conjugatorInverseCentral := 3, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 3, orbitPenultimateState := 275, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 82, orbitMiddleState := 229, orbitMiddleCentral := 5, conjugatorInverseState := 82, conjugatorInverseCentral := 3, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 3, orbitPenultimateState := 275, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 48, orbitMiddleState := 260, orbitMiddleCentral := 0, conjugatorInverseState := 45, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 4, orbitPenultimateState := 283, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 48, orbitMiddleState := 260, orbitMiddleCentral := 1, conjugatorInverseState := 45, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 4, orbitPenultimateState := 283, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 317. -/
def alternatingSixSchurConjugacyDatumRow317 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 103, orbitMiddleState := 148, orbitMiddleCentral := 1, conjugatorInverseState := 98, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 292, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 103, orbitMiddleState := 148, orbitMiddleCentral := 2, conjugatorInverseState := 98, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 292, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 73, orbitMiddleState := 109, orbitMiddleCentral := 0, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 186, orbitPenultimateCentral := 1 },
    { classIndex := 7, conjugatorState := 73, orbitMiddleState := 109, orbitMiddleCentral := 1, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 186, orbitPenultimateCentral := 2 },
    { classIndex := 8, conjugatorState := 73, orbitMiddleState := 109, orbitMiddleCentral := 2, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 186, orbitPenultimateCentral := 3 },
    { classIndex := 6, conjugatorState := 103, orbitMiddleState := 148, orbitMiddleCentral := 0, conjugatorInverseState := 98, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 292, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 318. -/
def alternatingSixSchurConjugacyDatumRow318 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 161, orbitMiddleState := 264, orbitMiddleCentral := 2, conjugatorInverseState := 192, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 161, orbitMiddleState := 264, orbitMiddleCentral := 3, conjugatorInverseState := 192, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 161, orbitMiddleState := 264, orbitMiddleCentral := 4, conjugatorInverseState := 192, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 161, orbitMiddleState := 264, orbitMiddleCentral := 5, conjugatorInverseState := 192, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 161, orbitMiddleState := 264, orbitMiddleCentral := 0, conjugatorInverseState := 192, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 161, orbitMiddleState := 264, orbitMiddleCentral := 1, conjugatorInverseState := 192, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 319. -/
def alternatingSixSchurConjugacyDatumRow319 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 89, orbitMiddleState := 173, orbitMiddleCentral := 4, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 309, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 43, orbitMiddleState := 324, orbitMiddleCentral := 2, conjugatorInverseState := 43, conjugatorInverseCentral := 5, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 5, orbitPenultimateState := 323, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 43, orbitMiddleState := 324, orbitMiddleCentral := 3, conjugatorInverseState := 43, conjugatorInverseCentral := 5, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 5, orbitPenultimateState := 323, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 51, orbitMiddleState := 209, orbitMiddleCentral := 3, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 188, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 51, orbitMiddleState := 209, orbitMiddleCentral := 4, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 188, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 89, orbitMiddleState := 173, orbitMiddleCentral := 3, conjugatorInverseState := 84, conjugatorInverseCentral := 2, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 309, orbitPenultimateCentral := 2 }
  ]


end GroupTheory
end McKayConjecture
