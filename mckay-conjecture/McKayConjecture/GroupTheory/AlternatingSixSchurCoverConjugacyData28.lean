/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 280–289

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 280. -/
def alternatingSixSchurConjugacyDatumRow280 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 21, orbitMiddleState := 271, orbitMiddleCentral := 0, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 182, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 21, orbitMiddleState := 271, orbitMiddleCentral := 1, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 182, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 218, orbitMiddleState := 339, orbitMiddleCentral := 5, conjugatorInverseState := 231, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 146, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 218, orbitMiddleState := 339, orbitMiddleCentral := 0, conjugatorInverseState := 231, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 146, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 15, orbitMiddleState := 254, orbitMiddleCentral := 3, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 202, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 15, orbitMiddleState := 254, orbitMiddleCentral := 4, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 202, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 281. -/
def alternatingSixSchurConjugacyDatumRow281 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 62, orbitMiddleState := 136, orbitMiddleCentral := 1, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 284, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 62, orbitMiddleState := 136, orbitMiddleCentral := 2, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 284, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 62, orbitMiddleState := 136, orbitMiddleCentral := 3, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 284, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 62, orbitMiddleState := 136, orbitMiddleCentral := 4, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 284, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 62, orbitMiddleState := 136, orbitMiddleCentral := 5, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 284, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 62, orbitMiddleState := 136, orbitMiddleCentral := 0, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 284, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 282. -/
def alternatingSixSchurConjugacyDatumRow282 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 12, conjugatorState := 39, orbitMiddleState := 61, orbitMiddleCentral := 3, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 134, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 39, orbitMiddleState := 61, orbitMiddleCentral := 4, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 134, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 39, orbitMiddleState := 61, orbitMiddleCentral := 5, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 134, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 39, orbitMiddleState := 61, orbitMiddleCentral := 0, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 134, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 39, orbitMiddleState := 61, orbitMiddleCentral := 1, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 134, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 39, orbitMiddleState := 61, orbitMiddleCentral := 2, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 134, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 283. -/
def alternatingSixSchurConjugacyDatumRow283 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 58, orbitMiddleState := 91, orbitMiddleCentral := 5, conjugatorInverseState := 53, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 0, orbitPenultimateState := 135, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 58, orbitMiddleState := 91, orbitMiddleCentral := 0, conjugatorInverseState := 53, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 0, orbitPenultimateState := 135, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 120, orbitMiddleState := 333, orbitMiddleCentral := 4, conjugatorInverseState := 148, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 154, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 120, orbitMiddleState := 333, orbitMiddleCentral := 5, conjugatorInverseState := 148, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 154, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 45, orbitMiddleState := 66, orbitMiddleCentral := 1, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 141, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 45, orbitMiddleState := 66, orbitMiddleCentral := 2, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 141, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 284. -/
def alternatingSixSchurConjugacyDatumRow284 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 88, orbitMiddleState := 178, orbitMiddleCentral := 2, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 313, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 88, orbitMiddleState := 178, orbitMiddleCentral := 3, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 313, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 88, orbitMiddleState := 178, orbitMiddleCentral := 4, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 313, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 88, orbitMiddleState := 178, orbitMiddleCentral := 5, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 313, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 88, orbitMiddleState := 178, orbitMiddleCentral := 0, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 313, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 88, orbitMiddleState := 178, orbitMiddleCentral := 1, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 313, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 285. -/
def alternatingSixSchurConjugacyDatumRow285 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 122, orbitMiddleState := 170, orbitMiddleCentral := 5, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 323, orbitPenultimateCentral := 0 },
    { classIndex := 9, conjugatorState := 122, orbitMiddleState := 170, orbitMiddleCentral := 0, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 323, orbitPenultimateCentral := 1 },
    { classIndex := 10, conjugatorState := 122, orbitMiddleState := 170, orbitMiddleCentral := 1, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 323, orbitPenultimateCentral := 2 },
    { classIndex := 11, conjugatorState := 122, orbitMiddleState := 170, orbitMiddleCentral := 2, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 323, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 122, orbitMiddleState := 170, orbitMiddleCentral := 3, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 323, orbitPenultimateCentral := 4 },
    { classIndex := 13, conjugatorState := 122, orbitMiddleState := 170, orbitMiddleCentral := 4, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 323, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 286. -/
def alternatingSixSchurConjugacyDatumRow286 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 22, orbitMiddleState := 188, orbitMiddleCentral := 1, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 285, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 22, orbitMiddleState := 188, orbitMiddleCentral := 2, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 285, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 201, orbitMiddleState := 297, orbitMiddleCentral := 0, conjugatorInverseState := 201, conjugatorInverseCentral := 3, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 3, orbitPenultimateState := 353, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 201, orbitMiddleState := 297, orbitMiddleCentral := 1, conjugatorInverseState := 201, conjugatorInverseCentral := 3, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 3, orbitPenultimateState := 353, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 33, orbitMiddleState := 212, orbitMiddleCentral := 4, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 221, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 33, orbitMiddleState := 212, orbitMiddleCentral := 5, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 221, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 287. -/
def alternatingSixSchurConjugacyDatumRow287 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 153, orbitMiddleState := 218, orbitMiddleCentral := 2, conjugatorInverseState := 139, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 277, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 153, orbitMiddleState := 218, orbitMiddleCentral := 3, conjugatorInverseState := 139, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 277, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 153, orbitMiddleState := 218, orbitMiddleCentral := 4, conjugatorInverseState := 139, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 277, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 153, orbitMiddleState := 218, orbitMiddleCentral := 5, conjugatorInverseState := 139, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 277, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 153, orbitMiddleState := 218, orbitMiddleCentral := 0, conjugatorInverseState := 139, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 277, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 153, orbitMiddleState := 218, orbitMiddleCentral := 1, conjugatorInverseState := 139, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 277, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 288. -/
def alternatingSixSchurConjugacyDatumRow288 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 135, orbitMiddleState := 186, orbitMiddleCentral := 2, conjugatorInverseState := 140, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 3 },
    { classIndex := 6, conjugatorState := 41, orbitMiddleState := 65, orbitMiddleCentral := 0, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 141, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 41, orbitMiddleState := 65, orbitMiddleCentral := 1, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 141, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 41, orbitMiddleState := 65, orbitMiddleCentral := 2, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 141, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 135, orbitMiddleState := 186, orbitMiddleCentral := 0, conjugatorInverseState := 140, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 1 },
    { classIndex := 7, conjugatorState := 135, orbitMiddleState := 186, orbitMiddleCentral := 1, conjugatorInverseState := 140, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 289. -/
def alternatingSixSchurConjugacyDatumRow289 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 49, orbitMiddleState := 272, orbitMiddleCentral := 4, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 214, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 49, orbitMiddleState := 272, orbitMiddleCentral := 5, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 214, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 41, orbitMiddleState := 202, orbitMiddleCentral := 3, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 246, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 41, orbitMiddleState := 202, orbitMiddleCentral := 4, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 246, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 233, orbitMiddleState := 350, orbitMiddleCentral := 5, conjugatorInverseState := 253, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 143, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 233, orbitMiddleState := 350, orbitMiddleCentral := 0, conjugatorInverseState := 253, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 143, orbitPenultimateCentral := 5 }
  ]


end GroupTheory
end McKayConjecture
