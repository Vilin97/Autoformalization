/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 300–309

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 300. -/
def alternatingSixSchurConjugacyDatumRow300 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 188, orbitMiddleState := 241, orbitMiddleCentral := 1, conjugatorInverseState := 194, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 321, orbitPenultimateCentral := 2 },
    { classIndex := 8, conjugatorState := 188, orbitMiddleState := 241, orbitMiddleCentral := 2, conjugatorInverseState := 194, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 321, orbitPenultimateCentral := 3 },
    { classIndex := 6, conjugatorState := 140, orbitMiddleState := 192, orbitMiddleCentral := 0, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 313, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 140, orbitMiddleState := 192, orbitMiddleCentral := 1, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 313, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 140, orbitMiddleState := 192, orbitMiddleCentral := 2, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 313, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 188, orbitMiddleState := 241, orbitMiddleCentral := 0, conjugatorInverseState := 194, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 321, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 301. -/
def alternatingSixSchurConjugacyDatumRow301 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 78, orbitMiddleState := 110, orbitMiddleCentral := 0, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 261, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 78, orbitMiddleState := 110, orbitMiddleCentral := 1, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 261, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 67, orbitMiddleState := 203, orbitMiddleCentral := 4, conjugatorInverseState := 54, conjugatorInverseCentral := 4, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 4, orbitPenultimateState := 256, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 67, orbitMiddleState := 203, orbitMiddleCentral := 5, conjugatorInverseState := 54, conjugatorInverseCentral := 4, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 4, orbitPenultimateState := 256, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 59, orbitMiddleState := 278, orbitMiddleCentral := 0, conjugatorInverseState := 69, conjugatorInverseCentral := 3, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 161, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 59, orbitMiddleState := 278, orbitMiddleCentral := 1, conjugatorInverseState := 69, conjugatorInverseCentral := 3, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 161, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 302. -/
def alternatingSixSchurConjugacyDatumRow302 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 35, orbitMiddleState := 76, orbitMiddleCentral := 3, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 161, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 35, orbitMiddleState := 76, orbitMiddleCentral := 4, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 161, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 93, orbitMiddleState := 299, orbitMiddleCentral := 2, conjugatorInverseState := 101, conjugatorInverseCentral := 4, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 4, orbitPenultimateState := 332, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 93, orbitMiddleState := 299, orbitMiddleCentral := 3, conjugatorInverseState := 101, conjugatorInverseCentral := 4, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 4, orbitPenultimateState := 332, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 68, orbitMiddleState := 226, orbitMiddleCentral := 1, conjugatorInverseState := 70, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 271, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 68, orbitMiddleState := 226, orbitMiddleCentral := 2, conjugatorInverseState := 70, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 271, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 303. -/
def alternatingSixSchurConjugacyDatumRow303 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 193, orbitMiddleState := 245, orbitMiddleCentral := 0, conjugatorInverseState := 211, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 352, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 193, orbitMiddleState := 245, orbitMiddleCentral := 1, conjugatorInverseState := 211, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 352, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 193, orbitMiddleState := 245, orbitMiddleCentral := 2, conjugatorInverseState := 211, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 352, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 182, orbitMiddleState := 237, orbitMiddleCentral := 2, conjugatorInverseState := 213, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 2, orbitPenultimateState := 355, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 182, orbitMiddleState := 237, orbitMiddleCentral := 3, conjugatorInverseState := 213, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 2, orbitPenultimateState := 355, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 182, orbitMiddleState := 237, orbitMiddleCentral := 4, conjugatorInverseState := 213, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 2, orbitPenultimateState := 355, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 304. -/
def alternatingSixSchurConjugacyDatumRow304 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 74, orbitMiddleState := 149, orbitMiddleCentral := 4, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 294, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 54, orbitMiddleState := 326, orbitMiddleCentral := 5, conjugatorInverseState := 67, conjugatorInverseCentral := 4, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 4, orbitPenultimateState := 339, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 54, orbitMiddleState := 326, orbitMiddleCentral := 0, conjugatorInverseState := 67, conjugatorInverseCentral := 4, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 4, orbitPenultimateState := 339, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 40, orbitMiddleState := 234, orbitMiddleCentral := 2, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 162, orbitPenultimateCentral := 5 },
    { classIndex := 28, conjugatorState := 40, orbitMiddleState := 234, orbitMiddleCentral := 3, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 162, orbitPenultimateCentral := 0 },
    { classIndex := 27, conjugatorState := 74, orbitMiddleState := 149, orbitMiddleCentral := 3, conjugatorInverseState := 56, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 3, orbitPenultimateState := 294, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 305. -/
def alternatingSixSchurConjugacyDatumRow305 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 50, orbitMiddleState := 81, orbitMiddleCentral := 5, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 226, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 50, orbitMiddleState := 81, orbitMiddleCentral := 0, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 226, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 92, orbitMiddleState := 208, orbitMiddleCentral := 2, conjugatorInverseState := 88, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 303, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 92, orbitMiddleState := 208, orbitMiddleCentral := 3, conjugatorInverseState := 88, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 303, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 150, orbitMiddleState := 197, orbitMiddleCentral := 3, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 350, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 150, orbitMiddleState := 197, orbitMiddleCentral := 4, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 350, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 306. -/
def alternatingSixSchurConjugacyDatumRow306 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 27, orbitMiddleState := 211, orbitMiddleCentral := 2, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 299, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 85, orbitMiddleState := 282, orbitMiddleCentral := 3, conjugatorInverseState := 102, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 0, orbitPenultimateState := 275, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 85, orbitMiddleState := 282, orbitMiddleCentral := 4, conjugatorInverseState := 102, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 0, orbitPenultimateState := 275, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 100, orbitMiddleState := 189, orbitMiddleCentral := 4, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 212, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 100, orbitMiddleState := 189, orbitMiddleCentral := 5, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 212, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 27, orbitMiddleState := 211, orbitMiddleCentral := 1, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 299, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 307. -/
def alternatingSixSchurConjugacyDatumRow307 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 149, orbitMiddleState := 204, orbitMiddleCentral := 2, conjugatorInverseState := 154, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 301, orbitPenultimateCentral := 4 },
    { classIndex := 6, conjugatorState := 208, orbitMiddleState := 259, orbitMiddleCentral := 0, conjugatorInverseState := 202, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 298, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 208, orbitMiddleState := 259, orbitMiddleCentral := 1, conjugatorInverseState := 202, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 298, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 208, orbitMiddleState := 259, orbitMiddleCentral := 2, conjugatorInverseState := 202, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 298, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 149, orbitMiddleState := 204, orbitMiddleCentral := 0, conjugatorInverseState := 154, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 301, orbitPenultimateCentral := 2 },
    { classIndex := 7, conjugatorState := 149, orbitMiddleState := 204, orbitMiddleCentral := 1, conjugatorInverseState := 154, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 301, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 308. -/
def alternatingSixSchurConjugacyDatumRow308 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 141, orbitMiddleState := 198, orbitMiddleCentral := 4, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 215, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 107, orbitMiddleState := 185, orbitMiddleCentral := 5, conjugatorInverseState := 87, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 316, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 107, orbitMiddleState := 185, orbitMiddleCentral := 0, conjugatorInverseState := 87, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 316, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 80, orbitMiddleState := 115, orbitMiddleCentral := 5, conjugatorInverseState := 75, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 129, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 80, orbitMiddleState := 115, orbitMiddleCentral := 0, conjugatorInverseState := 75, conjugatorInverseCentral := 2, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 129, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 141, orbitMiddleState := 198, orbitMiddleCentral := 3, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 215, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 309. -/
def alternatingSixSchurConjugacyDatumRow309 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 50, orbitMiddleState := 166, orbitMiddleCentral := 5, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 306, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 23, orbitMiddleState := 282, orbitMiddleCentral := 2, conjugatorInverseState := 26, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 2, orbitPenultimateState := 281, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 23, orbitMiddleState := 282, orbitMiddleCentral := 3, conjugatorInverseState := 26, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 2, orbitPenultimateState := 281, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 105, orbitMiddleState := 170, orbitMiddleCentral := 5, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 123, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 105, orbitMiddleState := 170, orbitMiddleCentral := 0, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 123, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 50, orbitMiddleState := 166, orbitMiddleCentral := 4, conjugatorInverseState := 55, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 0, orbitPenultimateState := 306, orbitPenultimateCentral := 4 }
  ]


end GroupTheory
end McKayConjecture
