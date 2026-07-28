/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 240–249

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 240. -/
def alternatingSixSchurConjugacyDatumRow240 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 83, orbitMiddleState := 196, orbitMiddleCentral := 3, conjugatorInverseState := 104, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 248, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 27, orbitMiddleState := 61, orbitMiddleCentral := 3, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 135, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 27, orbitMiddleState := 61, orbitMiddleCentral := 4, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 135, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 115, orbitMiddleState := 287, orbitMiddleCentral := 2, conjugatorInverseState := 145, conjugatorInverseCentral := 3, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 3, orbitPenultimateState := 354, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 115, orbitMiddleState := 287, orbitMiddleCentral := 3, conjugatorInverseState := 145, conjugatorInverseCentral := 3, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 3, orbitPenultimateState := 354, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 83, orbitMiddleState := 196, orbitMiddleCentral := 2, conjugatorInverseState := 104, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 248, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 241. -/
def alternatingSixSchurConjugacyDatumRow241 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 157, orbitMiddleState := 195, orbitMiddleCentral := 2, conjugatorInverseState := 117, conjugatorInverseCentral := 2, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 242, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 157, orbitMiddleState := 195, orbitMiddleCentral := 3, conjugatorInverseState := 117, conjugatorInverseCentral := 2, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 242, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 157, orbitMiddleState := 195, orbitMiddleCentral := 4, conjugatorInverseState := 117, conjugatorInverseCentral := 2, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 242, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 157, orbitMiddleState := 195, orbitMiddleCentral := 5, conjugatorInverseState := 117, conjugatorInverseCentral := 2, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 242, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 157, orbitMiddleState := 195, orbitMiddleCentral := 0, conjugatorInverseState := 117, conjugatorInverseCentral := 2, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 242, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 157, orbitMiddleState := 195, orbitMiddleCentral := 1, conjugatorInverseState := 117, conjugatorInverseCentral := 2, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 242, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 242. -/
def alternatingSixSchurConjugacyDatumRow242 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 174, orbitMiddleState := 199, orbitMiddleCentral := 1, conjugatorInverseState := 187, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 351, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 39, orbitMiddleState := 66, orbitMiddleCentral := 5, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 142, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 39, orbitMiddleState := 66, orbitMiddleCentral := 0, conjugatorInverseState := 34, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 142, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 114, orbitMiddleState := 233, orbitMiddleCentral := 2, conjugatorInverseState := 129, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 318, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 114, orbitMiddleState := 233, orbitMiddleCentral := 3, conjugatorInverseState := 129, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 318, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 174, orbitMiddleState := 199, orbitMiddleCentral := 0, conjugatorInverseState := 187, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 351, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 243. -/
def alternatingSixSchurConjugacyDatumRow243 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 59, orbitMiddleState := 89, orbitMiddleCentral := 0, conjugatorInverseState := 69, conjugatorInverseCentral := 3, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 191, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 59, orbitMiddleState := 89, orbitMiddleCentral := 1, conjugatorInverseState := 69, conjugatorInverseCentral := 3, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 191, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 59, orbitMiddleState := 89, orbitMiddleCentral := 2, conjugatorInverseState := 69, conjugatorInverseCentral := 3, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 3, orbitPenultimateState := 191, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 33, orbitMiddleState := 53, orbitMiddleCentral := 0, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 121, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 33, orbitMiddleState := 53, orbitMiddleCentral := 1, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 121, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 33, orbitMiddleState := 53, orbitMiddleCentral := 2, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 121, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 244. -/
def alternatingSixSchurConjugacyDatumRow244 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 229, orbitMiddleState := 309, orbitMiddleCentral := 5, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 284, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 229, orbitMiddleState := 309, orbitMiddleCentral := 0, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 284, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 229, orbitMiddleState := 309, orbitMiddleCentral := 1, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 284, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 229, orbitMiddleState := 309, orbitMiddleCentral := 2, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 284, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 229, orbitMiddleState := 309, orbitMiddleCentral := 3, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 284, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 229, orbitMiddleState := 309, orbitMiddleCentral := 4, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 284, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 245. -/
def alternatingSixSchurConjugacyDatumRow245 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 150, orbitMiddleState := 257, orbitMiddleCentral := 1, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 359, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 150, orbitMiddleState := 257, orbitMiddleCentral := 2, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 359, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 150, orbitMiddleState := 257, orbitMiddleCentral := 3, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 359, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 150, orbitMiddleState := 257, orbitMiddleCentral := 4, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 359, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 150, orbitMiddleState := 257, orbitMiddleCentral := 5, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 359, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 150, orbitMiddleState := 257, orbitMiddleCentral := 0, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 359, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 246. -/
def alternatingSixSchurConjugacyDatumRow246 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 91, orbitMiddleState := 185, orbitMiddleCentral := 4, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 240, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 91, orbitMiddleState := 185, orbitMiddleCentral := 5, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 240, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 91, orbitMiddleState := 185, orbitMiddleCentral := 0, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 240, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 91, orbitMiddleState := 185, orbitMiddleCentral := 1, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 240, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 91, orbitMiddleState := 185, orbitMiddleCentral := 2, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 240, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 91, orbitMiddleState := 185, orbitMiddleCentral := 3, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 240, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 247. -/
def alternatingSixSchurConjugacyDatumRow247 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 206, orbitMiddleState := 257, orbitMiddleCentral := 0, conjugatorInverseState := 162, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 158, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 206, orbitMiddleState := 257, orbitMiddleCentral := 1, conjugatorInverseState := 162, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 158, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 206, orbitMiddleState := 257, orbitMiddleCentral := 2, conjugatorInverseState := 162, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 158, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 206, orbitMiddleState := 257, orbitMiddleCentral := 3, conjugatorInverseState := 162, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 158, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 206, orbitMiddleState := 257, orbitMiddleCentral := 4, conjugatorInverseState := 162, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 158, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 206, orbitMiddleState := 257, orbitMiddleCentral := 5, conjugatorInverseState := 162, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 158, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 248. -/
def alternatingSixSchurConjugacyDatumRow248 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 233, orbitMiddleState := 277, orbitMiddleCentral := 0, conjugatorInverseState := 253, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 345, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 233, orbitMiddleState := 277, orbitMiddleCentral := 1, conjugatorInverseState := 253, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 345, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 233, orbitMiddleState := 277, orbitMiddleCentral := 2, conjugatorInverseState := 253, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 345, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 173, orbitMiddleState := 230, orbitMiddleCentral := 0, conjugatorInverseState := 210, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 282, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 173, orbitMiddleState := 230, orbitMiddleCentral := 1, conjugatorInverseState := 210, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 282, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 173, orbitMiddleState := 230, orbitMiddleCentral := 2, conjugatorInverseState := 210, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 282, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 249. -/
def alternatingSixSchurConjugacyDatumRow249 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 159, orbitMiddleState := 343, orbitMiddleCentral := 0, conjugatorInverseState := 197, conjugatorInverseCentral := 5, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 5, orbitPenultimateState := 290, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 25, orbitMiddleState := 96, orbitMiddleCentral := 3, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 189, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 25, orbitMiddleState := 96, orbitMiddleCentral := 4, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 189, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 184, orbitMiddleState := 210, orbitMiddleCentral := 4, conjugatorInverseState := 169, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 5, orbitPenultimateState := 110, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 184, orbitMiddleState := 210, orbitMiddleCentral := 5, conjugatorInverseState := 169, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 5, orbitPenultimateState := 110, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 159, orbitMiddleState := 343, orbitMiddleCentral := 5, conjugatorInverseState := 197, conjugatorInverseCentral := 5, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 5, orbitPenultimateState := 290, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
