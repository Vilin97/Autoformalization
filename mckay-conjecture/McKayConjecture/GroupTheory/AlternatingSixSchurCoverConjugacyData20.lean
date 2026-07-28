/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 200–209

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 200. -/
def alternatingSixSchurConjugacyDatumRow200 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 6, orbitMiddleState := 101, orbitMiddleCentral := 1, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 145, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 6, orbitMiddleState := 101, orbitMiddleCentral := 2, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 145, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 156, orbitMiddleState := 341, orbitMiddleCentral := 5, conjugatorInverseState := 146, conjugatorInverseCentral := 0, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 0, orbitPenultimateState := 329, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 156, orbitMiddleState := 341, orbitMiddleCentral := 0, conjugatorInverseState := 146, conjugatorInverseCentral := 0, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 0, orbitPenultimateState := 329, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 162, orbitMiddleState := 175, orbitMiddleCentral := 5, conjugatorInverseState := 206, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 5, orbitPenultimateState := 207, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 162, orbitMiddleState := 175, orbitMiddleCentral := 0, conjugatorInverseState := 206, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 5, orbitPenultimateState := 207, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 201. -/
def alternatingSixSchurConjugacyDatumRow201 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 38, orbitMiddleState := 60, orbitMiddleCentral := 1, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 132, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 38, orbitMiddleState := 60, orbitMiddleCentral := 2, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 132, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 26, orbitMiddleState := 44, orbitMiddleCentral := 0, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 102, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 26, orbitMiddleState := 44, orbitMiddleCentral := 1, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 102, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 26, orbitMiddleState := 44, orbitMiddleCentral := 2, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 102, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 38, orbitMiddleState := 60, orbitMiddleCentral := 0, conjugatorInverseState := 41, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 16, inverseFactorRightCentral := 4, orbitPenultimateState := 132, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 202. -/
def alternatingSixSchurConjugacyDatumRow202 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 27, orbitMiddleState := 45, orbitMiddleCentral := 5, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 103, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 27, orbitMiddleState := 45, orbitMiddleCentral := 0, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 103, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 27, orbitMiddleState := 45, orbitMiddleCentral := 1, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 103, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 27, orbitMiddleState := 45, orbitMiddleCentral := 2, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 103, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 27, orbitMiddleState := 45, orbitMiddleCentral := 3, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 103, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 27, orbitMiddleState := 45, orbitMiddleCentral := 4, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 103, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 203. -/
def alternatingSixSchurConjugacyDatumRow203 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 6, orbitMiddleState := 103, orbitMiddleCentral := 1, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 148, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 6, orbitMiddleState := 103, orbitMiddleCentral := 2, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 148, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 164, orbitMiddleState := 326, orbitMiddleCentral := 0, conjugatorInverseState := 183, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 2, orbitPenultimateState := 146, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 164, orbitMiddleState := 326, orbitMiddleCentral := 1, conjugatorInverseState := 183, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 2, orbitPenultimateState := 146, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 87, orbitMiddleState := 257, orbitMiddleCentral := 3, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 104, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 87, orbitMiddleState := 257, orbitMiddleCentral := 4, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 104, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 204. -/
def alternatingSixSchurConjugacyDatumRow204 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 174, orbitMiddleState := 258, orbitMiddleCentral := 5, conjugatorInverseState := 187, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 71, orbitPenultimateCentral := 3 },
    { classIndex := 26, conjugatorState := 174, orbitMiddleState := 258, orbitMiddleCentral := 0, conjugatorInverseState := 187, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 71, orbitPenultimateCentral := 4 },
    { classIndex := 21, conjugatorState := 174, orbitMiddleState := 258, orbitMiddleCentral := 1, conjugatorInverseState := 187, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 71, orbitPenultimateCentral := 5 },
    { classIndex := 22, conjugatorState := 174, orbitMiddleState := 258, orbitMiddleCentral := 2, conjugatorInverseState := 187, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 71, orbitPenultimateCentral := 0 },
    { classIndex := 23, conjugatorState := 174, orbitMiddleState := 258, orbitMiddleCentral := 3, conjugatorInverseState := 187, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 71, orbitPenultimateCentral := 1 },
    { classIndex := 24, conjugatorState := 174, orbitMiddleState := 258, orbitMiddleCentral := 4, conjugatorInverseState := 187, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 71, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 205. -/
def alternatingSixSchurConjugacyDatumRow205 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 13, conjugatorState := 241, orbitMiddleState := 284, orbitMiddleCentral := 4, conjugatorInverseState := 224, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 4, orbitPenultimateState := 126, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 241, orbitMiddleState := 284, orbitMiddleCentral := 5, conjugatorInverseState := 224, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 4, orbitPenultimateState := 126, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 241, orbitMiddleState := 284, orbitMiddleCentral := 0, conjugatorInverseState := 224, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 4, orbitPenultimateState := 126, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 241, orbitMiddleState := 284, orbitMiddleCentral := 1, conjugatorInverseState := 224, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 4, orbitPenultimateState := 126, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 241, orbitMiddleState := 284, orbitMiddleCentral := 2, conjugatorInverseState := 224, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 4, orbitPenultimateState := 126, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 241, orbitMiddleState := 284, orbitMiddleCentral := 3, conjugatorInverseState := 224, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 4, orbitPenultimateState := 126, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 206. -/
def alternatingSixSchurConjugacyDatumRow206 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 17, orbitMiddleState := 46, orbitMiddleCentral := 5, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 104, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 97, orbitMiddleState := 143, orbitMiddleCentral := 5, conjugatorInverseState := 81, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 198, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 97, orbitMiddleState := 143, orbitMiddleCentral := 0, conjugatorInverseState := 81, conjugatorInverseCentral := 0, inverseFactorLeftState := 10, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 198, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 185, orbitMiddleState := 273, orbitMiddleCentral := 4, conjugatorInverseState := 203, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 83, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 185, orbitMiddleState := 273, orbitMiddleCentral := 5, conjugatorInverseState := 203, conjugatorInverseCentral := 5, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 83, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 17, orbitMiddleState := 46, orbitMiddleCentral := 4, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 104, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 207. -/
def alternatingSixSchurConjugacyDatumRow207 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 87, orbitMiddleState := 233, orbitMiddleCentral := 1, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 2 },
    { classIndex := 21, conjugatorState := 87, orbitMiddleState := 233, orbitMiddleCentral := 2, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 87, orbitMiddleState := 233, orbitMiddleCentral := 3, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 87, orbitMiddleState := 233, orbitMiddleCentral := 4, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 87, orbitMiddleState := 233, orbitMiddleCentral := 5, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 87, orbitMiddleState := 233, orbitMiddleCentral := 0, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 208. -/
def alternatingSixSchurConjugacyDatumRow208 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 167, orbitMiddleState := 223, orbitMiddleCentral := 2, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 299, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 167, orbitMiddleState := 223, orbitMiddleCentral := 3, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 299, orbitPenultimateCentral := 4 },
    { classIndex := 13, conjugatorState := 167, orbitMiddleState := 223, orbitMiddleCentral := 4, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 299, orbitPenultimateCentral := 5 },
    { classIndex := 14, conjugatorState := 167, orbitMiddleState := 223, orbitMiddleCentral := 5, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 299, orbitPenultimateCentral := 0 },
    { classIndex := 9, conjugatorState := 167, orbitMiddleState := 223, orbitMiddleCentral := 0, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 299, orbitPenultimateCentral := 1 },
    { classIndex := 10, conjugatorState := 167, orbitMiddleState := 223, orbitMiddleCentral := 1, conjugatorInverseState := 172, conjugatorInverseCentral := 4, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 299, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 209. -/
def alternatingSixSchurConjugacyDatumRow209 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 17, orbitMiddleState := 108, orbitMiddleCentral := 2, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 107, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 84, orbitMiddleState := 258, orbitMiddleCentral := 2, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 296, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 84, orbitMiddleState := 258, orbitMiddleCentral := 3, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 296, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 244, orbitMiddleState := 264, orbitMiddleCentral := 2, conjugatorInverseState := 256, conjugatorInverseCentral := 5, inverseFactorLeftState := 45, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 115, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 244, orbitMiddleState := 264, orbitMiddleCentral := 3, conjugatorInverseState := 256, conjugatorInverseCentral := 5, inverseFactorLeftState := 45, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 115, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 17, orbitMiddleState := 108, orbitMiddleCentral := 1, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 107, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
