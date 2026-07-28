/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 190–199

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 190. -/
def alternatingSixSchurConjugacyDatumRow190 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 13, orbitMiddleState := 117, orbitMiddleCentral := 3, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 164, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 13, orbitMiddleState := 117, orbitMiddleCentral := 4, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 164, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 210, orbitMiddleState := 268, orbitMiddleCentral := 4, conjugatorInverseState := 173, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 81, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 210, orbitMiddleState := 268, orbitMiddleCentral := 5, conjugatorInverseState := 173, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 5, orbitPenultimateState := 81, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 68, orbitMiddleState := 351, orbitMiddleCentral := 3, conjugatorInverseState := 70, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 305, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 68, orbitMiddleState := 351, orbitMiddleCentral := 4, conjugatorInverseState := 70, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 305, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 191. -/
def alternatingSixSchurConjugacyDatumRow191 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 42, orbitMiddleState := 65, orbitMiddleCentral := 1, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 64, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 42, orbitMiddleState := 65, orbitMiddleCentral := 2, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 64, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 42, orbitMiddleState := 65, orbitMiddleCentral := 3, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 64, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 42, orbitMiddleState := 65, orbitMiddleCentral := 4, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 64, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 42, orbitMiddleState := 65, orbitMiddleCentral := 5, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 64, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 42, orbitMiddleState := 65, orbitMiddleCentral := 0, conjugatorInverseState := 36, conjugatorInverseCentral := 1, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 64, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 192. -/
def alternatingSixSchurConjugacyDatumRow192 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 165, orbitMiddleState := 242, orbitMiddleCentral := 2, conjugatorInverseState := 209, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 63, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 165, orbitMiddleState := 242, orbitMiddleCentral := 3, conjugatorInverseState := 209, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 63, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 165, orbitMiddleState := 242, orbitMiddleCentral := 4, conjugatorInverseState := 209, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 63, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 165, orbitMiddleState := 242, orbitMiddleCentral := 5, conjugatorInverseState := 209, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 63, orbitPenultimateCentral := 3 },
    { classIndex := 24, conjugatorState := 165, orbitMiddleState := 242, orbitMiddleCentral := 0, conjugatorInverseState := 209, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 63, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 165, orbitMiddleState := 242, orbitMiddleCentral := 1, conjugatorInverseState := 209, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 63, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 193. -/
def alternatingSixSchurConjugacyDatumRow193 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 7, orbitMiddleState := 194, orbitMiddleCentral := 3, conjugatorInverseState := 7, conjugatorInverseCentral := 3, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 3, orbitPenultimateState := 141, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 163, orbitMiddleState := 168, orbitMiddleCentral := 1, conjugatorInverseState := 181, conjugatorInverseCentral := 1, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 1, orbitPenultimateState := 180, orbitPenultimateCentral := 5 },
    { classIndex := 28, conjugatorState := 163, orbitMiddleState := 168, orbitMiddleCentral := 2, conjugatorInverseState := 181, conjugatorInverseCentral := 1, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 1, orbitPenultimateState := 180, orbitPenultimateCentral := 0 },
    { classIndex := 27, conjugatorState := 124, orbitMiddleState := 276, orbitMiddleCentral := 4, conjugatorInverseState := 122, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 349, orbitPenultimateCentral := 5 },
    { classIndex := 28, conjugatorState := 124, orbitMiddleState := 276, orbitMiddleCentral := 5, conjugatorInverseState := 122, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 349, orbitPenultimateCentral := 0 },
    { classIndex := 27, conjugatorState := 7, orbitMiddleState := 194, orbitMiddleCentral := 2, conjugatorInverseState := 7, conjugatorInverseCentral := 3, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 3, orbitPenultimateState := 141, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 194. -/
def alternatingSixSchurConjugacyDatumRow194 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 172, orbitMiddleState := 228, orbitMiddleCentral := 2, conjugatorInverseState := 167, conjugatorInverseCentral := 4, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 214, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 172, orbitMiddleState := 228, orbitMiddleCentral := 3, conjugatorInverseState := 167, conjugatorInverseCentral := 4, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 214, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 172, orbitMiddleState := 228, orbitMiddleCentral := 4, conjugatorInverseState := 167, conjugatorInverseCentral := 4, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 214, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 172, orbitMiddleState := 228, orbitMiddleCentral := 5, conjugatorInverseState := 167, conjugatorInverseCentral := 4, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 214, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 172, orbitMiddleState := 228, orbitMiddleCentral := 0, conjugatorInverseState := 167, conjugatorInverseCentral := 4, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 214, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 172, orbitMiddleState := 228, orbitMiddleCentral := 1, conjugatorInverseState := 167, conjugatorInverseCentral := 4, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 214, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 195. -/
def alternatingSixSchurConjugacyDatumRow195 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 73, orbitMiddleState := 211, orbitMiddleCentral := 4, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 156, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 73, orbitMiddleState := 211, orbitMiddleCentral := 5, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 156, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 73, orbitMiddleState := 211, orbitMiddleCentral := 0, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 156, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 73, orbitMiddleState := 211, orbitMiddleCentral := 1, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 156, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 73, orbitMiddleState := 211, orbitMiddleCentral := 2, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 156, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 73, orbitMiddleState := 211, orbitMiddleCentral := 3, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 156, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 196. -/
def alternatingSixSchurConjugacyDatumRow196 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 48, orbitMiddleState := 74, orbitMiddleCentral := 1, conjugatorInverseState := 45, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 4, orbitPenultimateState := 157, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 48, orbitMiddleState := 74, orbitMiddleCentral := 2, conjugatorInverseState := 45, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 4, orbitPenultimateState := 157, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 25, orbitMiddleState := 42, orbitMiddleCentral := 0, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 99, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 25, orbitMiddleState := 42, orbitMiddleCentral := 1, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 99, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 25, orbitMiddleState := 42, orbitMiddleCentral := 2, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 99, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 48, orbitMiddleState := 74, orbitMiddleCentral := 0, conjugatorInverseState := 45, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 4, orbitPenultimateState := 157, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 197. -/
def alternatingSixSchurConjugacyDatumRow197 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 29, orbitMiddleState := 43, orbitMiddleCentral := 0, conjugatorInverseState := 17, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 100, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 140, orbitMiddleState := 277, orbitMiddleCentral := 4, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 342, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 140, orbitMiddleState := 277, orbitMiddleCentral := 5, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 342, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 132, orbitMiddleState := 309, orbitMiddleCentral := 1, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 320, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 132, orbitMiddleState := 309, orbitMiddleCentral := 2, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 320, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 29, orbitMiddleState := 43, orbitMiddleCentral := 5, conjugatorInverseState := 17, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 100, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 198. -/
def alternatingSixSchurConjugacyDatumRow198 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 13, conjugatorState := 259, orbitMiddleState := 296, orbitMiddleCentral := 4, conjugatorInverseState := 228, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 4, orbitPenultimateState := 351, orbitPenultimateCentral := 5 },
    { classIndex := 14, conjugatorState := 259, orbitMiddleState := 296, orbitMiddleCentral := 5, conjugatorInverseState := 228, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 4, orbitPenultimateState := 351, orbitPenultimateCentral := 0 },
    { classIndex := 9, conjugatorState := 259, orbitMiddleState := 296, orbitMiddleCentral := 0, conjugatorInverseState := 228, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 4, orbitPenultimateState := 351, orbitPenultimateCentral := 1 },
    { classIndex := 10, conjugatorState := 259, orbitMiddleState := 296, orbitMiddleCentral := 1, conjugatorInverseState := 228, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 4, orbitPenultimateState := 351, orbitPenultimateCentral := 2 },
    { classIndex := 11, conjugatorState := 259, orbitMiddleState := 296, orbitMiddleCentral := 2, conjugatorInverseState := 228, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 4, orbitPenultimateState := 351, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 259, orbitMiddleState := 296, orbitMiddleCentral := 3, conjugatorInverseState := 228, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 33, inverseFactorRightCentral := 4, orbitPenultimateState := 351, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 199. -/
def alternatingSixSchurConjugacyDatumRow199 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 44, orbitMiddleState := 68, orbitMiddleCentral := 5, conjugatorInverseState := 31, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 146, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 44, orbitMiddleState := 68, orbitMiddleCentral := 0, conjugatorInverseState := 31, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 146, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 44, orbitMiddleState := 68, orbitMiddleCentral := 1, conjugatorInverseState := 31, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 146, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 44, orbitMiddleState := 68, orbitMiddleCentral := 2, conjugatorInverseState := 31, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 146, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 44, orbitMiddleState := 68, orbitMiddleCentral := 3, conjugatorInverseState := 31, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 146, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 44, orbitMiddleState := 68, orbitMiddleCentral := 4, conjugatorInverseState := 31, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 146, orbitPenultimateCentral := 4 }
  ]


end GroupTheory
end McKayConjecture
