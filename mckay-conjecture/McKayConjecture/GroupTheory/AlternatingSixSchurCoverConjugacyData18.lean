/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 180–189

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 180. -/
def alternatingSixSchurConjugacyDatumRow180 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 2, orbitMiddleState := 131, orbitMiddleCentral := 3, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 131, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 218, orbitMiddleState := 294, orbitMiddleCentral := 0, conjugatorInverseState := 231, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 288, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 218, orbitMiddleState := 294, orbitMiddleCentral := 1, conjugatorInverseState := 231, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 288, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 212, orbitMiddleState := 317, orbitMiddleCentral := 3, conjugatorInverseState := 170, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 5, orbitPenultimateState := 313, orbitPenultimateCentral := 5 },
    { classIndex := 28, conjugatorState := 212, orbitMiddleState := 317, orbitMiddleCentral := 4, conjugatorInverseState := 170, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 5, orbitPenultimateState := 313, orbitPenultimateCentral := 0 },
    { classIndex := 27, conjugatorState := 2, orbitMiddleState := 131, orbitMiddleCentral := 2, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 131, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 181. -/
def alternatingSixSchurConjugacyDatumRow181 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 103, orbitMiddleState := 332, orbitMiddleCentral := 1, conjugatorInverseState := 98, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 280, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 103, orbitMiddleState := 332, orbitMiddleCentral := 2, conjugatorInverseState := 98, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 280, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 21, orbitMiddleState := 139, orbitMiddleCentral := 3, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 180, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 21, orbitMiddleState := 139, orbitMiddleCentral := 4, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 180, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 262, orbitMiddleState := 315, orbitMiddleCentral := 1, conjugatorInverseState := 280, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 50, inverseFactorRightCentral := 4, orbitPenultimateState := 279, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 262, orbitMiddleState := 315, orbitMiddleCentral := 2, conjugatorInverseState := 280, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 50, inverseFactorRightCentral := 4, orbitPenultimateState := 279, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 182. -/
def alternatingSixSchurConjugacyDatumRow182 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 101, orbitMiddleState := 251, orbitMiddleCentral := 4, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 201, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 101, orbitMiddleState := 251, orbitMiddleCentral := 5, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 201, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 101, orbitMiddleState := 251, orbitMiddleCentral := 0, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 201, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 101, orbitMiddleState := 251, orbitMiddleCentral := 1, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 201, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 101, orbitMiddleState := 251, orbitMiddleCentral := 2, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 201, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 101, orbitMiddleState := 251, orbitMiddleCentral := 3, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 201, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 183. -/
def alternatingSixSchurConjugacyDatumRow183 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 23, conjugatorState := 61, orbitMiddleState := 185, orbitMiddleCentral := 4, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 60, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 61, orbitMiddleState := 185, orbitMiddleCentral := 5, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 60, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 61, orbitMiddleState := 185, orbitMiddleCentral := 0, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 60, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 61, orbitMiddleState := 185, orbitMiddleCentral := 1, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 60, orbitPenultimateCentral := 2 },
    { classIndex := 21, conjugatorState := 61, orbitMiddleState := 185, orbitMiddleCentral := 2, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 60, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 61, orbitMiddleState := 185, orbitMiddleCentral := 3, conjugatorInverseState := 73, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 60, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 184. -/
def alternatingSixSchurConjugacyDatumRow184 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 19, orbitMiddleState := 38, orbitMiddleCentral := 5, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 90, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 19, orbitMiddleState := 38, orbitMiddleCentral := 0, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 90, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 204, orbitMiddleState := 262, orbitMiddleCentral := 0, conjugatorInverseState := 178, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 273, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 204, orbitMiddleState := 262, orbitMiddleCentral := 1, conjugatorInverseState := 178, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 273, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 136, orbitMiddleState := 331, orbitMiddleCentral := 4, conjugatorInverseState := 150, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 258, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 136, orbitMiddleState := 331, orbitMiddleCentral := 5, conjugatorInverseState := 150, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 258, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 185. -/
def alternatingSixSchurConjugacyDatumRow185 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 23, orbitMiddleState := 260, orbitMiddleCentral := 3, conjugatorInverseState := 26, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 2, orbitPenultimateState := 186, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 88, orbitMiddleState := 300, orbitMiddleCentral := 2, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 347, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 88, orbitMiddleState := 300, orbitMiddleCentral := 3, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 347, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 78, orbitMiddleState := 306, orbitMiddleCentral := 1, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 309, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 78, orbitMiddleState := 306, orbitMiddleCentral := 2, conjugatorInverseState := 86, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 309, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 23, orbitMiddleState := 260, orbitMiddleCentral := 2, conjugatorInverseState := 26, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 2, orbitPenultimateState := 186, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 186. -/
def alternatingSixSchurConjugacyDatumRow186 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 140, orbitMiddleState := 288, orbitMiddleCentral := 4, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 140, orbitMiddleState := 288, orbitMiddleCentral := 5, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 140, orbitMiddleState := 288, orbitMiddleCentral := 0, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 140, orbitMiddleState := 288, orbitMiddleCentral := 1, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 140, orbitMiddleState := 288, orbitMiddleCentral := 2, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 3 },
    { classIndex := 24, conjugatorState := 140, orbitMiddleState := 288, orbitMiddleCentral := 3, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 187. -/
def alternatingSixSchurConjugacyDatumRow187 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 22, orbitMiddleState := 72, orbitMiddleCentral := 0, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 153, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 22, orbitMiddleState := 72, orbitMiddleCentral := 1, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 153, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 246, orbitMiddleState := 263, orbitMiddleCentral := 3, conjugatorInverseState := 251, conjugatorInverseCentral := 2, inverseFactorLeftState := 43, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 2, orbitPenultimateState := 265, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 246, orbitMiddleState := 263, orbitMiddleCentral := 4, conjugatorInverseState := 251, conjugatorInverseCentral := 2, inverseFactorLeftState := 43, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 2, orbitPenultimateState := 265, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 79, orbitMiddleState := 320, orbitMiddleCentral := 3, conjugatorInverseState := 99, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 285, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 79, orbitMiddleState := 320, orbitMiddleCentral := 4, conjugatorInverseState := 99, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 285, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 188. -/
def alternatingSixSchurConjugacyDatumRow188 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 24, orbitMiddleState := 40, orbitMiddleCentral := 5, conjugatorInverseState := 18, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 95, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 24, orbitMiddleState := 40, orbitMiddleCentral := 0, conjugatorInverseState := 18, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 95, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 24, orbitMiddleState := 40, orbitMiddleCentral := 1, conjugatorInverseState := 18, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 95, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 24, orbitMiddleState := 40, orbitMiddleCentral := 2, conjugatorInverseState := 18, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 95, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 24, orbitMiddleState := 40, orbitMiddleCentral := 3, conjugatorInverseState := 18, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 95, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 24, orbitMiddleState := 40, orbitMiddleCentral := 4, conjugatorInverseState := 18, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 95, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 189. -/
def alternatingSixSchurConjugacyDatumRow189 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 77, orbitMiddleState := 219, orbitMiddleCentral := 4, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 164, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 77, orbitMiddleState := 219, orbitMiddleCentral := 5, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 164, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 77, orbitMiddleState := 219, orbitMiddleCentral := 0, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 164, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 77, orbitMiddleState := 219, orbitMiddleCentral := 1, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 164, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 77, orbitMiddleState := 219, orbitMiddleCentral := 2, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 164, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 77, orbitMiddleState := 219, orbitMiddleCentral := 3, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 164, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
