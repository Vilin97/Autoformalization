/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 230–239

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 230. -/
def alternatingSixSchurConjugacyDatumRow230 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 169, orbitMiddleState := 251, orbitMiddleCentral := 1, conjugatorInverseState := 184, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 252, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 169, orbitMiddleState := 251, orbitMiddleCentral := 2, conjugatorInverseState := 184, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 252, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 169, orbitMiddleState := 251, orbitMiddleCentral := 3, conjugatorInverseState := 184, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 252, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 169, orbitMiddleState := 251, orbitMiddleCentral := 4, conjugatorInverseState := 184, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 252, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 169, orbitMiddleState := 251, orbitMiddleCentral := 5, conjugatorInverseState := 184, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 252, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 169, orbitMiddleState := 251, orbitMiddleCentral := 0, conjugatorInverseState := 184, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 252, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 231. -/
def alternatingSixSchurConjugacyDatumRow231 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 131, orbitMiddleState := 271, orbitMiddleCentral := 3, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 183, orbitPenultimateCentral := 2 },
    { classIndex := 25, conjugatorState := 131, orbitMiddleState := 271, orbitMiddleCentral := 4, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 183, orbitPenultimateCentral := 3 },
    { classIndex := 26, conjugatorState := 131, orbitMiddleState := 271, orbitMiddleCentral := 5, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 183, orbitPenultimateCentral := 4 },
    { classIndex := 21, conjugatorState := 131, orbitMiddleState := 271, orbitMiddleCentral := 0, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 183, orbitPenultimateCentral := 5 },
    { classIndex := 22, conjugatorState := 131, orbitMiddleState := 271, orbitMiddleCentral := 1, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 183, orbitPenultimateCentral := 0 },
    { classIndex := 23, conjugatorState := 131, orbitMiddleState := 271, orbitMiddleCentral := 2, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 183, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 232. -/
def alternatingSixSchurConjugacyDatumRow232 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 116, orbitMiddleState := 162, orbitMiddleCentral := 2, conjugatorInverseState := 116, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 127, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 116, orbitMiddleState := 162, orbitMiddleCentral := 3, conjugatorInverseState := 116, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 127, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 116, orbitMiddleState := 162, orbitMiddleCentral := 4, conjugatorInverseState := 116, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 127, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 116, orbitMiddleState := 162, orbitMiddleCentral := 5, conjugatorInverseState := 116, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 127, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 116, orbitMiddleState := 162, orbitMiddleCentral := 0, conjugatorInverseState := 116, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 127, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 116, orbitMiddleState := 162, orbitMiddleCentral := 1, conjugatorInverseState := 116, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 127, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 233. -/
def alternatingSixSchurConjugacyDatumRow233 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 190, orbitMiddleState := 220, orbitMiddleCentral := 2, conjugatorInverseState := 177, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 116, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 190, orbitMiddleState := 220, orbitMiddleCentral := 3, conjugatorInverseState := 177, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 116, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 190, orbitMiddleState := 220, orbitMiddleCentral := 4, conjugatorInverseState := 177, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 116, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 190, orbitMiddleState := 220, orbitMiddleCentral := 5, conjugatorInverseState := 177, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 116, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 190, orbitMiddleState := 220, orbitMiddleCentral := 0, conjugatorInverseState := 177, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 116, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 190, orbitMiddleState := 220, orbitMiddleCentral := 1, conjugatorInverseState := 177, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 116, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 234. -/
def alternatingSixSchurConjugacyDatumRow234 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 113, orbitMiddleState := 161, orbitMiddleCentral := 4, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 128, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 113, orbitMiddleState := 161, orbitMiddleCentral := 5, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 128, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 113, orbitMiddleState := 161, orbitMiddleCentral := 0, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 128, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 113, orbitMiddleState := 161, orbitMiddleCentral := 1, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 128, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 113, orbitMiddleState := 161, orbitMiddleCentral := 2, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 128, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 113, orbitMiddleState := 161, orbitMiddleCentral := 3, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 128, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 235. -/
def alternatingSixSchurConjugacyDatumRow235 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 35, orbitMiddleState := 36, orbitMiddleCentral := 3, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 88, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 35, orbitMiddleState := 36, orbitMiddleCentral := 4, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 88, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 35, orbitMiddleState := 36, orbitMiddleCentral := 5, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 88, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 35, orbitMiddleState := 36, orbitMiddleCentral := 0, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 88, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 35, orbitMiddleState := 36, orbitMiddleCentral := 1, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 88, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 35, orbitMiddleState := 36, orbitMiddleCentral := 2, conjugatorInverseState := 35, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 88, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 236. -/
def alternatingSixSchurConjugacyDatumRow236 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 299, orbitMiddleState := 306, orbitMiddleCentral := 5, conjugatorInverseState := 281, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 299, orbitMiddleState := 306, orbitMiddleCentral := 0, conjugatorInverseState := 281, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 299, orbitMiddleState := 306, orbitMiddleCentral := 1, conjugatorInverseState := 281, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 299, orbitMiddleState := 306, orbitMiddleCentral := 2, conjugatorInverseState := 281, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 299, orbitMiddleState := 306, orbitMiddleCentral := 3, conjugatorInverseState := 281, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 299, orbitMiddleState := 306, orbitMiddleCentral := 4, conjugatorInverseState := 281, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 237. -/
def alternatingSixSchurConjugacyDatumRow237 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 101, orbitMiddleState := 145, orbitMiddleCentral := 1, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 121, orbitPenultimateCentral := 5 },
    { classIndex := 8, conjugatorState := 101, orbitMiddleState := 145, orbitMiddleCentral := 2, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 121, orbitPenultimateCentral := 0 },
    { classIndex := 6, conjugatorState := 64, orbitMiddleState := 97, orbitMiddleCentral := 0, conjugatorInverseState := 66, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 180, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 64, orbitMiddleState := 97, orbitMiddleCentral := 1, conjugatorInverseState := 66, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 180, orbitPenultimateCentral := 5 },
    { classIndex := 8, conjugatorState := 64, orbitMiddleState := 97, orbitMiddleCentral := 2, conjugatorInverseState := 66, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 180, orbitPenultimateCentral := 0 },
    { classIndex := 6, conjugatorState := 101, orbitMiddleState := 145, orbitMiddleCentral := 0, conjugatorInverseState := 93, conjugatorInverseCentral := 4, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 121, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 238. -/
def alternatingSixSchurConjugacyDatumRow238 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 219, orbitMiddleState := 265, orbitMiddleCentral := 0, conjugatorInverseState := 247, conjugatorInverseCentral := 4, inverseFactorLeftState := 41, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 4, orbitPenultimateState := 298, orbitPenultimateCentral := 5 },
    { classIndex := 7, conjugatorState := 219, orbitMiddleState := 265, orbitMiddleCentral := 1, conjugatorInverseState := 247, conjugatorInverseCentral := 4, inverseFactorLeftState := 41, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 4, orbitPenultimateState := 298, orbitPenultimateCentral := 0 },
    { classIndex := 8, conjugatorState := 219, orbitMiddleState := 265, orbitMiddleCentral := 2, conjugatorInverseState := 247, conjugatorInverseCentral := 4, inverseFactorLeftState := 41, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 4, orbitPenultimateState := 298, orbitPenultimateCentral := 1 },
    { classIndex := 6, conjugatorState := 166, orbitMiddleState := 222, orbitMiddleCentral := 0, conjugatorInverseState := 186, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 298, orbitPenultimateCentral := 1 },
    { classIndex := 7, conjugatorState := 166, orbitMiddleState := 222, orbitMiddleCentral := 1, conjugatorInverseState := 186, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 298, orbitPenultimateCentral := 2 },
    { classIndex := 8, conjugatorState := 166, orbitMiddleState := 222, orbitMiddleCentral := 2, conjugatorInverseState := 186, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 298, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 239. -/
def alternatingSixSchurConjugacyDatumRow239 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 111, orbitMiddleState := 195, orbitMiddleCentral := 1, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 317, orbitPenultimateCentral := 0 },
    { classIndex := 17, conjugatorState := 111, orbitMiddleState := 195, orbitMiddleCentral := 2, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 317, orbitPenultimateCentral := 1 },
    { classIndex := 18, conjugatorState := 111, orbitMiddleState := 195, orbitMiddleCentral := 3, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 317, orbitPenultimateCentral := 2 },
    { classIndex := 19, conjugatorState := 111, orbitMiddleState := 195, orbitMiddleCentral := 4, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 317, orbitPenultimateCentral := 3 },
    { classIndex := 20, conjugatorState := 111, orbitMiddleState := 195, orbitMiddleCentral := 5, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 317, orbitPenultimateCentral := 4 },
    { classIndex := 15, conjugatorState := 111, orbitMiddleState := 195, orbitMiddleCentral := 0, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 317, orbitPenultimateCentral := 5 }
  ]


end GroupTheory
end McKayConjecture
