/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 290–299

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 290. -/
def alternatingSixSchurConjugacyDatumRow290 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 53, orbitMiddleState := 54, orbitMiddleCentral := 2, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 144, orbitPenultimateCentral := 4 },
    { classIndex := 17, conjugatorState := 53, orbitMiddleState := 54, orbitMiddleCentral := 3, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 144, orbitPenultimateCentral := 5 },
    { classIndex := 18, conjugatorState := 53, orbitMiddleState := 54, orbitMiddleCentral := 4, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 144, orbitPenultimateCentral := 0 },
    { classIndex := 19, conjugatorState := 53, orbitMiddleState := 54, orbitMiddleCentral := 5, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 144, orbitPenultimateCentral := 1 },
    { classIndex := 20, conjugatorState := 53, orbitMiddleState := 54, orbitMiddleCentral := 0, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 144, orbitPenultimateCentral := 2 },
    { classIndex := 15, conjugatorState := 53, orbitMiddleState := 54, orbitMiddleCentral := 1, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 144, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 291. -/
def alternatingSixSchurConjugacyDatumRow291 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 140, orbitMiddleState := 244, orbitMiddleCentral := 2, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 352, orbitPenultimateCentral := 5 },
    { classIndex := 18, conjugatorState := 140, orbitMiddleState := 244, orbitMiddleCentral := 3, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 352, orbitPenultimateCentral := 0 },
    { classIndex := 19, conjugatorState := 140, orbitMiddleState := 244, orbitMiddleCentral := 4, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 352, orbitPenultimateCentral := 1 },
    { classIndex := 20, conjugatorState := 140, orbitMiddleState := 244, orbitMiddleCentral := 5, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 352, orbitPenultimateCentral := 2 },
    { classIndex := 15, conjugatorState := 140, orbitMiddleState := 244, orbitMiddleCentral := 0, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 352, orbitPenultimateCentral := 3 },
    { classIndex := 16, conjugatorState := 140, orbitMiddleState := 244, orbitMiddleCentral := 1, conjugatorInverseState := 135, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 352, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 292. -/
def alternatingSixSchurConjugacyDatumRow292 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 26, orbitMiddleState := 182, orbitMiddleCentral := 3, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 280, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 26, orbitMiddleState := 182, orbitMiddleCentral := 4, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 280, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 122, orbitMiddleState := 275, orbitMiddleCentral := 5, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 135, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 122, orbitMiddleState := 275, orbitMiddleCentral := 0, conjugatorInverseState := 124, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 135, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 48, orbitMiddleState := 333, orbitMiddleCentral := 3, conjugatorInverseState := 45, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 4, orbitPenultimateState := 332, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 48, orbitMiddleState := 333, orbitMiddleCentral := 4, conjugatorInverseState := 45, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 4, orbitPenultimateState := 332, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 293. -/
def alternatingSixSchurConjugacyDatumRow293 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 154, orbitMiddleState := 210, orbitMiddleCentral := 2, conjugatorInverseState := 149, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 3 },
    { classIndex := 6, conjugatorState := 45, orbitMiddleState := 69, orbitMiddleCentral := 0, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 148, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 45, orbitMiddleState := 69, orbitMiddleCentral := 1, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 148, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 45, orbitMiddleState := 69, orbitMiddleCentral := 2, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 148, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 154, orbitMiddleState := 210, orbitMiddleCentral := 0, conjugatorInverseState := 149, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 1 },
    { classIndex := 7, conjugatorState := 154, orbitMiddleState := 210, orbitMiddleCentral := 1, conjugatorInverseState := 149, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 294. -/
def alternatingSixSchurConjugacyDatumRow294 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 49, orbitMiddleState := 112, orbitMiddleCentral := 1, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 149, orbitPenultimateCentral := 3 },
    { classIndex := 17, conjugatorState := 49, orbitMiddleState := 112, orbitMiddleCentral := 2, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 149, orbitPenultimateCentral := 4 },
    { classIndex := 18, conjugatorState := 49, orbitMiddleState := 112, orbitMiddleCentral := 3, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 149, orbitPenultimateCentral := 5 },
    { classIndex := 19, conjugatorState := 49, orbitMiddleState := 112, orbitMiddleCentral := 4, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 149, orbitPenultimateCentral := 0 },
    { classIndex := 20, conjugatorState := 49, orbitMiddleState := 112, orbitMiddleCentral := 5, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 149, orbitPenultimateCentral := 1 },
    { classIndex := 15, conjugatorState := 49, orbitMiddleState := 112, orbitMiddleCentral := 0, conjugatorInverseState := 65, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 149, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 295. -/
def alternatingSixSchurConjugacyDatumRow295 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 84, orbitMiddleState := 90, orbitMiddleCentral := 1, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 147, orbitPenultimateCentral := 5 },
    { classIndex := 28, conjugatorState := 84, orbitMiddleState := 90, orbitMiddleCentral := 2, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 147, orbitPenultimateCentral := 0 },
    { classIndex := 27, conjugatorState := 141, orbitMiddleState := 242, orbitMiddleCentral := 3, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 358, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 141, orbitMiddleState := 242, orbitMiddleCentral := 4, conjugatorInverseState := 123, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 5, orbitPenultimateState := 358, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 28, orbitMiddleState := 297, orbitMiddleCentral := 2, conjugatorInverseState := 25, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 2, orbitPenultimateState := 296, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 28, orbitMiddleState := 297, orbitMiddleCentral := 3, conjugatorInverseState := 25, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 2, orbitPenultimateState := 296, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 296. -/
def alternatingSixSchurConjugacyDatumRow296 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 12, conjugatorState := 47, orbitMiddleState := 72, orbitMiddleCentral := 3, conjugatorInverseState := 33, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 152, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 47, orbitMiddleState := 72, orbitMiddleCentral := 4, conjugatorInverseState := 33, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 152, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 47, orbitMiddleState := 72, orbitMiddleCentral := 5, conjugatorInverseState := 33, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 152, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 47, orbitMiddleState := 72, orbitMiddleCentral := 0, conjugatorInverseState := 33, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 152, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 47, orbitMiddleState := 72, orbitMiddleCentral := 1, conjugatorInverseState := 33, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 152, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 47, orbitMiddleState := 72, orbitMiddleCentral := 2, conjugatorInverseState := 33, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 152, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 297. -/
def alternatingSixSchurConjugacyDatumRow297 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 73, orbitMiddleState := 154, orbitMiddleCentral := 4, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 298, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 73, orbitMiddleState := 154, orbitMiddleCentral := 5, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 298, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 73, orbitMiddleState := 154, orbitMiddleCentral := 0, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 298, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 73, orbitMiddleState := 154, orbitMiddleCentral := 1, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 298, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 73, orbitMiddleState := 154, orbitMiddleCentral := 2, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 298, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 73, orbitMiddleState := 154, orbitMiddleCentral := 3, conjugatorInverseState := 61, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 298, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 298. -/
def alternatingSixSchurConjugacyDatumRow298 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 121, orbitMiddleState := 168, orbitMiddleCentral := 5, conjugatorInverseState := 119, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 336, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 121, orbitMiddleState := 168, orbitMiddleCentral := 0, conjugatorInverseState := 119, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 336, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 121, orbitMiddleState := 168, orbitMiddleCentral := 1, conjugatorInverseState := 119, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 336, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 121, orbitMiddleState := 168, orbitMiddleCentral := 2, conjugatorInverseState := 119, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 336, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 121, orbitMiddleState := 168, orbitMiddleCentral := 3, conjugatorInverseState := 119, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 336, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 121, orbitMiddleState := 168, orbitMiddleCentral := 4, conjugatorInverseState := 119, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 5, orbitPenultimateState := 336, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 299. -/
def alternatingSixSchurConjugacyDatumRow299 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 203, orbitMiddleState := 293, orbitMiddleCentral := 5, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 337, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 203, orbitMiddleState := 293, orbitMiddleCentral := 0, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 337, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 203, orbitMiddleState := 293, orbitMiddleCentral := 1, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 337, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 203, orbitMiddleState := 293, orbitMiddleCentral := 2, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 337, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 203, orbitMiddleState := 293, orbitMiddleCentral := 3, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 337, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 203, orbitMiddleState := 293, orbitMiddleCentral := 4, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 337, orbitPenultimateCentral := 4 }
  ]


end GroupTheory
end McKayConjecture
