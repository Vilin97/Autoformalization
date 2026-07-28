/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 210–219

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 210. -/
def alternatingSixSchurConjugacyDatumRow210 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 149, orbitMiddleState := 293, orbitMiddleCentral := 4, conjugatorInverseState := 154, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 149, orbitMiddleState := 293, orbitMiddleCentral := 5, conjugatorInverseState := 154, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 149, orbitMiddleState := 293, orbitMiddleCentral := 0, conjugatorInverseState := 154, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 149, orbitMiddleState := 293, orbitMiddleCentral := 1, conjugatorInverseState := 154, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 149, orbitMiddleState := 293, orbitMiddleCentral := 2, conjugatorInverseState := 154, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 149, orbitMiddleState := 293, orbitMiddleCentral := 3, conjugatorInverseState := 154, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 211. -/
def alternatingSixSchurConjugacyDatumRow211 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 14, orbitMiddleState := 73, orbitMiddleCentral := 4, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 109, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 14, orbitMiddleState := 73, orbitMiddleCentral := 5, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 109, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 85, orbitMiddleState := 358, orbitMiddleCentral := 5, conjugatorInverseState := 102, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 0, orbitPenultimateState := 306, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 85, orbitMiddleState := 358, orbitMiddleCentral := 0, conjugatorInverseState := 102, conjugatorInverseCentral := 0, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 0, orbitPenultimateState := 306, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 117, orbitMiddleState := 161, orbitMiddleCentral := 1, conjugatorInverseState := 157, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 335, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 117, orbitMiddleState := 161, orbitMiddleCentral := 2, conjugatorInverseState := 157, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 2, orbitPenultimateState := 335, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 212. -/
def alternatingSixSchurConjugacyDatumRow212 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 4, orbitMiddleState := 111, orbitMiddleCentral := 4, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 156, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 187, orbitMiddleState := 281, orbitMiddleCentral := 5, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 340, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 187, orbitMiddleState := 281, orbitMiddleCentral := 0, conjugatorInverseState := 174, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 340, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 191, orbitMiddleState := 336, orbitMiddleCentral := 0, conjugatorInverseState := 198, conjugatorInverseCentral := 3, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 3, orbitPenultimateState := 167, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 191, orbitMiddleState := 336, orbitMiddleCentral := 1, conjugatorInverseState := 198, conjugatorInverseCentral := 3, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 3, orbitPenultimateState := 167, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 4, orbitMiddleState := 111, orbitMiddleCentral := 3, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 156, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 213. -/
def alternatingSixSchurConjugacyDatumRow213 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 23, conjugatorState := 100, orbitMiddleState := 250, orbitMiddleCentral := 4, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 100, orbitMiddleState := 250, orbitMiddleCentral := 5, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 100, orbitMiddleState := 250, orbitMiddleCentral := 0, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 100, orbitMiddleState := 250, orbitMiddleCentral := 1, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 2 },
    { classIndex := 21, conjugatorState := 100, orbitMiddleState := 250, orbitMiddleCentral := 2, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 100, orbitMiddleState := 250, orbitMiddleCentral := 3, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 214. -/
def alternatingSixSchurConjugacyDatumRow214 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 70, orbitMiddleState := 104, orbitMiddleCentral := 0, conjugatorInverseState := 68, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 1, orbitPenultimateState := 159, orbitPenultimateCentral := 5 },
    { classIndex := 7, conjugatorState := 70, orbitMiddleState := 104, orbitMiddleCentral := 1, conjugatorInverseState := 68, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 1, orbitPenultimateState := 159, orbitPenultimateCentral := 0 },
    { classIndex := 8, conjugatorState := 70, orbitMiddleState := 104, orbitMiddleCentral := 2, conjugatorInverseState := 68, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 1, orbitPenultimateState := 159, orbitPenultimateCentral := 1 },
    { classIndex := 6, conjugatorState := 100, orbitMiddleState := 144, orbitMiddleCentral := 0, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 227, orbitPenultimateCentral := 5 },
    { classIndex := 7, conjugatorState := 100, orbitMiddleState := 144, orbitMiddleCentral := 1, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 227, orbitPenultimateCentral := 0 },
    { classIndex := 8, conjugatorState := 100, orbitMiddleState := 144, orbitMiddleCentral := 2, conjugatorInverseState := 108, conjugatorInverseCentral := 4, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 4, orbitPenultimateState := 227, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 215. -/
def alternatingSixSchurConjugacyDatumRow215 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 127, orbitMiddleState := 176, orbitMiddleCentral := 1, conjugatorInverseState := 127, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 206, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 127, orbitMiddleState := 176, orbitMiddleCentral := 2, conjugatorInverseState := 127, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 206, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 127, orbitMiddleState := 176, orbitMiddleCentral := 3, conjugatorInverseState := 127, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 206, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 127, orbitMiddleState := 176, orbitMiddleCentral := 4, conjugatorInverseState := 127, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 206, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 127, orbitMiddleState := 176, orbitMiddleCentral := 5, conjugatorInverseState := 127, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 206, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 127, orbitMiddleState := 176, orbitMiddleCentral := 0, conjugatorInverseState := 127, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 206, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 216. -/
def alternatingSixSchurConjugacyDatumRow216 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 131, orbitMiddleState := 225, orbitMiddleCentral := 1, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 3 },
    { classIndex := 17, conjugatorState := 131, orbitMiddleState := 225, orbitMiddleCentral := 2, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 4 },
    { classIndex := 18, conjugatorState := 131, orbitMiddleState := 225, orbitMiddleCentral := 3, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 5 },
    { classIndex := 19, conjugatorState := 131, orbitMiddleState := 225, orbitMiddleCentral := 4, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 0 },
    { classIndex := 20, conjugatorState := 131, orbitMiddleState := 225, orbitMiddleCentral := 5, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 1 },
    { classIndex := 15, conjugatorState := 131, orbitMiddleState := 225, orbitMiddleCentral := 0, conjugatorInverseState := 137, conjugatorInverseCentral := 2, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 302, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 217. -/
def alternatingSixSchurConjugacyDatumRow217 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 198, orbitMiddleState := 227, orbitMiddleCentral := 3, conjugatorInverseState := 191, conjugatorInverseCentral := 3, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 43, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 0 },
    { classIndex := 20, conjugatorState := 198, orbitMiddleState := 227, orbitMiddleCentral := 4, conjugatorInverseState := 191, conjugatorInverseCentral := 3, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 43, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 1 },
    { classIndex := 15, conjugatorState := 198, orbitMiddleState := 227, orbitMiddleCentral := 5, conjugatorInverseState := 191, conjugatorInverseCentral := 3, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 43, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 2 },
    { classIndex := 16, conjugatorState := 198, orbitMiddleState := 227, orbitMiddleCentral := 0, conjugatorInverseState := 191, conjugatorInverseCentral := 3, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 43, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 3 },
    { classIndex := 17, conjugatorState := 198, orbitMiddleState := 227, orbitMiddleCentral := 1, conjugatorInverseState := 191, conjugatorInverseCentral := 3, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 43, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 4 },
    { classIndex := 18, conjugatorState := 198, orbitMiddleState := 227, orbitMiddleCentral := 2, conjugatorInverseState := 191, conjugatorInverseCentral := 3, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 43, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 218. -/
def alternatingSixSchurConjugacyDatumRow218 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 130, orbitMiddleState := 178, orbitMiddleCentral := 1, conjugatorInverseState := 155, conjugatorInverseCentral := 2, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 87, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 130, orbitMiddleState := 178, orbitMiddleCentral := 2, conjugatorInverseState := 155, conjugatorInverseCentral := 2, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 87, orbitPenultimateCentral := 3 },
    { classIndex := 24, conjugatorState := 130, orbitMiddleState := 178, orbitMiddleCentral := 3, conjugatorInverseState := 155, conjugatorInverseCentral := 2, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 87, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 130, orbitMiddleState := 178, orbitMiddleCentral := 4, conjugatorInverseState := 155, conjugatorInverseCentral := 2, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 87, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 130, orbitMiddleState := 178, orbitMiddleCentral := 5, conjugatorInverseState := 155, conjugatorInverseCentral := 2, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 87, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 130, orbitMiddleState := 178, orbitMiddleCentral := 0, conjugatorInverseState := 155, conjugatorInverseCentral := 2, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 87, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 219. -/
def alternatingSixSchurConjugacyDatumRow219 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 181, orbitMiddleState := 225, orbitMiddleCentral := 2, conjugatorInverseState := 163, conjugatorInverseCentral := 1, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 1, orbitPenultimateState := 190, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 181, orbitMiddleState := 225, orbitMiddleCentral := 3, conjugatorInverseState := 163, conjugatorInverseCentral := 1, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 1, orbitPenultimateState := 190, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 181, orbitMiddleState := 225, orbitMiddleCentral := 4, conjugatorInverseState := 163, conjugatorInverseCentral := 1, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 1, orbitPenultimateState := 190, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 181, orbitMiddleState := 225, orbitMiddleCentral := 5, conjugatorInverseState := 163, conjugatorInverseCentral := 1, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 1, orbitPenultimateState := 190, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 181, orbitMiddleState := 225, orbitMiddleCentral := 0, conjugatorInverseState := 163, conjugatorInverseCentral := 1, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 1, orbitPenultimateState := 190, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 181, orbitMiddleState := 225, orbitMiddleCentral := 1, conjugatorInverseState := 163, conjugatorInverseCentral := 1, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 1, orbitPenultimateState := 190, orbitPenultimateCentral := 4 }
  ]


end GroupTheory
end McKayConjecture
