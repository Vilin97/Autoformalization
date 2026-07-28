/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 70–79

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 70. -/
def alternatingSixSchurConjugacyDatumRow070 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 228, orbitMiddleState := 334, orbitMiddleCentral := 5, conjugatorInverseState := 259, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 227, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 228, orbitMiddleState := 334, orbitMiddleCentral := 0, conjugatorInverseState := 259, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 227, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 228, orbitMiddleState := 334, orbitMiddleCentral := 1, conjugatorInverseState := 259, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 227, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 228, orbitMiddleState := 334, orbitMiddleCentral := 2, conjugatorInverseState := 259, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 227, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 228, orbitMiddleState := 334, orbitMiddleCentral := 3, conjugatorInverseState := 259, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 227, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 228, orbitMiddleState := 334, orbitMiddleCentral := 4, conjugatorInverseState := 259, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 227, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 71. -/
def alternatingSixSchurConjugacyDatumRow071 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 316, orbitMiddleState := 345, orbitMiddleCentral := 1, conjugatorInverseState := 304, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 3, orbitPenultimateState := 233, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 316, orbitMiddleState := 345, orbitMiddleCentral := 2, conjugatorInverseState := 304, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 3, orbitPenultimateState := 233, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 316, orbitMiddleState := 345, orbitMiddleCentral := 3, conjugatorInverseState := 304, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 3, orbitPenultimateState := 233, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 316, orbitMiddleState := 345, orbitMiddleCentral := 4, conjugatorInverseState := 304, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 3, orbitPenultimateState := 233, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 316, orbitMiddleState := 345, orbitMiddleCentral := 5, conjugatorInverseState := 304, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 3, orbitPenultimateState := 233, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 316, orbitMiddleState := 345, orbitMiddleCentral := 0, conjugatorInverseState := 304, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 3, orbitPenultimateState := 233, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 72. -/
def alternatingSixSchurConjugacyDatumRow072 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 87, orbitMiddleState := 127, orbitMiddleCentral := 2, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 187, orbitPenultimateCentral := 0 },
    { classIndex := 6, conjugatorState := 23, orbitMiddleState := 39, orbitMiddleCentral := 0, conjugatorInverseState := 26, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 2, orbitPenultimateState := 93, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 23, orbitMiddleState := 39, orbitMiddleCentral := 1, conjugatorInverseState := 26, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 2, orbitPenultimateState := 93, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 23, orbitMiddleState := 39, orbitMiddleCentral := 2, conjugatorInverseState := 26, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 2, orbitPenultimateState := 93, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 87, orbitMiddleState := 127, orbitMiddleCentral := 0, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 187, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 87, orbitMiddleState := 127, orbitMiddleCentral := 1, conjugatorInverseState := 107, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 187, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 73. -/
def alternatingSixSchurConjugacyDatumRow073 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 15, conjugatorState := 224, orbitMiddleState := 302, orbitMiddleCentral := 0, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 298, orbitPenultimateCentral := 3 },
    { classIndex := 16, conjugatorState := 224, orbitMiddleState := 302, orbitMiddleCentral := 1, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 298, orbitPenultimateCentral := 4 },
    { classIndex := 17, conjugatorState := 224, orbitMiddleState := 302, orbitMiddleCentral := 2, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 298, orbitPenultimateCentral := 5 },
    { classIndex := 18, conjugatorState := 224, orbitMiddleState := 302, orbitMiddleCentral := 3, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 298, orbitPenultimateCentral := 0 },
    { classIndex := 19, conjugatorState := 224, orbitMiddleState := 302, orbitMiddleCentral := 4, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 298, orbitPenultimateCentral := 1 },
    { classIndex := 20, conjugatorState := 224, orbitMiddleState := 302, orbitMiddleCentral := 5, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 298, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 74. -/
def alternatingSixSchurConjugacyDatumRow074 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 305, orbitMiddleState := 338, orbitMiddleCentral := 1, conjugatorInverseState := 308, conjugatorInverseCentral := 3, inverseFactorLeftState := 55, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 3, orbitPenultimateState := 333, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 305, orbitMiddleState := 338, orbitMiddleCentral := 2, conjugatorInverseState := 308, conjugatorInverseCentral := 3, inverseFactorLeftState := 55, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 3, orbitPenultimateState := 333, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 305, orbitMiddleState := 338, orbitMiddleCentral := 3, conjugatorInverseState := 308, conjugatorInverseCentral := 3, inverseFactorLeftState := 55, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 3, orbitPenultimateState := 333, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 305, orbitMiddleState := 338, orbitMiddleCentral := 4, conjugatorInverseState := 308, conjugatorInverseCentral := 3, inverseFactorLeftState := 55, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 3, orbitPenultimateState := 333, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 305, orbitMiddleState := 338, orbitMiddleCentral := 5, conjugatorInverseState := 308, conjugatorInverseCentral := 3, inverseFactorLeftState := 55, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 3, orbitPenultimateState := 333, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 305, orbitMiddleState := 338, orbitMiddleCentral := 0, conjugatorInverseState := 308, conjugatorInverseCentral := 3, inverseFactorLeftState := 55, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 3, orbitPenultimateState := 333, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 75. -/
def alternatingSixSchurConjugacyDatumRow075 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 9, orbitMiddleState := 17, orbitMiddleCentral := 2, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 30, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 9, orbitMiddleState := 17, orbitMiddleCentral := 3, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 30, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 9, orbitMiddleState := 17, orbitMiddleCentral := 4, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 30, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 9, orbitMiddleState := 17, orbitMiddleCentral := 5, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 30, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 9, orbitMiddleState := 17, orbitMiddleCentral := 0, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 30, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 9, orbitMiddleState := 17, orbitMiddleCentral := 1, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 30, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 76. -/
def alternatingSixSchurConjugacyDatumRow076 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 13, conjugatorState := 291, orbitMiddleState := 325, orbitMiddleCentral := 4, conjugatorInverseState := 269, conjugatorInverseCentral := 1, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 70, inverseFactorRightCentral := 1, orbitPenultimateState := 164, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 291, orbitMiddleState := 325, orbitMiddleCentral := 5, conjugatorInverseState := 269, conjugatorInverseCentral := 1, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 70, inverseFactorRightCentral := 1, orbitPenultimateState := 164, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 291, orbitMiddleState := 325, orbitMiddleCentral := 0, conjugatorInverseState := 269, conjugatorInverseCentral := 1, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 70, inverseFactorRightCentral := 1, orbitPenultimateState := 164, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 291, orbitMiddleState := 325, orbitMiddleCentral := 1, conjugatorInverseState := 269, conjugatorInverseCentral := 1, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 70, inverseFactorRightCentral := 1, orbitPenultimateState := 164, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 291, orbitMiddleState := 325, orbitMiddleCentral := 2, conjugatorInverseState := 269, conjugatorInverseCentral := 1, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 70, inverseFactorRightCentral := 1, orbitPenultimateState := 164, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 291, orbitMiddleState := 325, orbitMiddleCentral := 3, conjugatorInverseState := 269, conjugatorInverseCentral := 1, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 70, inverseFactorRightCentral := 1, orbitPenultimateState := 164, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 77. -/
def alternatingSixSchurConjugacyDatumRow077 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 0, orbitMiddleState := 77, orbitMiddleCentral := 0, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 77, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 0, orbitMiddleState := 77, orbitMiddleCentral := 1, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 77, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 227, orbitMiddleState := 322, orbitMiddleCentral := 3, conjugatorInverseState := 252, conjugatorInverseCentral := 2, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 39, inverseFactorRightCentral := 2, orbitPenultimateState := 304, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 227, orbitMiddleState := 322, orbitMiddleCentral := 4, conjugatorInverseState := 252, conjugatorInverseCentral := 2, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 39, inverseFactorRightCentral := 2, orbitPenultimateState := 304, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 252, orbitMiddleState := 271, orbitMiddleCentral := 0, conjugatorInverseState := 227, conjugatorInverseCentral := 2, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 2, orbitPenultimateState := 217, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 252, orbitMiddleState := 271, orbitMiddleCentral := 1, conjugatorInverseState := 227, conjugatorInverseCentral := 2, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 2, orbitPenultimateState := 217, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 78. -/
def alternatingSixSchurConjugacyDatumRow078 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 23, conjugatorState := 33, orbitMiddleState := 120, orbitMiddleCentral := 4, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 52, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 33, orbitMiddleState := 120, orbitMiddleCentral := 5, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 52, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 33, orbitMiddleState := 120, orbitMiddleCentral := 0, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 52, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 33, orbitMiddleState := 120, orbitMiddleCentral := 1, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 52, orbitPenultimateCentral := 2 },
    { classIndex := 21, conjugatorState := 33, orbitMiddleState := 120, orbitMiddleCentral := 2, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 52, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 33, orbitMiddleState := 120, orbitMiddleCentral := 3, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 52, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 79. -/
def alternatingSixSchurConjugacyDatumRow079 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 0, orbitMiddleState := 79, orbitMiddleCentral := 0, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 79, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 0, orbitMiddleState := 79, orbitMiddleCentral := 1, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 79, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 106, orbitMiddleState := 304, orbitMiddleCentral := 5, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 163, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 106, orbitMiddleState := 304, orbitMiddleCentral := 0, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 163, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 90, orbitMiddleState := 302, orbitMiddleCentral := 1, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 167, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 90, orbitMiddleState := 302, orbitMiddleCentral := 2, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 167, orbitPenultimateCentral := 3 }
  ]


end GroupTheory
end McKayConjecture
