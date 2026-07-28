/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 100–109

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 100. -/
def alternatingSixSchurConjugacyDatumRow100 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 45, orbitMiddleState := 68, orbitMiddleCentral := 4, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 26, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 45, orbitMiddleState := 68, orbitMiddleCentral := 5, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 26, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 45, orbitMiddleState := 68, orbitMiddleCentral := 0, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 26, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 45, orbitMiddleState := 68, orbitMiddleCentral := 1, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 26, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 45, orbitMiddleState := 68, orbitMiddleCentral := 2, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 26, orbitPenultimateCentral := 3 },
    { classIndex := 24, conjugatorState := 45, orbitMiddleState := 68, orbitMiddleCentral := 3, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 26, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 101. -/
def alternatingSixSchurConjugacyDatumRow101 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 41, orbitMiddleState := 66, orbitMiddleCentral := 1, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 25, orbitPenultimateCentral := 2 },
    { classIndex := 22, conjugatorState := 41, orbitMiddleState := 66, orbitMiddleCentral := 2, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 25, orbitPenultimateCentral := 3 },
    { classIndex := 23, conjugatorState := 41, orbitMiddleState := 66, orbitMiddleCentral := 3, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 25, orbitPenultimateCentral := 4 },
    { classIndex := 24, conjugatorState := 41, orbitMiddleState := 66, orbitMiddleCentral := 4, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 25, orbitPenultimateCentral := 5 },
    { classIndex := 25, conjugatorState := 41, orbitMiddleState := 66, orbitMiddleCentral := 5, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 25, orbitPenultimateCentral := 0 },
    { classIndex := 26, conjugatorState := 41, orbitMiddleState := 66, orbitMiddleCentral := 0, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 25, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 102. -/
def alternatingSixSchurConjugacyDatumRow102 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 11, orbitMiddleState := 26, orbitMiddleCentral := 2, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 44, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 11, orbitMiddleState := 26, orbitMiddleCentral := 3, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 44, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 164, orbitMiddleState := 349, orbitMiddleCentral := 3, conjugatorInverseState := 183, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 2, orbitPenultimateState := 325, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 164, orbitMiddleState := 349, orbitMiddleCentral := 4, conjugatorInverseState := 183, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 2, orbitPenultimateState := 325, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 211, orbitMiddleState := 302, orbitMiddleCentral := 2, conjugatorInverseState := 193, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 5, orbitPenultimateState := 314, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 211, orbitMiddleState := 302, orbitMiddleCentral := 3, conjugatorInverseState := 193, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 5, orbitPenultimateState := 314, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 103. -/
def alternatingSixSchurConjugacyDatumRow103 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 13, conjugatorState := 217, orbitMiddleState := 264, orbitMiddleCentral := 4, conjugatorInverseState := 222, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 314, orbitPenultimateCentral := 5 },
    { classIndex := 14, conjugatorState := 217, orbitMiddleState := 264, orbitMiddleCentral := 5, conjugatorInverseState := 222, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 314, orbitPenultimateCentral := 0 },
    { classIndex := 9, conjugatorState := 217, orbitMiddleState := 264, orbitMiddleCentral := 0, conjugatorInverseState := 222, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 314, orbitPenultimateCentral := 1 },
    { classIndex := 10, conjugatorState := 217, orbitMiddleState := 264, orbitMiddleCentral := 1, conjugatorInverseState := 222, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 314, orbitPenultimateCentral := 2 },
    { classIndex := 11, conjugatorState := 217, orbitMiddleState := 264, orbitMiddleCentral := 2, conjugatorInverseState := 222, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 314, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 217, orbitMiddleState := 264, orbitMiddleCentral := 3, conjugatorInverseState := 222, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 314, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 104. -/
def alternatingSixSchurConjugacyDatumRow104 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 3, orbitMiddleState := 150, orbitMiddleCentral := 0, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 150, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 3, orbitMiddleState := 150, orbitMiddleCentral := 1, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 150, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 237, orbitMiddleState := 240, orbitMiddleCentral := 5, conjugatorInverseState := 237, conjugatorInverseCentral := 3, inverseFactorLeftState := 37, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 3, orbitPenultimateState := 254, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 237, orbitMiddleState := 240, orbitMiddleCentral := 0, conjugatorInverseState := 237, conjugatorInverseCentral := 3, inverseFactorLeftState := 37, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 3, orbitPenultimateState := 254, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 189, orbitMiddleState := 219, orbitMiddleCentral := 4, conjugatorInverseState := 171, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 328, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 189, orbitMiddleState := 219, orbitMiddleCentral := 5, conjugatorInverseState := 171, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 328, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 105. -/
def alternatingSixSchurConjugacyDatumRow105 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 15, orbitMiddleState := 27, orbitMiddleCentral := 1, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 46, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 15, orbitMiddleState := 27, orbitMiddleCentral := 2, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 46, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 20, orbitMiddleState := 35, orbitMiddleCentral := 0, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 86, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 20, orbitMiddleState := 35, orbitMiddleCentral := 1, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 86, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 20, orbitMiddleState := 35, orbitMiddleCentral := 2, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 86, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 15, orbitMiddleState := 27, orbitMiddleCentral := 0, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 46, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 106. -/
def alternatingSixSchurConjugacyDatumRow106 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 143, orbitMiddleState := 343, orbitMiddleCentral := 3, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 175, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 51, orbitMiddleState := 337, orbitMiddleCentral := 3, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 259, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 51, orbitMiddleState := 337, orbitMiddleCentral := 4, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 259, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 3, orbitMiddleState := 151, orbitMiddleCentral := 0, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 151, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 3, orbitMiddleState := 151, orbitMiddleCentral := 1, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 151, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 143, orbitMiddleState := 343, orbitMiddleCentral := 2, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 175, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 107. -/
def alternatingSixSchurConjugacyDatumRow107 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 11, orbitMiddleState := 28, orbitMiddleCentral := 2, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 47, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 11, orbitMiddleState := 28, orbitMiddleCentral := 3, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 47, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 203, orbitMiddleState := 305, orbitMiddleCentral := 4, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 219, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 203, orbitMiddleState := 305, orbitMiddleCentral := 5, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 219, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 195, orbitMiddleState := 348, orbitMiddleCentral := 1, conjugatorInverseState := 175, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 330, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 195, orbitMiddleState := 348, orbitMiddleCentral := 2, conjugatorInverseState := 175, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 330, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 108. -/
def alternatingSixSchurConjugacyDatumRow108 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 46, orbitMiddleState := 151, orbitMiddleCentral := 0, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 152, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 46, orbitMiddleState := 151, orbitMiddleCentral := 1, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 152, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 46, orbitMiddleState := 151, orbitMiddleCentral := 2, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 152, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 46, orbitMiddleState := 151, orbitMiddleCentral := 3, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 152, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 46, orbitMiddleState := 151, orbitMiddleCentral := 4, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 152, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 46, orbitMiddleState := 151, orbitMiddleCentral := 5, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 152, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 109. -/
def alternatingSixSchurConjugacyDatumRow109 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 29, orbitMiddleState := 48, orbitMiddleCentral := 2, conjugatorInverseState := 17, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 110, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 29, orbitMiddleState := 48, orbitMiddleCentral := 3, conjugatorInverseState := 17, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 110, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 29, orbitMiddleState := 48, orbitMiddleCentral := 4, conjugatorInverseState := 17, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 110, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 29, orbitMiddleState := 48, orbitMiddleCentral := 5, conjugatorInverseState := 17, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 110, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 29, orbitMiddleState := 48, orbitMiddleCentral := 0, conjugatorInverseState := 17, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 110, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 29, orbitMiddleState := 48, orbitMiddleCentral := 1, conjugatorInverseState := 17, conjugatorInverseCentral := 4, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 110, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
