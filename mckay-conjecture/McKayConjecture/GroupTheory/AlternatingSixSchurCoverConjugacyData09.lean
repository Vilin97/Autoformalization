/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 90–99

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 90. -/
def alternatingSixSchurConjugacyDatumRow090 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 2, orbitMiddleState := 133, orbitMiddleCentral := 0, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 133, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 2, orbitMiddleState := 133, orbitMiddleCentral := 1, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 133, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 52, orbitMiddleState := 336, orbitMiddleCentral := 0, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 237, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 52, orbitMiddleState := 336, orbitMiddleCentral := 1, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 237, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 142, orbitMiddleState := 345, orbitMiddleCentral := 0, conjugatorInverseState := 151, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 185, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 142, orbitMiddleState := 345, orbitMiddleCentral := 1, conjugatorInverseState := 151, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 185, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 91. -/
def alternatingSixSchurConjugacyDatumRow091 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 12, orbitMiddleState := 22, orbitMiddleCentral := 1, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 38, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 12, orbitMiddleState := 22, orbitMiddleCentral := 2, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 38, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 68, orbitMiddleState := 102, orbitMiddleCentral := 0, conjugatorInverseState := 70, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 132, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 68, orbitMiddleState := 102, orbitMiddleCentral := 1, conjugatorInverseState := 70, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 132, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 68, orbitMiddleState := 102, orbitMiddleCentral := 2, conjugatorInverseState := 70, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 132, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 12, orbitMiddleState := 22, orbitMiddleCentral := 0, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 38, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 92. -/
def alternatingSixSchurConjugacyDatumRow092 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 13, conjugatorState := 290, orbitMiddleState := 323, orbitMiddleCentral := 4, conjugatorInverseState := 273, conjugatorInverseCentral := 1, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 318, orbitPenultimateCentral := 2 },
    { classIndex := 14, conjugatorState := 290, orbitMiddleState := 323, orbitMiddleCentral := 5, conjugatorInverseState := 273, conjugatorInverseCentral := 1, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 318, orbitPenultimateCentral := 3 },
    { classIndex := 9, conjugatorState := 290, orbitMiddleState := 323, orbitMiddleCentral := 0, conjugatorInverseState := 273, conjugatorInverseCentral := 1, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 318, orbitPenultimateCentral := 4 },
    { classIndex := 10, conjugatorState := 290, orbitMiddleState := 323, orbitMiddleCentral := 1, conjugatorInverseState := 273, conjugatorInverseCentral := 1, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 318, orbitPenultimateCentral := 5 },
    { classIndex := 11, conjugatorState := 290, orbitMiddleState := 323, orbitMiddleCentral := 2, conjugatorInverseState := 273, conjugatorInverseCentral := 1, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 318, orbitPenultimateCentral := 0 },
    { classIndex := 12, conjugatorState := 290, orbitMiddleState := 323, orbitMiddleCentral := 3, conjugatorInverseState := 273, conjugatorInverseCentral := 1, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 318, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 93. -/
def alternatingSixSchurConjugacyDatumRow093 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 40, orbitMiddleState := 138, orbitMiddleCentral := 4, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 137, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 40, orbitMiddleState := 138, orbitMiddleCentral := 5, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 137, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 40, orbitMiddleState := 138, orbitMiddleCentral := 0, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 137, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 40, orbitMiddleState := 138, orbitMiddleCentral := 1, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 137, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 40, orbitMiddleState := 138, orbitMiddleCentral := 2, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 137, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 40, orbitMiddleState := 138, orbitMiddleCentral := 3, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 137, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 94. -/
def alternatingSixSchurConjugacyDatumRow094 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 1, orbitMiddleState := 62, orbitMiddleCentral := 1, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 62, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 1, orbitMiddleState := 62, orbitMiddleCentral := 2, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 62, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 201, orbitMiddleState := 340, orbitMiddleCentral := 2, conjugatorInverseState := 201, conjugatorInverseCentral := 3, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 3, orbitPenultimateState := 319, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 201, orbitMiddleState := 340, orbitMiddleCentral := 3, conjugatorInverseState := 201, conjugatorInverseCentral := 3, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 3, orbitPenultimateState := 319, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 248, orbitMiddleState := 288, orbitMiddleCentral := 0, conjugatorInverseState := 248, conjugatorInverseCentral := 5, inverseFactorLeftState := 42, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 5 },
    { classIndex := 28, conjugatorState := 248, orbitMiddleState := 288, orbitMiddleCentral := 1, conjugatorInverseState := 248, conjugatorInverseCentral := 5, inverseFactorLeftState := 42, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 95. -/
def alternatingSixSchurConjugacyDatumRow095 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 13, orbitMiddleState := 221, orbitMiddleCentral := 3, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 189, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 13, orbitMiddleState := 221, orbitMiddleCentral := 4, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 189, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 126, orbitMiddleState := 313, orbitMiddleCentral := 3, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 284, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 126, orbitMiddleState := 313, orbitMiddleCentral := 4, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 284, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 251, orbitMiddleState := 337, orbitMiddleCentral := 1, conjugatorInverseState := 246, conjugatorInverseCentral := 2, inverseFactorLeftState := 41, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 2, orbitPenultimateState := 220, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 251, orbitMiddleState := 337, orbitMiddleCentral := 2, conjugatorInverseState := 246, conjugatorInverseCentral := 2, inverseFactorLeftState := 41, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 2, orbitPenultimateState := 220, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 96. -/
def alternatingSixSchurConjugacyDatumRow096 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 13, orbitMiddleState := 24, orbitMiddleCentral := 1, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 40, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 13, orbitMiddleState := 24, orbitMiddleCentral := 2, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 40, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 18, orbitMiddleState := 32, orbitMiddleCentral := 0, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 78, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 18, orbitMiddleState := 32, orbitMiddleCentral := 1, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 78, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 18, orbitMiddleState := 32, orbitMiddleCentral := 2, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 78, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 13, orbitMiddleState := 24, orbitMiddleCentral := 0, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 40, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 97. -/
def alternatingSixSchurConjugacyDatumRow097 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 1, orbitMiddleState := 64, orbitMiddleCentral := 1, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 1, orbitMiddleState := 64, orbitMiddleCentral := 2, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 126, orbitMiddleState := 285, orbitMiddleCentral := 0, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 95, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 126, orbitMiddleState := 285, orbitMiddleCentral := 1, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 95, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 112, orbitMiddleState := 283, orbitMiddleCentral := 2, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 98, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 112, orbitMiddleState := 283, orbitMiddleCentral := 3, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 98, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 98. -/
def alternatingSixSchurConjugacyDatumRow098 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 14, orbitMiddleState := 25, orbitMiddleCentral := 2, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 42, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 14, orbitMiddleState := 25, orbitMiddleCentral := 3, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 42, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 14, orbitMiddleState := 25, orbitMiddleCentral := 4, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 42, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 14, orbitMiddleState := 25, orbitMiddleCentral := 5, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 42, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 14, orbitMiddleState := 25, orbitMiddleCentral := 0, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 42, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 14, orbitMiddleState := 25, orbitMiddleCentral := 1, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 42, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 99. -/
def alternatingSixSchurConjugacyDatumRow099 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 7, orbitMiddleState := 196, orbitMiddleCentral := 0, conjugatorInverseState := 7, conjugatorInverseCentral := 3, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 3, orbitPenultimateState := 143, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 7, orbitMiddleState := 196, orbitMiddleCentral := 1, conjugatorInverseState := 7, conjugatorInverseCentral := 3, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 3, orbitPenultimateState := 143, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 91, orbitMiddleState := 354, orbitMiddleCentral := 0, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 289, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 91, orbitMiddleState := 354, orbitMiddleCentral := 1, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 289, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 105, orbitMiddleState := 359, orbitMiddleCentral := 3, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 290, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 105, orbitMiddleState := 359, orbitMiddleCentral := 4, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 290, orbitPenultimateCentral := 0 }
  ]


end GroupTheory
end McKayConjecture
