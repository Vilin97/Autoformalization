/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 110–119

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 110. -/
def alternatingSixSchurConjugacyDatumRow110 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 16, orbitMiddleState := 29, orbitMiddleCentral := 1, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 48, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 16, orbitMiddleState := 29, orbitMiddleCentral := 2, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 48, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 66, orbitMiddleState := 99, orbitMiddleCentral := 0, conjugatorInverseState := 64, conjugatorInverseCentral := 1, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 157, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 66, orbitMiddleState := 99, orbitMiddleCentral := 1, conjugatorInverseState := 64, conjugatorInverseCentral := 1, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 157, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 66, orbitMiddleState := 99, orbitMiddleCentral := 2, conjugatorInverseState := 64, conjugatorInverseCentral := 1, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 1, orbitPenultimateState := 157, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 16, orbitMiddleState := 29, orbitMiddleCentral := 0, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 48, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 111. -/
def alternatingSixSchurConjugacyDatumRow111 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 238, orbitMiddleState := 328, orbitMiddleCentral := 2, conjugatorInverseState := 238, conjugatorInverseCentral := 5, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 5, orbitPenultimateState := 261, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 123, orbitMiddleState := 345, orbitMiddleCentral := 1, conjugatorInverseState := 141, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 262, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 123, orbitMiddleState := 345, orbitMiddleCentral := 2, conjugatorInverseState := 141, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 5, orbitPenultimateState := 262, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 16, orbitMiddleState := 165, orbitMiddleCentral := 2, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 212, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 16, orbitMiddleState := 165, orbitMiddleCentral := 3, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 212, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 238, orbitMiddleState := 328, orbitMiddleCentral := 1, conjugatorInverseState := 238, conjugatorInverseCentral := 5, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 5, orbitPenultimateState := 261, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 112. -/
def alternatingSixSchurConjugacyDatumRow112 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 16, orbitMiddleState := 48, orbitMiddleCentral := 1, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 49, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 16, orbitMiddleState := 48, orbitMiddleCentral := 2, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 49, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 16, orbitMiddleState := 48, orbitMiddleCentral := 3, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 49, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 16, orbitMiddleState := 48, orbitMiddleCentral := 4, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 49, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 16, orbitMiddleState := 48, orbitMiddleCentral := 5, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 49, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 16, orbitMiddleState := 48, orbitMiddleCentral := 0, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 49, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 113. -/
def alternatingSixSchurConjugacyDatumRow113 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 105, orbitMiddleState := 126, orbitMiddleCentral := 3, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 105, orbitMiddleState := 126, orbitMiddleCentral := 4, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 105, orbitMiddleState := 126, orbitMiddleCentral := 5, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 105, orbitMiddleState := 126, orbitMiddleCentral := 0, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 105, orbitMiddleState := 126, orbitMiddleCentral := 1, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 105, orbitMiddleState := 126, orbitMiddleCentral := 2, conjugatorInverseState := 105, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 114. -/
def alternatingSixSchurConjugacyDatumRow114 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 19, conjugatorState := 320, orbitMiddleState := 350, orbitMiddleCentral := 4, conjugatorInverseState := 321, conjugatorInverseCentral := 4, inverseFactorLeftState := 64, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 206, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 320, orbitMiddleState := 350, orbitMiddleCentral := 5, conjugatorInverseState := 321, conjugatorInverseCentral := 4, inverseFactorLeftState := 64, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 206, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 320, orbitMiddleState := 350, orbitMiddleCentral := 0, conjugatorInverseState := 321, conjugatorInverseCentral := 4, inverseFactorLeftState := 64, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 206, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 320, orbitMiddleState := 350, orbitMiddleCentral := 1, conjugatorInverseState := 321, conjugatorInverseCentral := 4, inverseFactorLeftState := 64, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 206, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 320, orbitMiddleState := 350, orbitMiddleCentral := 2, conjugatorInverseState := 321, conjugatorInverseCentral := 4, inverseFactorLeftState := 64, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 206, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 320, orbitMiddleState := 350, orbitMiddleCentral := 3, conjugatorInverseState := 321, conjugatorInverseCentral := 4, inverseFactorLeftState := 64, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 206, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 115. -/
def alternatingSixSchurConjugacyDatumRow115 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 57, orbitMiddleState := 175, orbitMiddleCentral := 5, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 127, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 57, orbitMiddleState := 175, orbitMiddleCentral := 0, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 127, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 57, orbitMiddleState := 175, orbitMiddleCentral := 1, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 127, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 57, orbitMiddleState := 175, orbitMiddleCentral := 2, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 127, orbitPenultimateCentral := 3 },
    { classIndex := 24, conjugatorState := 57, orbitMiddleState := 175, orbitMiddleCentral := 3, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 127, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 57, orbitMiddleState := 175, orbitMiddleCentral := 4, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 127, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 116. -/
def alternatingSixSchurConjugacyDatumRow116 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 36, orbitMiddleState := 58, orbitMiddleCentral := 0, conjugatorInverseState := 42, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 1, orbitPenultimateState := 128, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 36, orbitMiddleState := 58, orbitMiddleCentral := 1, conjugatorInverseState := 42, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 1, orbitPenultimateState := 128, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 36, orbitMiddleState := 58, orbitMiddleCentral := 2, conjugatorInverseState := 42, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 1, orbitPenultimateState := 128, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 62, orbitMiddleState := 94, orbitMiddleCentral := 0, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 209, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 62, orbitMiddleState := 94, orbitMiddleCentral := 1, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 209, orbitPenultimateCentral := 5 },
    { classIndex := 8, conjugatorState := 62, orbitMiddleState := 94, orbitMiddleCentral := 2, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 209, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 117. -/
def alternatingSixSchurConjugacyDatumRow117 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 30, orbitMiddleState := 31, orbitMiddleCentral := 2, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 77, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 30, orbitMiddleState := 31, orbitMiddleCentral := 3, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 77, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 30, orbitMiddleState := 31, orbitMiddleCentral := 4, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 77, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 30, orbitMiddleState := 31, orbitMiddleCentral := 5, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 77, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 30, orbitMiddleState := 31, orbitMiddleCentral := 0, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 77, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 30, orbitMiddleState := 31, orbitMiddleCentral := 1, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 77, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 118. -/
def alternatingSixSchurConjugacyDatumRow118 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 258, orbitMiddleState := 295, orbitMiddleCentral := 0, conjugatorInverseState := 240, conjugatorInverseCentral := 5, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 339, orbitPenultimateCentral := 2 },
    { classIndex := 7, conjugatorState := 258, orbitMiddleState := 295, orbitMiddleCentral := 1, conjugatorInverseState := 240, conjugatorInverseCentral := 5, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 339, orbitPenultimateCentral := 3 },
    { classIndex := 8, conjugatorState := 258, orbitMiddleState := 295, orbitMiddleCentral := 2, conjugatorInverseState := 240, conjugatorInverseCentral := 5, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 339, orbitPenultimateCentral := 4 },
    { classIndex := 6, conjugatorState := 276, orbitMiddleState := 310, orbitMiddleCentral := 0, conjugatorInverseState := 283, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 4, orbitPenultimateState := 320, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 276, orbitMiddleState := 310, orbitMiddleCentral := 1, conjugatorInverseState := 283, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 4, orbitPenultimateState := 320, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 276, orbitMiddleState := 310, orbitMiddleCentral := 2, conjugatorInverseState := 283, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 4, orbitPenultimateState := 320, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 119. -/
def alternatingSixSchurConjugacyDatumRow119 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 194, orbitMiddleState := 317, orbitMiddleCentral := 5, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 157, orbitPenultimateCentral := 4 },
    { classIndex := 21, conjugatorState := 194, orbitMiddleState := 317, orbitMiddleCentral := 0, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 157, orbitPenultimateCentral := 5 },
    { classIndex := 22, conjugatorState := 194, orbitMiddleState := 317, orbitMiddleCentral := 1, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 157, orbitPenultimateCentral := 0 },
    { classIndex := 23, conjugatorState := 194, orbitMiddleState := 317, orbitMiddleCentral := 2, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 157, orbitPenultimateCentral := 1 },
    { classIndex := 24, conjugatorState := 194, orbitMiddleState := 317, orbitMiddleCentral := 3, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 157, orbitPenultimateCentral := 2 },
    { classIndex := 25, conjugatorState := 194, orbitMiddleState := 317, orbitMiddleCentral := 4, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 157, orbitPenultimateCentral := 3 }
  ]


end GroupTheory
end McKayConjecture
