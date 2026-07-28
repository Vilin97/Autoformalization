/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 80–89

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 80. -/
def alternatingSixSchurConjugacyDatumRow080 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 239, orbitMiddleState := 281, orbitMiddleCentral := 2, conjugatorInverseState := 229, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 4, orbitPenultimateState := 273, orbitPenultimateCentral := 0 },
    { classIndex := 12, conjugatorState := 239, orbitMiddleState := 281, orbitMiddleCentral := 3, conjugatorInverseState := 229, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 4, orbitPenultimateState := 273, orbitPenultimateCentral := 1 },
    { classIndex := 13, conjugatorState := 239, orbitMiddleState := 281, orbitMiddleCentral := 4, conjugatorInverseState := 229, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 4, orbitPenultimateState := 273, orbitPenultimateCentral := 2 },
    { classIndex := 14, conjugatorState := 239, orbitMiddleState := 281, orbitMiddleCentral := 5, conjugatorInverseState := 229, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 4, orbitPenultimateState := 273, orbitPenultimateCentral := 3 },
    { classIndex := 9, conjugatorState := 239, orbitMiddleState := 281, orbitMiddleCentral := 0, conjugatorInverseState := 229, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 4, orbitPenultimateState := 273, orbitPenultimateCentral := 4 },
    { classIndex := 10, conjugatorState := 239, orbitMiddleState := 281, orbitMiddleCentral := 1, conjugatorInverseState := 229, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 4, orbitPenultimateState := 273, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 81. -/
def alternatingSixSchurConjugacyDatumRow081 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 10, orbitMiddleState := 226, orbitMiddleCentral := 0, conjugatorInverseState := 14, conjugatorInverseCentral := 2, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 2, orbitPenultimateState := 169, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 10, orbitMiddleState := 226, orbitMiddleCentral := 1, conjugatorInverseState := 14, conjugatorInverseCentral := 2, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 2, orbitPenultimateState := 169, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 113, orbitMiddleState := 346, orbitMiddleCentral := 1, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 271, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 113, orbitMiddleState := 346, orbitMiddleCentral := 2, conjugatorInverseState := 134, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 271, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 125, orbitMiddleState := 353, orbitMiddleCentral := 4, conjugatorInverseState := 125, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 268, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 125, orbitMiddleState := 353, orbitMiddleCentral := 5, conjugatorInverseState := 125, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 5, orbitPenultimateState := 268, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 82. -/
def alternatingSixSchurConjugacyDatumRow082 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 112, orbitMiddleState := 158, orbitMiddleCentral := 1, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 83, orbitPenultimateCentral := 0 },
    { classIndex := 8, conjugatorState := 112, orbitMiddleState := 158, orbitMiddleCentral := 2, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 83, orbitPenultimateCentral := 1 },
    { classIndex := 6, conjugatorState := 10, orbitMiddleState := 19, orbitMiddleCentral := 0, conjugatorInverseState := 14, conjugatorInverseCentral := 2, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 2, orbitPenultimateState := 33, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 10, orbitMiddleState := 19, orbitMiddleCentral := 1, conjugatorInverseState := 14, conjugatorInverseCentral := 2, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 2, orbitPenultimateState := 33, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 10, orbitMiddleState := 19, orbitMiddleCentral := 2, conjugatorInverseState := 14, conjugatorInverseCentral := 2, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 2, orbitPenultimateState := 33, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 112, orbitMiddleState := 158, orbitMiddleCentral := 0, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 83, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 83. -/
def alternatingSixSchurConjugacyDatumRow083 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 8, orbitMiddleState := 34, orbitMiddleCentral := 1, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 55, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 8, orbitMiddleState := 34, orbitMiddleCentral := 2, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 55, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 138, orbitMiddleState := 357, orbitMiddleCentral := 2, conjugatorInverseState := 147, conjugatorInverseCentral := 0, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 274, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 138, orbitMiddleState := 357, orbitMiddleCentral := 3, conjugatorInverseState := 147, conjugatorInverseCentral := 0, inverseFactorLeftState := 26, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 274, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 182, orbitMiddleState := 236, orbitMiddleCentral := 0, conjugatorInverseState := 213, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 2, orbitPenultimateState := 308, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 182, orbitMiddleState := 236, orbitMiddleCentral := 1, conjugatorInverseState := 213, conjugatorInverseCentral := 2, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 2, orbitPenultimateState := 308, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 84. -/
def alternatingSixSchurConjugacyDatumRow084 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 11, orbitMiddleState := 20, orbitMiddleCentral := 2, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 35, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 11, orbitMiddleState := 20, orbitMiddleCentral := 3, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 35, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 11, orbitMiddleState := 20, orbitMiddleCentral := 4, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 35, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 11, orbitMiddleState := 20, orbitMiddleCentral := 5, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 35, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 11, orbitMiddleState := 20, orbitMiddleCentral := 0, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 35, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 11, orbitMiddleState := 20, orbitMiddleCentral := 1, conjugatorInverseState := 9, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 35, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 85. -/
def alternatingSixSchurConjugacyDatumRow085 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 5, orbitMiddleState := 174, orbitMiddleCentral := 0, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 124, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 5, orbitMiddleState := 174, orbitMiddleCentral := 1, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 124, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 213, orbitMiddleState := 264, orbitMiddleCentral := 4, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 228, orbitPenultimateCentral := 1 },
    { classIndex := 28, conjugatorState := 213, orbitMiddleState := 264, orbitMiddleCentral := 5, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 228, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 188, orbitMiddleState := 359, orbitMiddleCentral := 1, conjugatorInverseState := 194, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 233, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 188, orbitMiddleState := 359, orbitMiddleCentral := 2, conjugatorInverseState := 194, conjugatorInverseCentral := 5, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 233, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 86. -/
def alternatingSixSchurConjugacyDatumRow086 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 34, orbitMiddleState := 123, orbitMiddleCentral := 4, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 56, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 34, orbitMiddleState := 123, orbitMiddleCentral := 5, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 56, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 34, orbitMiddleState := 123, orbitMiddleCentral := 0, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 56, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 34, orbitMiddleState := 123, orbitMiddleCentral := 1, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 56, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 34, orbitMiddleState := 123, orbitMiddleCentral := 2, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 56, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 34, orbitMiddleState := 123, orbitMiddleCentral := 3, conjugatorInverseState := 39, conjugatorInverseCentral := 1, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 56, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 87. -/
def alternatingSixSchurConjugacyDatumRow087 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 8, orbitMiddleState := 36, orbitMiddleCentral := 1, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 58, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 8, orbitMiddleState := 36, orbitMiddleCentral := 2, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 58, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 213, orbitMiddleState := 229, orbitMiddleCentral := 0, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 56, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 213, orbitMiddleState := 229, orbitMiddleCentral := 1, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 56, orbitPenultimateCentral := 0 },
    { classIndex := 29, conjugatorState := 202, orbitMiddleState := 225, orbitMiddleCentral := 5, conjugatorInverseState := 208, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 59, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 202, orbitMiddleState := 225, orbitMiddleCentral := 0, conjugatorInverseState := 208, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 59, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 88. -/
def alternatingSixSchurConjugacyDatumRow088 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 22, orbitMiddleState := 37, orbitMiddleCentral := 4, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 36, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 22, orbitMiddleState := 37, orbitMiddleCentral := 5, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 36, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 22, orbitMiddleState := 37, orbitMiddleCentral := 0, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 36, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 22, orbitMiddleState := 37, orbitMiddleCentral := 1, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 36, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 22, orbitMiddleState := 37, orbitMiddleCentral := 2, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 36, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 22, orbitMiddleState := 37, orbitMiddleCentral := 3, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 36, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 89. -/
def alternatingSixSchurConjugacyDatumRow089 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 261, orbitMiddleState := 298, orbitMiddleCentral := 2, conjugatorInverseState := 223, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 4, orbitPenultimateState := 238, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 261, orbitMiddleState := 298, orbitMiddleCentral := 3, conjugatorInverseState := 223, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 4, orbitPenultimateState := 238, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 261, orbitMiddleState := 298, orbitMiddleCentral := 4, conjugatorInverseState := 223, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 4, orbitPenultimateState := 238, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 261, orbitMiddleState := 298, orbitMiddleCentral := 5, conjugatorInverseState := 223, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 4, orbitPenultimateState := 238, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 261, orbitMiddleState := 298, orbitMiddleCentral := 0, conjugatorInverseState := 223, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 4, orbitPenultimateState := 238, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 261, orbitMiddleState := 298, orbitMiddleCentral := 1, conjugatorInverseState := 223, conjugatorInverseCentral := 4, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 4, orbitPenultimateState := 238, orbitPenultimateCentral := 4 }
  ]


end GroupTheory
end McKayConjecture
