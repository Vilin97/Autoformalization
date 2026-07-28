/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 60–69

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 60. -/
def alternatingSixSchurConjugacyDatumRow060 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 109, orbitMiddleState := 154, orbitMiddleCentral := 1, conjugatorInverseState := 76, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 135, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 109, orbitMiddleState := 154, orbitMiddleCentral := 2, conjugatorInverseState := 76, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 135, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 109, orbitMiddleState := 154, orbitMiddleCentral := 3, conjugatorInverseState := 76, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 135, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 109, orbitMiddleState := 154, orbitMiddleCentral := 4, conjugatorInverseState := 76, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 135, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 109, orbitMiddleState := 154, orbitMiddleCentral := 5, conjugatorInverseState := 76, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 135, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 109, orbitMiddleState := 154, orbitMiddleCentral := 0, conjugatorInverseState := 76, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 135, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 61. -/
def alternatingSixSchurConjugacyDatumRow061 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 18, conjugatorState := 324, orbitMiddleState := 359, orbitMiddleCentral := 2, conjugatorInverseState := 318, conjugatorInverseCentral := 1, inverseFactorLeftState := 62, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 241, orbitPenultimateCentral := 0 },
    { classIndex := 19, conjugatorState := 324, orbitMiddleState := 359, orbitMiddleCentral := 3, conjugatorInverseState := 318, conjugatorInverseCentral := 1, inverseFactorLeftState := 62, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 241, orbitPenultimateCentral := 1 },
    { classIndex := 20, conjugatorState := 324, orbitMiddleState := 359, orbitMiddleCentral := 4, conjugatorInverseState := 318, conjugatorInverseCentral := 1, inverseFactorLeftState := 62, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 241, orbitPenultimateCentral := 2 },
    { classIndex := 15, conjugatorState := 324, orbitMiddleState := 359, orbitMiddleCentral := 5, conjugatorInverseState := 318, conjugatorInverseCentral := 1, inverseFactorLeftState := 62, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 241, orbitPenultimateCentral := 3 },
    { classIndex := 16, conjugatorState := 324, orbitMiddleState := 359, orbitMiddleCentral := 0, conjugatorInverseState := 318, conjugatorInverseCentral := 1, inverseFactorLeftState := 62, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 241, orbitPenultimateCentral := 4 },
    { classIndex := 17, conjugatorState := 324, orbitMiddleState := 359, orbitMiddleCentral := 1, conjugatorInverseState := 318, conjugatorInverseCentral := 1, inverseFactorLeftState := 62, inverseFactorLeftCentral := 0, inverseFactorRightState := 54, inverseFactorRightCentral := 1, orbitPenultimateState := 241, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 62. -/
def alternatingSixSchurConjugacyDatumRow062 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 77, orbitMiddleState := 116, orbitMiddleCentral := 2, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 234, orbitPenultimateCentral := 0 },
    { classIndex := 6, conjugatorState := 28, orbitMiddleState := 47, orbitMiddleCentral := 0, conjugatorInverseState := 25, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 2, orbitPenultimateState := 108, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 28, orbitMiddleState := 47, orbitMiddleCentral := 1, conjugatorInverseState := 25, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 2, orbitPenultimateState := 108, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 28, orbitMiddleState := 47, orbitMiddleCentral := 2, conjugatorInverseState := 25, conjugatorInverseCentral := 2, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 2, orbitPenultimateState := 108, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 77, orbitMiddleState := 116, orbitMiddleCentral := 0, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 234, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 77, orbitMiddleState := 116, orbitMiddleCentral := 1, conjugatorInverseState := 94, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 234, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 63. -/
def alternatingSixSchurConjugacyDatumRow063 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 144, orbitMiddleState := 197, orbitMiddleCentral := 3, conjugatorInverseState := 128, conjugatorInverseCentral := 3, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 221, orbitPenultimateCentral := 2 },
    { classIndex := 11, conjugatorState := 144, orbitMiddleState := 197, orbitMiddleCentral := 4, conjugatorInverseState := 128, conjugatorInverseCentral := 3, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 221, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 144, orbitMiddleState := 197, orbitMiddleCentral := 5, conjugatorInverseState := 128, conjugatorInverseCentral := 3, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 221, orbitPenultimateCentral := 4 },
    { classIndex := 13, conjugatorState := 144, orbitMiddleState := 197, orbitMiddleCentral := 0, conjugatorInverseState := 128, conjugatorInverseCentral := 3, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 221, orbitPenultimateCentral := 5 },
    { classIndex := 14, conjugatorState := 144, orbitMiddleState := 197, orbitMiddleCentral := 1, conjugatorInverseState := 128, conjugatorInverseCentral := 3, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 221, orbitPenultimateCentral := 0 },
    { classIndex := 9, conjugatorState := 144, orbitMiddleState := 197, orbitMiddleCentral := 2, conjugatorInverseState := 128, conjugatorInverseCentral := 3, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 221, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 64. -/
def alternatingSixSchurConjugacyDatumRow064 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 224, orbitMiddleState := 336, orbitMiddleCentral := 4, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 224, orbitMiddleState := 336, orbitMiddleCentral := 5, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 224, orbitMiddleState := 336, orbitMiddleCentral := 0, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 224, orbitMiddleState := 336, orbitMiddleCentral := 1, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 224, orbitMiddleState := 336, orbitMiddleCentral := 2, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 224, orbitMiddleState := 336, orbitMiddleCentral := 3, conjugatorInverseState := 241, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 65. -/
def alternatingSixSchurConjugacyDatumRow065 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 295, orbitMiddleState := 329, orbitMiddleCentral := 2, conjugatorInverseState := 264, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 51, inverseFactorRightCentral := 4, orbitPenultimateState := 145, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 295, orbitMiddleState := 329, orbitMiddleCentral := 3, conjugatorInverseState := 264, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 51, inverseFactorRightCentral := 4, orbitPenultimateState := 145, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 295, orbitMiddleState := 329, orbitMiddleCentral := 4, conjugatorInverseState := 264, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 51, inverseFactorRightCentral := 4, orbitPenultimateState := 145, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 295, orbitMiddleState := 329, orbitMiddleCentral := 5, conjugatorInverseState := 264, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 51, inverseFactorRightCentral := 4, orbitPenultimateState := 145, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 295, orbitMiddleState := 329, orbitMiddleCentral := 0, conjugatorInverseState := 264, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 51, inverseFactorRightCentral := 4, orbitPenultimateState := 145, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 295, orbitMiddleState := 329, orbitMiddleCentral := 1, conjugatorInverseState := 264, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 51, inverseFactorRightCentral := 4, orbitPenultimateState := 145, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 66. -/
def alternatingSixSchurConjugacyDatumRow066 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 223, orbitMiddleState := 267, orbitMiddleCentral := 3, conjugatorInverseState := 261, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 221, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 223, orbitMiddleState := 267, orbitMiddleCentral := 4, conjugatorInverseState := 261, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 221, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 223, orbitMiddleState := 267, orbitMiddleCentral := 5, conjugatorInverseState := 261, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 221, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 223, orbitMiddleState := 267, orbitMiddleCentral := 0, conjugatorInverseState := 261, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 221, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 223, orbitMiddleState := 267, orbitMiddleCentral := 1, conjugatorInverseState := 261, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 221, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 223, orbitMiddleState := 267, orbitMiddleCentral := 2, conjugatorInverseState := 261, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 4, orbitPenultimateState := 221, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 67. -/
def alternatingSixSchurConjugacyDatumRow067 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 18, conjugatorState := 297, orbitMiddleState := 337, orbitMiddleCentral := 5, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 325, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 297, orbitMiddleState := 337, orbitMiddleCentral := 0, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 325, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 297, orbitMiddleState := 337, orbitMiddleCentral := 1, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 325, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 297, orbitMiddleState := 337, orbitMiddleCentral := 2, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 325, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 297, orbitMiddleState := 337, orbitMiddleCentral := 3, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 325, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 297, orbitMiddleState := 337, orbitMiddleCentral := 4, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 325, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 68. -/
def alternatingSixSchurConjugacyDatumRow068 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 229, orbitMiddleState := 275, orbitMiddleCentral := 2, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 90, orbitPenultimateCentral := 3 },
    { classIndex := 26, conjugatorState := 229, orbitMiddleState := 275, orbitMiddleCentral := 3, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 90, orbitPenultimateCentral := 4 },
    { classIndex := 21, conjugatorState := 229, orbitMiddleState := 275, orbitMiddleCentral := 4, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 90, orbitPenultimateCentral := 5 },
    { classIndex := 22, conjugatorState := 229, orbitMiddleState := 275, orbitMiddleCentral := 5, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 90, orbitPenultimateCentral := 0 },
    { classIndex := 23, conjugatorState := 229, orbitMiddleState := 275, orbitMiddleCentral := 0, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 90, orbitPenultimateCentral := 1 },
    { classIndex := 24, conjugatorState := 229, orbitMiddleState := 275, orbitMiddleCentral := 1, conjugatorInverseState := 239, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 90, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 69. -/
def alternatingSixSchurConjugacyDatumRow069 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 114, orbitMiddleState := 160, orbitMiddleCentral := 3, conjugatorInverseState := 129, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 150, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 114, orbitMiddleState := 160, orbitMiddleCentral := 4, conjugatorInverseState := 129, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 150, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 114, orbitMiddleState := 160, orbitMiddleCentral := 5, conjugatorInverseState := 129, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 150, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 114, orbitMiddleState := 160, orbitMiddleCentral := 0, conjugatorInverseState := 129, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 150, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 114, orbitMiddleState := 160, orbitMiddleCentral := 1, conjugatorInverseState := 129, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 150, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 114, orbitMiddleState := 160, orbitMiddleCentral := 2, conjugatorInverseState := 129, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 150, orbitPenultimateCentral := 5 }
  ]


end GroupTheory
end McKayConjecture
