/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 0–9

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 0. -/
def alternatingSixSchurConjugacyDatumRow000 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 0, conjugatorState := 0, orbitMiddleState := 0, orbitMiddleCentral := 0, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 0, orbitPenultimateCentral := 0 },
    { classIndex := 1, conjugatorState := 0, orbitMiddleState := 0, orbitMiddleCentral := 1, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 0, orbitPenultimateCentral := 1 },
    { classIndex := 2, conjugatorState := 0, orbitMiddleState := 0, orbitMiddleCentral := 2, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 0, orbitPenultimateCentral := 2 },
    { classIndex := 3, conjugatorState := 0, orbitMiddleState := 0, orbitMiddleCentral := 3, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 0, orbitPenultimateCentral := 3 },
    { classIndex := 4, conjugatorState := 0, orbitMiddleState := 0, orbitMiddleCentral := 4, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 0, orbitPenultimateCentral := 4 },
    { classIndex := 5, conjugatorState := 0, orbitMiddleState := 0, orbitMiddleCentral := 5, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 0, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 1. -/
def alternatingSixSchurConjugacyDatumRow001 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 0, orbitMiddleState := 1, orbitMiddleCentral := 0, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 1, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 0, orbitMiddleState := 1, orbitMiddleCentral := 1, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 1, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 0, orbitMiddleState := 1, orbitMiddleCentral := 2, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 1, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 96, orbitMiddleState := 118, orbitMiddleCentral := 3, conjugatorInverseState := 96, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 32, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 96, orbitMiddleState := 118, orbitMiddleCentral := 4, conjugatorInverseState := 96, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 32, orbitPenultimateCentral := 5 },
    { classIndex := 8, conjugatorState := 96, orbitMiddleState := 118, orbitMiddleCentral := 5, conjugatorInverseState := 96, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 32, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 2. -/
def alternatingSixSchurConjugacyDatumRow002 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 0, orbitMiddleState := 2, orbitMiddleCentral := 0, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 2, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 0, orbitMiddleState := 2, orbitMiddleCentral := 1, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 2, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 0, orbitMiddleState := 2, orbitMiddleCentral := 2, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 2, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 0, orbitMiddleState := 2, orbitMiddleCentral := 3, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 2, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 0, orbitMiddleState := 2, orbitMiddleCentral := 4, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 2, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 0, orbitMiddleState := 2, orbitMiddleCentral := 5, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 2, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 3. -/
def alternatingSixSchurConjugacyDatumRow003 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 340, orbitMiddleState := 357, orbitMiddleCentral := 0, conjugatorInverseState := 340, conjugatorInverseCentral := 5, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 97, inverseFactorRightCentral := 5, orbitPenultimateState := 153, orbitPenultimateCentral := 1 },
    { classIndex := 10, conjugatorState := 340, orbitMiddleState := 357, orbitMiddleCentral := 1, conjugatorInverseState := 340, conjugatorInverseCentral := 5, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 97, inverseFactorRightCentral := 5, orbitPenultimateState := 153, orbitPenultimateCentral := 2 },
    { classIndex := 11, conjugatorState := 340, orbitMiddleState := 357, orbitMiddleCentral := 2, conjugatorInverseState := 340, conjugatorInverseCentral := 5, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 97, inverseFactorRightCentral := 5, orbitPenultimateState := 153, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 340, orbitMiddleState := 357, orbitMiddleCentral := 3, conjugatorInverseState := 340, conjugatorInverseCentral := 5, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 97, inverseFactorRightCentral := 5, orbitPenultimateState := 153, orbitPenultimateCentral := 4 },
    { classIndex := 13, conjugatorState := 340, orbitMiddleState := 357, orbitMiddleCentral := 4, conjugatorInverseState := 340, conjugatorInverseCentral := 5, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 97, inverseFactorRightCentral := 5, orbitPenultimateState := 153, orbitPenultimateCentral := 5 },
    { classIndex := 14, conjugatorState := 340, orbitMiddleState := 357, orbitMiddleCentral := 5, conjugatorInverseState := 340, conjugatorInverseCentral := 5, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 97, inverseFactorRightCentral := 5, orbitPenultimateState := 153, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 4. -/
def alternatingSixSchurConjugacyDatumRow004 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 15, conjugatorState := 0, orbitMiddleState := 4, orbitMiddleCentral := 0, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 4, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 0, orbitMiddleState := 4, orbitMiddleCentral := 1, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 4, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 0, orbitMiddleState := 4, orbitMiddleCentral := 2, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 4, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 0, orbitMiddleState := 4, orbitMiddleCentral := 3, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 4, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 0, orbitMiddleState := 4, orbitMiddleCentral := 4, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 4, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 0, orbitMiddleState := 4, orbitMiddleCentral := 5, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 4, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 5. -/
def alternatingSixSchurConjugacyDatumRow005 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 213, orbitMiddleState := 262, orbitMiddleCentral := 3, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 83, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 213, orbitMiddleState := 262, orbitMiddleCentral := 4, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 83, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 213, orbitMiddleState := 262, orbitMiddleCentral := 5, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 83, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 213, orbitMiddleState := 262, orbitMiddleCentral := 0, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 83, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 213, orbitMiddleState := 262, orbitMiddleCentral := 1, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 83, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 213, orbitMiddleState := 262, orbitMiddleCentral := 2, conjugatorInverseState := 182, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 45, inverseFactorRightCentral := 2, orbitPenultimateState := 83, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 6. -/
def alternatingSixSchurConjugacyDatumRow006 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 15, conjugatorState := 1, orbitMiddleState := 2, orbitMiddleCentral := 1, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 2, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 1, orbitMiddleState := 2, orbitMiddleCentral := 2, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 2, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 1, orbitMiddleState := 2, orbitMiddleCentral := 3, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 2, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 1, orbitMiddleState := 2, orbitMiddleCentral := 4, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 2, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 1, orbitMiddleState := 2, orbitMiddleCentral := 5, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 2, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 1, orbitMiddleState := 2, orbitMiddleCentral := 0, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 2, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 7. -/
def alternatingSixSchurConjugacyDatumRow007 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 165, orbitMiddleState := 221, orbitMiddleCentral := 1, conjugatorInverseState := 209, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 99, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 165, orbitMiddleState := 221, orbitMiddleCentral := 2, conjugatorInverseState := 209, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 99, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 54, orbitMiddleState := 82, orbitMiddleCentral := 0, conjugatorInverseState := 67, conjugatorInverseCentral := 4, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 4, orbitPenultimateState := 43, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 54, orbitMiddleState := 82, orbitMiddleCentral := 1, conjugatorInverseState := 67, conjugatorInverseCentral := 4, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 4, orbitPenultimateState := 43, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 54, orbitMiddleState := 82, orbitMiddleCentral := 2, conjugatorInverseState := 67, conjugatorInverseCentral := 4, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 4, orbitPenultimateState := 43, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 165, orbitMiddleState := 221, orbitMiddleCentral := 0, conjugatorInverseState := 209, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 99, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 8. -/
def alternatingSixSchurConjugacyDatumRow008 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 237, orbitMiddleState := 238, orbitMiddleCentral := 4, conjugatorInverseState := 237, conjugatorInverseCentral := 3, inverseFactorLeftState := 37, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 3, orbitPenultimateState := 103, orbitPenultimateCentral := 4 },
    { classIndex := 15, conjugatorState := 237, orbitMiddleState := 238, orbitMiddleCentral := 5, conjugatorInverseState := 237, conjugatorInverseCentral := 3, inverseFactorLeftState := 37, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 3, orbitPenultimateState := 103, orbitPenultimateCentral := 5 },
    { classIndex := 16, conjugatorState := 237, orbitMiddleState := 238, orbitMiddleCentral := 0, conjugatorInverseState := 237, conjugatorInverseCentral := 3, inverseFactorLeftState := 37, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 3, orbitPenultimateState := 103, orbitPenultimateCentral := 0 },
    { classIndex := 17, conjugatorState := 237, orbitMiddleState := 238, orbitMiddleCentral := 1, conjugatorInverseState := 237, conjugatorInverseCentral := 3, inverseFactorLeftState := 37, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 3, orbitPenultimateState := 103, orbitPenultimateCentral := 1 },
    { classIndex := 18, conjugatorState := 237, orbitMiddleState := 238, orbitMiddleCentral := 2, conjugatorInverseState := 237, conjugatorInverseCentral := 3, inverseFactorLeftState := 37, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 3, orbitPenultimateState := 103, orbitPenultimateCentral := 2 },
    { classIndex := 19, conjugatorState := 237, orbitMiddleState := 238, orbitMiddleCentral := 3, conjugatorInverseState := 237, conjugatorInverseCentral := 3, inverseFactorLeftState := 37, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 3, orbitPenultimateState := 103, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 9. -/
def alternatingSixSchurConjugacyDatumRow009 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 1, orbitMiddleState := 4, orbitMiddleCentral := 1, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 4, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 1, orbitMiddleState := 4, orbitMiddleCentral := 2, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 4, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 1, orbitMiddleState := 4, orbitMiddleCentral := 3, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 4, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 1, orbitMiddleState := 4, orbitMiddleCentral := 4, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 4, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 1, orbitMiddleState := 4, orbitMiddleCentral := 5, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 4, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 1, orbitMiddleState := 4, orbitMiddleCentral := 0, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 4, orbitPenultimateCentral := 0 }
  ]


end GroupTheory
end McKayConjecture
