/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 150–159

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 150. -/
def alternatingSixSchurConjugacyDatumRow150 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 23, conjugatorState := 111, orbitMiddleState := 248, orbitMiddleCentral := 2, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 158, orbitPenultimateCentral := 3 },
    { classIndex := 24, conjugatorState := 111, orbitMiddleState := 248, orbitMiddleCentral := 3, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 158, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 111, orbitMiddleState := 248, orbitMiddleCentral := 4, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 158, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 111, orbitMiddleState := 248, orbitMiddleCentral := 5, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 158, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 111, orbitMiddleState := 248, orbitMiddleCentral := 0, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 158, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 111, orbitMiddleState := 248, orbitMiddleCentral := 1, conjugatorInverseState := 95, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 158, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 151. -/
def alternatingSixSchurConjugacyDatumRow151 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 94, orbitMiddleState := 136, orbitMiddleCentral := 1, conjugatorInverseState := 77, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 153, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 94, orbitMiddleState := 136, orbitMiddleCentral := 2, conjugatorInverseState := 77, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 153, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 94, orbitMiddleState := 136, orbitMiddleCentral := 3, conjugatorInverseState := 77, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 153, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 94, orbitMiddleState := 136, orbitMiddleCentral := 4, conjugatorInverseState := 77, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 153, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 94, orbitMiddleState := 136, orbitMiddleCentral := 5, conjugatorInverseState := 77, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 153, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 94, orbitMiddleState := 136, orbitMiddleCentral := 0, conjugatorInverseState := 77, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 153, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 152. -/
def alternatingSixSchurConjugacyDatumRow152 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 84, orbitMiddleState := 85, orbitMiddleCentral := 2, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 231, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 84, orbitMiddleState := 85, orbitMiddleCentral := 3, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 231, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 84, orbitMiddleState := 85, orbitMiddleCentral := 4, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 231, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 84, orbitMiddleState := 85, orbitMiddleCentral := 5, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 231, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 84, orbitMiddleState := 85, orbitMiddleCentral := 0, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 231, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 84, orbitMiddleState := 85, orbitMiddleCentral := 1, conjugatorInverseState := 89, conjugatorInverseCentral := 2, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 231, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 153. -/
def alternatingSixSchurConjugacyDatumRow153 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 23, conjugatorState := 91, orbitMiddleState := 135, orbitMiddleCentral := 3, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 4 },
    { classIndex := 24, conjugatorState := 91, orbitMiddleState := 135, orbitMiddleCentral := 4, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 5 },
    { classIndex := 25, conjugatorState := 91, orbitMiddleState := 135, orbitMiddleCentral := 5, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 0 },
    { classIndex := 26, conjugatorState := 91, orbitMiddleState := 135, orbitMiddleCentral := 0, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 1 },
    { classIndex := 21, conjugatorState := 91, orbitMiddleState := 135, orbitMiddleCentral := 1, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 2 },
    { classIndex := 22, conjugatorState := 91, orbitMiddleState := 135, orbitMiddleCentral := 2, conjugatorInverseState := 91, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 154. -/
def alternatingSixSchurConjugacyDatumRow154 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 27, orbitMiddleState := 28, orbitMiddleCentral := 2, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 73, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 27, orbitMiddleState := 28, orbitMiddleCentral := 3, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 73, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 27, orbitMiddleState := 28, orbitMiddleCentral := 4, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 73, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 27, orbitMiddleState := 28, orbitMiddleCentral := 5, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 73, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 27, orbitMiddleState := 28, orbitMiddleCentral := 0, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 73, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 27, orbitMiddleState := 28, orbitMiddleCentral := 1, conjugatorInverseState := 20, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 4, orbitPenultimateState := 73, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 155. -/
def alternatingSixSchurConjugacyDatumRow155 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 95, orbitMiddleState := 136, orbitMiddleCentral := 3, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 1 },
    { classIndex := 25, conjugatorState := 95, orbitMiddleState := 136, orbitMiddleCentral := 4, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 95, orbitMiddleState := 136, orbitMiddleCentral := 5, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 95, orbitMiddleState := 136, orbitMiddleCentral := 0, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 95, orbitMiddleState := 136, orbitMiddleCentral := 1, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 95, orbitMiddleState := 136, orbitMiddleCentral := 2, conjugatorInverseState := 111, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 93, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 156. -/
def alternatingSixSchurConjugacyDatumRow156 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 53, orbitMiddleState := 80, orbitMiddleCentral := 3, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 119, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 53, orbitMiddleState := 80, orbitMiddleCentral := 4, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 119, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 53, orbitMiddleState := 80, orbitMiddleCentral := 5, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 119, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 53, orbitMiddleState := 80, orbitMiddleCentral := 0, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 119, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 53, orbitMiddleState := 80, orbitMiddleCentral := 1, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 119, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 53, orbitMiddleState := 80, orbitMiddleCentral := 2, conjugatorInverseState := 58, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 119, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 157. -/
def alternatingSixSchurConjugacyDatumRow157 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 41, orbitMiddleState := 98, orbitMiddleCentral := 1, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 41, orbitMiddleState := 98, orbitMiddleCentral := 2, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 41, orbitMiddleState := 98, orbitMiddleCentral := 3, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 41, orbitMiddleState := 98, orbitMiddleCentral := 4, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 41, orbitMiddleState := 98, orbitMiddleCentral := 5, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 41, orbitMiddleState := 98, orbitMiddleCentral := 0, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 158. -/
def alternatingSixSchurConjugacyDatumRow158 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 4, orbitMiddleState := 159, orbitMiddleCentral := 1, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 112, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 41, orbitMiddleState := 317, orbitMiddleCentral := 0, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 248, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 41, orbitMiddleState := 317, orbitMiddleCentral := 1, conjugatorInverseState := 38, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 248, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 168, orbitMiddleState := 332, orbitMiddleCentral := 1, conjugatorInverseState := 207, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 216, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 168, orbitMiddleState := 332, orbitMiddleCentral := 2, conjugatorInverseState := 207, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 216, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 4, orbitMiddleState := 159, orbitMiddleCentral := 0, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 112, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 159. -/
def alternatingSixSchurConjugacyDatumRow159 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 14, orbitMiddleState := 49, orbitMiddleCentral := 4, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 75, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 14, orbitMiddleState := 49, orbitMiddleCentral := 5, conjugatorInverseState := 10, conjugatorInverseCentral := 2, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 75, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 230, orbitMiddleState := 238, orbitMiddleCentral := 1, conjugatorInverseState := 235, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 203, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 230, orbitMiddleState := 238, orbitMiddleCentral := 2, conjugatorInverseState := 235, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 203, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 139, orbitMiddleState := 162, orbitMiddleCentral := 3, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 76, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 139, orbitMiddleState := 162, orbitMiddleCentral := 4, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 76, orbitPenultimateCentral := 5 }
  ]


end GroupTheory
end McKayConjecture
