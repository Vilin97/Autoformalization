/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 40–49

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 40. -/
def alternatingSixSchurConjugacyDatumRow040 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 25, orbitMiddleState := 98, orbitMiddleCentral := 3, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 41, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 25, orbitMiddleState := 98, orbitMiddleCentral := 4, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 41, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 25, orbitMiddleState := 98, orbitMiddleCentral := 5, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 41, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 25, orbitMiddleState := 98, orbitMiddleCentral := 0, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 41, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 25, orbitMiddleState := 98, orbitMiddleCentral := 1, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 41, orbitPenultimateCentral := 2 },
    { classIndex := 21, conjugatorState := 25, orbitMiddleState := 98, orbitMiddleCentral := 2, conjugatorInverseState := 28, conjugatorInverseCentral := 2, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 41, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 41. -/
def alternatingSixSchurConjugacyDatumRow041 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 263, orbitMiddleState := 294, orbitMiddleCentral := 2, conjugatorInverseState := 274, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 55, inverseFactorRightCentral := 3, orbitPenultimateState := 254, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 263, orbitMiddleState := 294, orbitMiddleCentral := 3, conjugatorInverseState := 274, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 55, inverseFactorRightCentral := 3, orbitPenultimateState := 254, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 263, orbitMiddleState := 294, orbitMiddleCentral := 4, conjugatorInverseState := 274, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 55, inverseFactorRightCentral := 3, orbitPenultimateState := 254, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 263, orbitMiddleState := 294, orbitMiddleCentral := 5, conjugatorInverseState := 274, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 55, inverseFactorRightCentral := 3, orbitPenultimateState := 254, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 263, orbitMiddleState := 294, orbitMiddleCentral := 0, conjugatorInverseState := 274, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 55, inverseFactorRightCentral := 3, orbitPenultimateState := 254, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 263, orbitMiddleState := 294, orbitMiddleCentral := 1, conjugatorInverseState := 274, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 55, inverseFactorRightCentral := 3, orbitPenultimateState := 254, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 42. -/
def alternatingSixSchurConjugacyDatumRow042 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 13, orbitMiddleState := 64, orbitMiddleCentral := 0, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 41, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 13, orbitMiddleState := 64, orbitMiddleCentral := 1, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 41, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 13, orbitMiddleState := 64, orbitMiddleCentral := 2, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 41, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 13, orbitMiddleState := 64, orbitMiddleCentral := 3, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 41, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 13, orbitMiddleState := 64, orbitMiddleCentral := 4, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 41, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 13, orbitMiddleState := 64, orbitMiddleCentral := 5, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 41, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 43. -/
def alternatingSixSchurConjugacyDatumRow043 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 90, orbitMiddleState := 132, orbitMiddleCentral := 0, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 102, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 90, orbitMiddleState := 132, orbitMiddleCentral := 1, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 102, orbitPenultimateCentral := 5 },
    { classIndex := 8, conjugatorState := 90, orbitMiddleState := 132, orbitMiddleCentral := 2, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 102, orbitPenultimateCentral := 0 },
    { classIndex := 6, conjugatorState := 7, orbitMiddleState := 14, orbitMiddleCentral := 0, conjugatorInverseState := 7, conjugatorInverseCentral := 3, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 3, orbitPenultimateState := 25, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 7, orbitMiddleState := 14, orbitMiddleCentral := 1, conjugatorInverseState := 7, conjugatorInverseCentral := 3, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 3, orbitPenultimateState := 25, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 7, orbitMiddleState := 14, orbitMiddleCentral := 2, conjugatorInverseState := 7, conjugatorInverseCentral := 3, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 3, orbitPenultimateState := 25, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 44. -/
def alternatingSixSchurConjugacyDatumRow044 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 15, orbitMiddleState := 70, orbitMiddleCentral := 1, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 45, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 15, orbitMiddleState := 70, orbitMiddleCentral := 2, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 45, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 15, orbitMiddleState := 70, orbitMiddleCentral := 3, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 45, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 15, orbitMiddleState := 70, orbitMiddleCentral := 4, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 45, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 15, orbitMiddleState := 70, orbitMiddleCentral := 5, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 45, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 15, orbitMiddleState := 70, orbitMiddleCentral := 0, conjugatorInverseState := 15, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 45, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 45. -/
def alternatingSixSchurConjugacyDatumRow045 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 8, orbitMiddleState := 15, orbitMiddleCentral := 1, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 27, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 8, orbitMiddleState := 15, orbitMiddleCentral := 2, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 27, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 8, orbitMiddleState := 15, orbitMiddleCentral := 3, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 27, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 8, orbitMiddleState := 15, orbitMiddleCentral := 4, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 27, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 8, orbitMiddleState := 15, orbitMiddleCentral := 5, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 27, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 8, orbitMiddleState := 15, orbitMiddleCentral := 0, conjugatorInverseState := 4, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 5, orbitPenultimateState := 27, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 46. -/
def alternatingSixSchurConjugacyDatumRow046 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 26, orbitMiddleState := 103, orbitMiddleCentral := 3, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 45, orbitPenultimateCentral := 1 },
    { classIndex := 25, conjugatorState := 26, orbitMiddleState := 103, orbitMiddleCentral := 4, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 45, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 26, orbitMiddleState := 103, orbitMiddleCentral := 5, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 45, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 26, orbitMiddleState := 103, orbitMiddleCentral := 0, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 45, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 26, orbitMiddleState := 103, orbitMiddleCentral := 1, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 45, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 26, orbitMiddleState := 103, orbitMiddleCentral := 2, conjugatorInverseState := 23, conjugatorInverseCentral := 2, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 7, inverseFactorRightCentral := 2, orbitPenultimateState := 45, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 47. -/
def alternatingSixSchurConjugacyDatumRow047 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 17, orbitMiddleState := 48, orbitMiddleCentral := 4, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 16, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 17, orbitMiddleState := 48, orbitMiddleCentral := 5, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 16, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 17, orbitMiddleState := 48, orbitMiddleCentral := 0, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 16, orbitPenultimateCentral := 1 },
    { classIndex := 25, conjugatorState := 17, orbitMiddleState := 48, orbitMiddleCentral := 1, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 16, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 17, orbitMiddleState := 48, orbitMiddleCentral := 2, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 16, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 17, orbitMiddleState := 48, orbitMiddleCentral := 3, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 16, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 48. -/
def alternatingSixSchurConjugacyDatumRow048 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 279, orbitMiddleState := 313, orbitMiddleCentral := 1, conjugatorInverseState := 268, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 69, inverseFactorRightCentral := 3, orbitPenultimateState := 262, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 279, orbitMiddleState := 313, orbitMiddleCentral := 2, conjugatorInverseState := 268, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 69, inverseFactorRightCentral := 3, orbitPenultimateState := 262, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 279, orbitMiddleState := 313, orbitMiddleCentral := 3, conjugatorInverseState := 268, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 69, inverseFactorRightCentral := 3, orbitPenultimateState := 262, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 279, orbitMiddleState := 313, orbitMiddleCentral := 4, conjugatorInverseState := 268, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 69, inverseFactorRightCentral := 3, orbitPenultimateState := 262, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 279, orbitMiddleState := 313, orbitMiddleCentral := 5, conjugatorInverseState := 268, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 69, inverseFactorRightCentral := 3, orbitPenultimateState := 262, orbitPenultimateCentral := 2 },
    { classIndex := 9, conjugatorState := 279, orbitMiddleState := 313, orbitMiddleCentral := 0, conjugatorInverseState := 268, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 69, inverseFactorRightCentral := 3, orbitPenultimateState := 262, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 49. -/
def alternatingSixSchurConjugacyDatumRow049 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 129, orbitMiddleState := 178, orbitMiddleCentral := 1, conjugatorInverseState := 114, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 114, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 129, orbitMiddleState := 178, orbitMiddleCentral := 2, conjugatorInverseState := 114, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 114, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 129, orbitMiddleState := 178, orbitMiddleCentral := 3, conjugatorInverseState := 114, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 114, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 129, orbitMiddleState := 178, orbitMiddleCentral := 4, conjugatorInverseState := 114, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 114, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 129, orbitMiddleState := 178, orbitMiddleCentral := 5, conjugatorInverseState := 114, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 114, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 129, orbitMiddleState := 178, orbitMiddleCentral := 0, conjugatorInverseState := 114, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 5, orbitPenultimateState := 114, orbitPenultimateCentral := 2 }
  ]


end GroupTheory
end McKayConjecture
