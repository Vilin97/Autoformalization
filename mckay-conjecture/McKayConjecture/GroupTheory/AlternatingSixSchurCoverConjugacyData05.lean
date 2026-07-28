/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 50–59

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 50. -/
def alternatingSixSchurConjugacyDatumRow050 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 18, conjugatorState := 106, orbitMiddleState := 208, orbitMiddleCentral := 3, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 218, orbitPenultimateCentral := 1 },
    { classIndex := 19, conjugatorState := 106, orbitMiddleState := 208, orbitMiddleCentral := 4, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 218, orbitPenultimateCentral := 2 },
    { classIndex := 20, conjugatorState := 106, orbitMiddleState := 208, orbitMiddleCentral := 5, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 218, orbitPenultimateCentral := 3 },
    { classIndex := 15, conjugatorState := 106, orbitMiddleState := 208, orbitMiddleCentral := 0, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 218, orbitPenultimateCentral := 4 },
    { classIndex := 16, conjugatorState := 106, orbitMiddleState := 208, orbitMiddleCentral := 1, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 218, orbitPenultimateCentral := 5 },
    { classIndex := 17, conjugatorState := 106, orbitMiddleState := 208, orbitMiddleCentral := 2, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 218, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 51. -/
def alternatingSixSchurConjugacyDatumRow051 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 145, orbitMiddleState := 199, orbitMiddleCentral := 1, conjugatorInverseState := 115, conjugatorInverseCentral := 3, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 53, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 145, orbitMiddleState := 199, orbitMiddleCentral := 2, conjugatorInverseState := 115, conjugatorInverseCentral := 3, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 53, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 145, orbitMiddleState := 199, orbitMiddleCentral := 3, conjugatorInverseState := 115, conjugatorInverseCentral := 3, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 53, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 145, orbitMiddleState := 199, orbitMiddleCentral := 4, conjugatorInverseState := 115, conjugatorInverseCentral := 3, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 53, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 145, orbitMiddleState := 199, orbitMiddleCentral := 5, conjugatorInverseState := 115, conjugatorInverseCentral := 3, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 53, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 145, orbitMiddleState := 199, orbitMiddleCentral := 0, conjugatorInverseState := 115, conjugatorInverseCentral := 3, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 3, orbitPenultimateState := 53, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 52. -/
def alternatingSixSchurConjugacyDatumRow052 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 310, orbitMiddleState := 342, orbitMiddleCentral := 2, conjugatorInverseState := 302, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 3, orbitPenultimateState := 100, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 310, orbitMiddleState := 342, orbitMiddleCentral := 3, conjugatorInverseState := 302, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 3, orbitPenultimateState := 100, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 310, orbitMiddleState := 342, orbitMiddleCentral := 4, conjugatorInverseState := 302, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 3, orbitPenultimateState := 100, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 310, orbitMiddleState := 342, orbitMiddleCentral := 5, conjugatorInverseState := 302, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 3, orbitPenultimateState := 100, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 310, orbitMiddleState := 342, orbitMiddleCentral := 0, conjugatorInverseState := 302, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 3, orbitPenultimateState := 100, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 310, orbitMiddleState := 342, orbitMiddleCentral := 1, conjugatorInverseState := 302, conjugatorInverseCentral := 3, inverseFactorLeftState := 50, inverseFactorLeftCentral := 0, inverseFactorRightState := 63, inverseFactorRightCentral := 3, orbitPenultimateState := 100, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 53. -/
def alternatingSixSchurConjugacyDatumRow053 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 18, conjugatorState := 137, orbitMiddleState := 138, orbitMiddleCentral := 4, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 119, orbitPenultimateCentral := 2 },
    { classIndex := 19, conjugatorState := 137, orbitMiddleState := 138, orbitMiddleCentral := 5, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 119, orbitPenultimateCentral := 3 },
    { classIndex := 20, conjugatorState := 137, orbitMiddleState := 138, orbitMiddleCentral := 0, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 119, orbitPenultimateCentral := 4 },
    { classIndex := 15, conjugatorState := 137, orbitMiddleState := 138, orbitMiddleCentral := 1, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 119, orbitPenultimateCentral := 5 },
    { classIndex := 16, conjugatorState := 137, orbitMiddleState := 138, orbitMiddleCentral := 2, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 119, orbitPenultimateCentral := 0 },
    { classIndex := 17, conjugatorState := 137, orbitMiddleState := 138, orbitMiddleCentral := 3, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 119, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 54. -/
def alternatingSixSchurConjugacyDatumRow054 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 18, conjugatorState := 282, orbitMiddleState := 345, orbitMiddleCentral := 2, conjugatorInverseState := 285, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 0 },
    { classIndex := 19, conjugatorState := 282, orbitMiddleState := 345, orbitMiddleCentral := 3, conjugatorInverseState := 285, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 1 },
    { classIndex := 20, conjugatorState := 282, orbitMiddleState := 345, orbitMiddleCentral := 4, conjugatorInverseState := 285, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 2 },
    { classIndex := 15, conjugatorState := 282, orbitMiddleState := 345, orbitMiddleCentral := 5, conjugatorInverseState := 285, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 3 },
    { classIndex := 16, conjugatorState := 282, orbitMiddleState := 345, orbitMiddleCentral := 0, conjugatorInverseState := 285, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 4 },
    { classIndex := 17, conjugatorState := 282, orbitMiddleState := 345, orbitMiddleCentral := 1, conjugatorInverseState := 285, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 73, inverseFactorRightCentral := 4, orbitPenultimateState := 228, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 55. -/
def alternatingSixSchurConjugacyDatumRow055 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 9, orbitMiddleState := 10, orbitMiddleCentral := 2, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 19, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 9, orbitMiddleState := 10, orbitMiddleCentral := 3, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 19, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 9, orbitMiddleState := 10, orbitMiddleCentral := 4, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 19, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 9, orbitMiddleState := 10, orbitMiddleCentral := 5, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 19, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 9, orbitMiddleState := 10, orbitMiddleCentral := 0, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 19, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 9, orbitMiddleState := 10, orbitMiddleCentral := 1, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 19, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 56. -/
def alternatingSixSchurConjugacyDatumRow056 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 92, orbitMiddleState := 134, orbitMiddleCentral := 3, conjugatorInverseState := 88, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 184, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 92, orbitMiddleState := 134, orbitMiddleCentral := 4, conjugatorInverseState := 88, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 184, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 92, orbitMiddleState := 134, orbitMiddleCentral := 5, conjugatorInverseState := 88, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 184, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 92, orbitMiddleState := 134, orbitMiddleCentral := 0, conjugatorInverseState := 88, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 184, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 92, orbitMiddleState := 134, orbitMiddleCentral := 1, conjugatorInverseState := 88, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 184, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 92, orbitMiddleState := 134, orbitMiddleCentral := 2, conjugatorInverseState := 88, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 184, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 57. -/
def alternatingSixSchurConjugacyDatumRow057 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 332, orbitMiddleState := 346, orbitMiddleCentral := 3, conjugatorInverseState := 311, conjugatorInverseCentral := 3, inverseFactorLeftState := 57, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 3, orbitPenultimateState := 201, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 332, orbitMiddleState := 346, orbitMiddleCentral := 4, conjugatorInverseState := 311, conjugatorInverseCentral := 3, inverseFactorLeftState := 57, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 3, orbitPenultimateState := 201, orbitPenultimateCentral := 4 },
    { classIndex := 13, conjugatorState := 332, orbitMiddleState := 346, orbitMiddleCentral := 5, conjugatorInverseState := 311, conjugatorInverseCentral := 3, inverseFactorLeftState := 57, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 3, orbitPenultimateState := 201, orbitPenultimateCentral := 5 },
    { classIndex := 14, conjugatorState := 332, orbitMiddleState := 346, orbitMiddleCentral := 0, conjugatorInverseState := 311, conjugatorInverseCentral := 3, inverseFactorLeftState := 57, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 3, orbitPenultimateState := 201, orbitPenultimateCentral := 0 },
    { classIndex := 9, conjugatorState := 332, orbitMiddleState := 346, orbitMiddleCentral := 1, conjugatorInverseState := 311, conjugatorInverseCentral := 3, inverseFactorLeftState := 57, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 3, orbitPenultimateState := 201, orbitPenultimateCentral := 1 },
    { classIndex := 10, conjugatorState := 332, orbitMiddleState := 346, orbitMiddleCentral := 2, conjugatorInverseState := 311, conjugatorInverseCentral := 3, inverseFactorLeftState := 57, inverseFactorLeftCentral := 0, inverseFactorRightState := 56, inverseFactorRightCentral := 3, orbitPenultimateState := 201, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 58. -/
def alternatingSixSchurConjugacyDatumRow058 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 5, orbitMiddleState := 20, orbitMiddleCentral := 1, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 36, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 5, orbitMiddleState := 20, orbitMiddleCentral := 2, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 36, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 5, orbitMiddleState := 20, orbitMiddleCentral := 3, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 36, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 5, orbitMiddleState := 20, orbitMiddleCentral := 4, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 36, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 5, orbitMiddleState := 20, orbitMiddleCentral := 5, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 36, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 5, orbitMiddleState := 20, orbitMiddleCentral := 0, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 36, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 59. -/
def alternatingSixSchurConjugacyDatumRow059 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 286, orbitMiddleState := 319, orbitMiddleCentral := 1, conjugatorInverseState := 278, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 239, orbitPenultimateCentral := 0 },
    { classIndex := 12, conjugatorState := 286, orbitMiddleState := 319, orbitMiddleCentral := 2, conjugatorInverseState := 278, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 239, orbitPenultimateCentral := 1 },
    { classIndex := 13, conjugatorState := 286, orbitMiddleState := 319, orbitMiddleCentral := 3, conjugatorInverseState := 278, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 239, orbitPenultimateCentral := 2 },
    { classIndex := 14, conjugatorState := 286, orbitMiddleState := 319, orbitMiddleCentral := 4, conjugatorInverseState := 278, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 239, orbitPenultimateCentral := 3 },
    { classIndex := 9, conjugatorState := 286, orbitMiddleState := 319, orbitMiddleCentral := 5, conjugatorInverseState := 278, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 239, orbitPenultimateCentral := 4 },
    { classIndex := 10, conjugatorState := 286, orbitMiddleState := 319, orbitMiddleCentral := 0, conjugatorInverseState := 278, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 239, orbitPenultimateCentral := 5 }
  ]


end GroupTheory
end McKayConjecture
