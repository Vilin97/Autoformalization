/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 30–39

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 30. -/
def alternatingSixSchurConjugacyDatumRow030 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 4, orbitMiddleState := 31, orbitMiddleCentral := 1, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 17, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 4, orbitMiddleState := 31, orbitMiddleCentral := 2, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 17, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 4, orbitMiddleState := 31, orbitMiddleCentral := 3, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 17, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 4, orbitMiddleState := 31, orbitMiddleCentral := 4, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 17, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 4, orbitMiddleState := 31, orbitMiddleCentral := 5, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 17, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 4, orbitMiddleState := 31, orbitMiddleCentral := 0, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 17, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 31. -/
def alternatingSixSchurConjugacyDatumRow031 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 16, orbitMiddleState := 49, orbitMiddleCentral := 0, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 30, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 16, orbitMiddleState := 49, orbitMiddleCentral := 1, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 30, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 16, orbitMiddleState := 49, orbitMiddleCentral := 2, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 30, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 16, orbitMiddleState := 49, orbitMiddleCentral := 3, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 30, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 16, orbitMiddleState := 49, orbitMiddleCentral := 4, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 30, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 16, orbitMiddleState := 49, orbitMiddleCentral := 5, conjugatorInverseState := 12, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 4, inverseFactorRightCentral := 5, orbitPenultimateState := 30, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 32. -/
def alternatingSixSchurConjugacyDatumRow032 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 4, orbitMiddleState := 9, orbitMiddleCentral := 1, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 18, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 4, orbitMiddleState := 9, orbitMiddleCentral := 2, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 18, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 40, orbitMiddleState := 63, orbitMiddleCentral := 0, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 118, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 40, orbitMiddleState := 63, orbitMiddleCentral := 1, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 118, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 40, orbitMiddleState := 63, orbitMiddleCentral := 2, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 118, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 4, orbitMiddleState := 9, orbitMiddleCentral := 0, conjugatorInverseState := 8, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 18, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 33. -/
def alternatingSixSchurConjugacyDatumRow033 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 18, orbitMiddleState := 79, orbitMiddleCentral := 0, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 80, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 18, orbitMiddleState := 79, orbitMiddleCentral := 1, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 80, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 18, orbitMiddleState := 79, orbitMiddleCentral := 2, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 80, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 18, orbitMiddleState := 79, orbitMiddleCentral := 3, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 80, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 18, orbitMiddleState := 79, orbitMiddleCentral := 4, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 80, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 18, orbitMiddleState := 79, orbitMiddleCentral := 5, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 80, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 34. -/
def alternatingSixSchurConjugacyDatumRow034 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 20, orbitMiddleState := 85, orbitMiddleCentral := 1, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 84, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 20, orbitMiddleState := 85, orbitMiddleCentral := 2, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 84, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 20, orbitMiddleState := 85, orbitMiddleCentral := 3, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 84, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 20, orbitMiddleState := 85, orbitMiddleCentral := 4, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 84, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 20, orbitMiddleState := 85, orbitMiddleCentral := 5, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 84, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 20, orbitMiddleState := 85, orbitMiddleCentral := 0, conjugatorInverseState := 27, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 84, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 35. -/
def alternatingSixSchurConjugacyDatumRow035 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 7, conjugatorState := 5, orbitMiddleState := 11, orbitMiddleCentral := 1, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 20, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 5, orbitMiddleState := 11, orbitMiddleCentral := 2, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 20, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 46, orbitMiddleState := 71, orbitMiddleCentral := 0, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 125, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 46, orbitMiddleState := 71, orbitMiddleCentral := 1, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 125, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 46, orbitMiddleState := 71, orbitMiddleCentral := 2, conjugatorInverseState := 40, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 125, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 5, orbitMiddleState := 11, orbitMiddleCentral := 0, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 20, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 36. -/
def alternatingSixSchurConjugacyDatumRow036 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 12, orbitMiddleState := 59, orbitMiddleCentral := 3, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 37, orbitPenultimateCentral := 3 },
    { classIndex := 23, conjugatorState := 12, orbitMiddleState := 59, orbitMiddleCentral := 4, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 37, orbitPenultimateCentral := 4 },
    { classIndex := 24, conjugatorState := 12, orbitMiddleState := 59, orbitMiddleCentral := 5, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 37, orbitPenultimateCentral := 5 },
    { classIndex := 25, conjugatorState := 12, orbitMiddleState := 59, orbitMiddleCentral := 0, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 37, orbitPenultimateCentral := 0 },
    { classIndex := 26, conjugatorState := 12, orbitMiddleState := 59, orbitMiddleCentral := 1, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 37, orbitPenultimateCentral := 1 },
    { classIndex := 21, conjugatorState := 12, orbitMiddleState := 59, orbitMiddleCentral := 2, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 37, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 37. -/
def alternatingSixSchurConjugacyDatumRow037 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 5, orbitMiddleState := 36, orbitMiddleCentral := 4, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 21, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 5, orbitMiddleState := 36, orbitMiddleCentral := 5, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 21, orbitPenultimateCentral := 2 },
    { classIndex := 21, conjugatorState := 5, orbitMiddleState := 36, orbitMiddleCentral := 0, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 21, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 5, orbitMiddleState := 36, orbitMiddleCentral := 1, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 21, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 5, orbitMiddleState := 36, orbitMiddleCentral := 2, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 21, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 5, orbitMiddleState := 36, orbitMiddleCentral := 3, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 21, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 38. -/
def alternatingSixSchurConjugacyDatumRow038 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 6, orbitMiddleState := 12, orbitMiddleCentral := 1, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 22, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 6, orbitMiddleState := 12, orbitMiddleCentral := 2, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 22, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 6, orbitMiddleState := 12, orbitMiddleCentral := 3, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 22, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 6, orbitMiddleState := 12, orbitMiddleCentral := 4, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 22, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 6, orbitMiddleState := 12, orbitMiddleCentral := 5, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 22, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 6, orbitMiddleState := 12, orbitMiddleCentral := 0, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 22, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 39. -/
def alternatingSixSchurConjugacyDatumRow039 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 21, orbitMiddleState := 38, orbitMiddleCentral := 1, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 12, orbitPenultimateCentral := 2 },
    { classIndex := 22, conjugatorState := 21, orbitMiddleState := 38, orbitMiddleCentral := 2, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 12, orbitPenultimateCentral := 3 },
    { classIndex := 23, conjugatorState := 21, orbitMiddleState := 38, orbitMiddleCentral := 3, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 12, orbitPenultimateCentral := 4 },
    { classIndex := 24, conjugatorState := 21, orbitMiddleState := 38, orbitMiddleCentral := 4, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 12, orbitPenultimateCentral := 5 },
    { classIndex := 25, conjugatorState := 21, orbitMiddleState := 38, orbitMiddleCentral := 5, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 12, orbitPenultimateCentral := 0 },
    { classIndex := 26, conjugatorState := 21, orbitMiddleState := 38, orbitMiddleCentral := 0, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 12, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
