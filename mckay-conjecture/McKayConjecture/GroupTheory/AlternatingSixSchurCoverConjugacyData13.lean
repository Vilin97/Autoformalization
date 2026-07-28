/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 130–139

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 130. -/
def alternatingSixSchurConjugacyDatumRow130 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 96, orbitMiddleState := 117, orbitMiddleCentral := 0, conjugatorInverseState := 96, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 190, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 96, orbitMiddleState := 117, orbitMiddleCentral := 1, conjugatorInverseState := 96, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 190, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 96, orbitMiddleState := 117, orbitMiddleCentral := 2, conjugatorInverseState := 96, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 190, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 96, orbitMiddleState := 117, orbitMiddleCentral := 3, conjugatorInverseState := 96, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 190, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 96, orbitMiddleState := 117, orbitMiddleCentral := 4, conjugatorInverseState := 96, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 190, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 96, orbitMiddleState := 117, orbitMiddleCentral := 5, conjugatorInverseState := 96, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 3, orbitPenultimateState := 190, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 131. -/
def alternatingSixSchurConjugacyDatumRow131 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 52, orbitMiddleState := 120, orbitMiddleCentral := 1, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 168, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 52, orbitMiddleState := 120, orbitMiddleCentral := 2, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 168, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 52, orbitMiddleState := 120, orbitMiddleCentral := 3, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 168, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 52, orbitMiddleState := 120, orbitMiddleCentral := 4, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 168, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 52, orbitMiddleState := 120, orbitMiddleCentral := 5, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 168, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 52, orbitMiddleState := 120, orbitMiddleCentral := 0, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 168, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 132. -/
def alternatingSixSchurConjugacyDatumRow132 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 21, orbitMiddleState := 59, orbitMiddleCentral := 1, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 60, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 21, orbitMiddleState := 59, orbitMiddleCentral := 2, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 60, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 21, orbitMiddleState := 59, orbitMiddleCentral := 3, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 60, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 21, orbitMiddleState := 59, orbitMiddleCentral := 4, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 60, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 21, orbitMiddleState := 59, orbitMiddleCentral := 5, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 60, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 21, orbitMiddleState := 59, orbitMiddleCentral := 0, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 60, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 133. -/
def alternatingSixSchurConjugacyDatumRow133 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 265, orbitMiddleState := 303, orbitMiddleCentral := 5, conjugatorInverseState := 270, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 71, inverseFactorRightCentral := 3, orbitPenultimateState := 106, orbitPenultimateCentral := 0 },
    { classIndex := 9, conjugatorState := 265, orbitMiddleState := 303, orbitMiddleCentral := 0, conjugatorInverseState := 270, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 71, inverseFactorRightCentral := 3, orbitPenultimateState := 106, orbitPenultimateCentral := 1 },
    { classIndex := 10, conjugatorState := 265, orbitMiddleState := 303, orbitMiddleCentral := 1, conjugatorInverseState := 270, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 71, inverseFactorRightCentral := 3, orbitPenultimateState := 106, orbitPenultimateCentral := 2 },
    { classIndex := 11, conjugatorState := 265, orbitMiddleState := 303, orbitMiddleCentral := 2, conjugatorInverseState := 270, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 71, inverseFactorRightCentral := 3, orbitPenultimateState := 106, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 265, orbitMiddleState := 303, orbitMiddleCentral := 3, conjugatorInverseState := 270, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 71, inverseFactorRightCentral := 3, orbitPenultimateState := 106, orbitPenultimateCentral := 4 },
    { classIndex := 13, conjugatorState := 265, orbitMiddleState := 303, orbitMiddleCentral := 4, conjugatorInverseState := 270, conjugatorInverseCentral := 3, inverseFactorLeftState := 32, inverseFactorLeftCentral := 0, inverseFactorRightState := 71, inverseFactorRightCentral := 3, orbitPenultimateState := 106, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 134. -/
def alternatingSixSchurConjugacyDatumRow134 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 106, orbitMiddleState := 153, orbitMiddleCentral := 4, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 5 },
    { classIndex := 25, conjugatorState := 106, orbitMiddleState := 153, orbitMiddleCentral := 5, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 0 },
    { classIndex := 26, conjugatorState := 106, orbitMiddleState := 153, orbitMiddleCentral := 0, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 1 },
    { classIndex := 21, conjugatorState := 106, orbitMiddleState := 153, orbitMiddleCentral := 1, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 2 },
    { classIndex := 22, conjugatorState := 106, orbitMiddleState := 153, orbitMiddleCentral := 2, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 3 },
    { classIndex := 23, conjugatorState := 106, orbitMiddleState := 153, orbitMiddleCentral := 3, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 135. -/
def alternatingSixSchurConjugacyDatumRow135 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 18, conjugatorState := 200, orbitMiddleState := 201, orbitMiddleCentral := 4, conjugatorInverseState := 180, conjugatorInverseCentral := 5, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 5, orbitPenultimateState := 184, orbitPenultimateCentral := 2 },
    { classIndex := 19, conjugatorState := 200, orbitMiddleState := 201, orbitMiddleCentral := 5, conjugatorInverseState := 180, conjugatorInverseCentral := 5, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 5, orbitPenultimateState := 184, orbitPenultimateCentral := 3 },
    { classIndex := 20, conjugatorState := 200, orbitMiddleState := 201, orbitMiddleCentral := 0, conjugatorInverseState := 180, conjugatorInverseCentral := 5, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 5, orbitPenultimateState := 184, orbitPenultimateCentral := 4 },
    { classIndex := 15, conjugatorState := 200, orbitMiddleState := 201, orbitMiddleCentral := 1, conjugatorInverseState := 180, conjugatorInverseCentral := 5, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 5, orbitPenultimateState := 184, orbitPenultimateCentral := 5 },
    { classIndex := 16, conjugatorState := 200, orbitMiddleState := 201, orbitMiddleCentral := 2, conjugatorInverseState := 180, conjugatorInverseCentral := 5, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 5, orbitPenultimateState := 184, orbitPenultimateCentral := 0 },
    { classIndex := 17, conjugatorState := 200, orbitMiddleState := 201, orbitMiddleCentral := 3, conjugatorInverseState := 180, conjugatorInverseCentral := 5, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 31, inverseFactorRightCentral := 5, orbitPenultimateState := 184, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 136. -/
def alternatingSixSchurConjugacyDatumRow136 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 110, orbitMiddleState := 154, orbitMiddleCentral := 0, conjugatorInverseState := 110, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 110, orbitMiddleState := 154, orbitMiddleCentral := 1, conjugatorInverseState := 110, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 110, orbitMiddleState := 154, orbitMiddleCentral := 2, conjugatorInverseState := 110, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 110, orbitMiddleState := 154, orbitMiddleCentral := 3, conjugatorInverseState := 110, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 1 },
    { classIndex := 25, conjugatorState := 110, orbitMiddleState := 154, orbitMiddleCentral := 4, conjugatorInverseState := 110, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 110, orbitMiddleState := 154, orbitMiddleCentral := 5, conjugatorInverseState := 110, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 3, orbitPenultimateState := 108, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 137. -/
def alternatingSixSchurConjugacyDatumRow137 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 22, orbitMiddleState := 23, orbitMiddleCentral := 2, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 62, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 22, orbitMiddleState := 23, orbitMiddleCentral := 3, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 62, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 22, orbitMiddleState := 23, orbitMiddleCentral := 4, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 62, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 22, orbitMiddleState := 23, orbitMiddleCentral := 5, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 62, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 22, orbitMiddleState := 23, orbitMiddleCentral := 0, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 62, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 22, orbitMiddleState := 23, orbitMiddleCentral := 1, conjugatorInverseState := 21, conjugatorInverseCentral := 4, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 4, orbitPenultimateState := 62, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 138. -/
def alternatingSixSchurConjugacyDatumRow138 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 272, orbitMiddleState := 300, orbitMiddleCentral := 1, conjugatorInverseState := 277, conjugatorInverseCentral := 3, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 74, inverseFactorRightCentral := 3, orbitPenultimateState := 111, orbitPenultimateCentral := 0 },
    { classIndex := 9, conjugatorState := 272, orbitMiddleState := 300, orbitMiddleCentral := 2, conjugatorInverseState := 277, conjugatorInverseCentral := 3, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 74, inverseFactorRightCentral := 3, orbitPenultimateState := 111, orbitPenultimateCentral := 1 },
    { classIndex := 10, conjugatorState := 272, orbitMiddleState := 300, orbitMiddleCentral := 3, conjugatorInverseState := 277, conjugatorInverseCentral := 3, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 74, inverseFactorRightCentral := 3, orbitPenultimateState := 111, orbitPenultimateCentral := 2 },
    { classIndex := 11, conjugatorState := 272, orbitMiddleState := 300, orbitMiddleCentral := 4, conjugatorInverseState := 277, conjugatorInverseCentral := 3, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 74, inverseFactorRightCentral := 3, orbitPenultimateState := 111, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 272, orbitMiddleState := 300, orbitMiddleCentral := 5, conjugatorInverseState := 277, conjugatorInverseCentral := 3, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 74, inverseFactorRightCentral := 3, orbitPenultimateState := 111, orbitPenultimateCentral := 4 },
    { classIndex := 13, conjugatorState := 272, orbitMiddleState := 300, orbitMiddleCentral := 0, conjugatorInverseState := 277, conjugatorInverseCentral := 3, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 74, inverseFactorRightCentral := 3, orbitPenultimateState := 111, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 139. -/
def alternatingSixSchurConjugacyDatumRow139 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 90, orbitMiddleState := 238, orbitMiddleCentral := 0, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 181, orbitPenultimateCentral := 2 },
    { classIndex := 22, conjugatorState := 90, orbitMiddleState := 238, orbitMiddleCentral := 1, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 181, orbitPenultimateCentral := 3 },
    { classIndex := 23, conjugatorState := 90, orbitMiddleState := 238, orbitMiddleCentral := 2, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 181, orbitPenultimateCentral := 4 },
    { classIndex := 24, conjugatorState := 90, orbitMiddleState := 238, orbitMiddleCentral := 3, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 181, orbitPenultimateCentral := 5 },
    { classIndex := 25, conjugatorState := 90, orbitMiddleState := 238, orbitMiddleCentral := 4, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 181, orbitPenultimateCentral := 0 },
    { classIndex := 26, conjugatorState := 90, orbitMiddleState := 238, orbitMiddleCentral := 5, conjugatorInverseState := 106, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 3, orbitPenultimateState := 181, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
