/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 120–129

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 120. -/
def alternatingSixSchurConjugacyDatumRow120 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 143, orbitMiddleState := 198, orbitMiddleCentral := 4, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 143, orbitMiddleState := 198, orbitMiddleCentral := 5, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 143, orbitMiddleState := 198, orbitMiddleCentral := 0, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 143, orbitMiddleState := 198, orbitMiddleCentral := 1, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 143, orbitMiddleState := 198, orbitMiddleCentral := 2, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 143, orbitMiddleState := 198, orbitMiddleCentral := 3, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 121. -/
def alternatingSixSchurConjugacyDatumRow121 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 193, orbitMiddleState := 244, orbitMiddleCentral := 4, conjugatorInverseState := 211, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 139, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 193, orbitMiddleState := 244, orbitMiddleCentral := 5, conjugatorInverseState := 211, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 139, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 193, orbitMiddleState := 244, orbitMiddleCentral := 0, conjugatorInverseState := 211, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 139, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 193, orbitMiddleState := 244, orbitMiddleCentral := 1, conjugatorInverseState := 211, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 139, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 193, orbitMiddleState := 244, orbitMiddleCentral := 2, conjugatorInverseState := 211, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 139, orbitPenultimateCentral := 3 },
    { classIndex := 24, conjugatorState := 193, orbitMiddleState := 244, orbitMiddleCentral := 3, conjugatorInverseState := 211, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 139, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 122. -/
def alternatingSixSchurConjugacyDatumRow122 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 203, orbitMiddleState := 256, orbitMiddleCentral := 3, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 159, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 203, orbitMiddleState := 256, orbitMiddleCentral := 4, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 159, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 203, orbitMiddleState := 256, orbitMiddleCentral := 5, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 159, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 203, orbitMiddleState := 256, orbitMiddleCentral := 0, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 159, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 203, orbitMiddleState := 256, orbitMiddleCentral := 1, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 159, orbitPenultimateCentral := 1 },
    { classIndex := 25, conjugatorState := 203, orbitMiddleState := 256, orbitMiddleCentral := 2, conjugatorInverseState := 185, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 159, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 123. -/
def alternatingSixSchurConjugacyDatumRow123 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 146, orbitMiddleState := 199, orbitMiddleCentral := 0, conjugatorInverseState := 156, conjugatorInverseCentral := 0, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 146, orbitMiddleState := 199, orbitMiddleCentral := 1, conjugatorInverseState := 156, conjugatorInverseCentral := 0, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 146, orbitMiddleState := 199, orbitMiddleCentral := 2, conjugatorInverseState := 156, conjugatorInverseCentral := 0, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 146, orbitMiddleState := 199, orbitMiddleCentral := 3, conjugatorInverseState := 156, conjugatorInverseCentral := 0, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 146, orbitMiddleState := 199, orbitMiddleCentral := 4, conjugatorInverseState := 156, conjugatorInverseCentral := 0, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 146, orbitMiddleState := 199, orbitMiddleCentral := 5, conjugatorInverseState := 156, conjugatorInverseCentral := 0, inverseFactorLeftState := 29, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 54, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 124. -/
def alternatingSixSchurConjugacyDatumRow124 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 202, orbitMiddleState := 314, orbitMiddleCentral := 0, conjugatorInverseState := 208, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 147, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 202, orbitMiddleState := 314, orbitMiddleCentral := 1, conjugatorInverseState := 208, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 147, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 202, orbitMiddleState := 314, orbitMiddleCentral := 2, conjugatorInverseState := 208, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 147, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 202, orbitMiddleState := 314, orbitMiddleCentral := 3, conjugatorInverseState := 208, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 147, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 202, orbitMiddleState := 314, orbitMiddleCentral := 4, conjugatorInverseState := 208, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 147, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 202, orbitMiddleState := 314, orbitMiddleCentral := 5, conjugatorInverseState := 208, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 5, orbitPenultimateState := 147, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 125. -/
def alternatingSixSchurConjugacyDatumRow125 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 266, orbitMiddleState := 305, orbitMiddleCentral := 0, conjugatorInverseState := 292, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 4, orbitPenultimateState := 359, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 266, orbitMiddleState := 305, orbitMiddleCentral := 1, conjugatorInverseState := 292, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 4, orbitPenultimateState := 359, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 266, orbitMiddleState := 305, orbitMiddleCentral := 2, conjugatorInverseState := 292, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 66, inverseFactorRightCentral := 4, orbitPenultimateState := 359, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 242, orbitMiddleState := 286, orbitMiddleCentral := 0, conjugatorInverseState := 260, conjugatorInverseCentral := 5, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 342, orbitPenultimateCentral := 2 },
    { classIndex := 7, conjugatorState := 242, orbitMiddleState := 286, orbitMiddleCentral := 1, conjugatorInverseState := 260, conjugatorInverseCentral := 5, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 342, orbitPenultimateCentral := 3 },
    { classIndex := 8, conjugatorState := 242, orbitMiddleState := 286, orbitMiddleCentral := 2, conjugatorInverseState := 260, conjugatorInverseCentral := 5, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 46, inverseFactorRightCentral := 5, orbitPenultimateState := 342, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 126. -/
def alternatingSixSchurConjugacyDatumRow126 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 69, orbitMiddleState := 70, orbitMiddleCentral := 2, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 69, orbitMiddleState := 70, orbitMiddleCentral := 3, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 69, orbitMiddleState := 70, orbitMiddleCentral := 4, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 69, orbitMiddleState := 70, orbitMiddleCentral := 5, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 69, orbitMiddleState := 70, orbitMiddleCentral := 0, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 69, orbitMiddleState := 70, orbitMiddleCentral := 1, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 206, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 127. -/
def alternatingSixSchurConjugacyDatumRow127 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 31, orbitMiddleState := 50, orbitMiddleCentral := 0, conjugatorInverseState := 44, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 1, orbitPenultimateState := 115, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 31, orbitMiddleState := 50, orbitMiddleCentral := 1, conjugatorInverseState := 44, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 1, orbitPenultimateState := 115, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 31, orbitMiddleState := 50, orbitMiddleCentral := 2, conjugatorInverseState := 44, conjugatorInverseCentral := 1, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 1, orbitPenultimateState := 115, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 72, orbitMiddleState := 107, orbitMiddleCentral := 0, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 218, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 72, orbitMiddleState := 107, orbitMiddleCentral := 1, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 218, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 72, orbitMiddleState := 107, orbitMiddleCentral := 2, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 218, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 128. -/
def alternatingSixSchurConjugacyDatumRow128 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 51, orbitMiddleState := 164, orbitMiddleCentral := 0, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 116, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 51, orbitMiddleState := 164, orbitMiddleCentral := 1, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 116, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 51, orbitMiddleState := 164, orbitMiddleCentral := 2, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 116, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 51, orbitMiddleState := 164, orbitMiddleCentral := 3, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 116, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 51, orbitMiddleState := 164, orbitMiddleCentral := 4, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 116, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 51, orbitMiddleState := 164, orbitMiddleCentral := 5, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 116, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 129. -/
def alternatingSixSchurConjugacyDatumRow129 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 194, orbitMiddleState := 283, orbitMiddleCentral := 1, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 345, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 194, orbitMiddleState := 283, orbitMiddleCentral := 2, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 345, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 194, orbitMiddleState := 283, orbitMiddleCentral := 3, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 345, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 194, orbitMiddleState := 283, orbitMiddleCentral := 4, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 345, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 194, orbitMiddleState := 283, orbitMiddleCentral := 5, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 345, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 194, orbitMiddleState := 283, orbitMiddleCentral := 0, conjugatorInverseState := 188, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 5, orbitPenultimateState := 345, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
