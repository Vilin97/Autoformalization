/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 20–29

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 20. -/
def alternatingSixSchurConjugacyDatumRow020 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 192, orbitMiddleState := 244, orbitMiddleCentral := 1, conjugatorInverseState := 161, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 179, orbitPenultimateCentral := 5 },
    { classIndex := 11, conjugatorState := 192, orbitMiddleState := 244, orbitMiddleCentral := 2, conjugatorInverseState := 161, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 179, orbitPenultimateCentral := 0 },
    { classIndex := 12, conjugatorState := 192, orbitMiddleState := 244, orbitMiddleCentral := 3, conjugatorInverseState := 161, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 179, orbitPenultimateCentral := 1 },
    { classIndex := 13, conjugatorState := 192, orbitMiddleState := 244, orbitMiddleCentral := 4, conjugatorInverseState := 161, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 179, orbitPenultimateCentral := 2 },
    { classIndex := 14, conjugatorState := 192, orbitMiddleState := 244, orbitMiddleCentral := 5, conjugatorInverseState := 161, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 179, orbitPenultimateCentral := 3 },
    { classIndex := 9, conjugatorState := 192, orbitMiddleState := 244, orbitMiddleCentral := 0, conjugatorInverseState := 161, conjugatorInverseCentral := 5, inverseFactorLeftState := 17, inverseFactorLeftCentral := 0, inverseFactorRightState := 38, inverseFactorRightCentral := 5, orbitPenultimateState := 179, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 21. -/
def alternatingSixSchurConjugacyDatumRow021 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 297, orbitMiddleState := 304, orbitMiddleCentral := 0, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 77, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 297, orbitMiddleState := 304, orbitMiddleCentral := 1, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 77, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 297, orbitMiddleState := 304, orbitMiddleCentral := 2, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 77, orbitPenultimateCentral := 1 },
    { classIndex := 25, conjugatorState := 297, orbitMiddleState := 304, orbitMiddleCentral := 3, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 77, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 297, orbitMiddleState := 304, orbitMiddleCentral := 4, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 77, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 297, orbitMiddleState := 304, orbitMiddleCentral := 5, conjugatorInverseState := 284, conjugatorInverseCentral := 4, inverseFactorLeftState := 39, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 77, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 22. -/
def alternatingSixSchurConjugacyDatumRow022 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 296, orbitMiddleState := 329, orbitMiddleCentral := 3, conjugatorInverseState := 298, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 174, orbitPenultimateCentral := 1 },
    { classIndex := 25, conjugatorState := 296, orbitMiddleState := 329, orbitMiddleCentral := 4, conjugatorInverseState := 298, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 174, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 296, orbitMiddleState := 329, orbitMiddleCentral := 5, conjugatorInverseState := 298, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 174, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 296, orbitMiddleState := 329, orbitMiddleCentral := 0, conjugatorInverseState := 298, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 174, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 296, orbitMiddleState := 329, orbitMiddleCentral := 1, conjugatorInverseState := 298, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 174, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 296, orbitMiddleState := 329, orbitMiddleCentral := 2, conjugatorInverseState := 298, conjugatorInverseCentral := 4, inverseFactorLeftState := 47, inverseFactorLeftCentral := 0, inverseFactorRightState := 72, inverseFactorRightCentral := 4, orbitPenultimateState := 174, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 23. -/
def alternatingSixSchurConjugacyDatumRow023 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 126, orbitMiddleState := 233, orbitMiddleCentral := 2, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 136, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 126, orbitMiddleState := 233, orbitMiddleCentral := 3, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 136, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 126, orbitMiddleState := 233, orbitMiddleCentral := 4, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 136, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 126, orbitMiddleState := 233, orbitMiddleCentral := 5, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 136, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 126, orbitMiddleState := 233, orbitMiddleCentral := 0, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 136, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 126, orbitMiddleState := 233, orbitMiddleCentral := 1, conjugatorInverseState := 132, conjugatorInverseCentral := 2, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 27, inverseFactorRightCentral := 2, orbitPenultimateState := 136, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 24. -/
def alternatingSixSchurConjugacyDatumRow024 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 204, orbitMiddleState := 255, orbitMiddleCentral := 0, conjugatorInverseState := 178, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 194, orbitPenultimateCentral := 5 },
    { classIndex := 11, conjugatorState := 204, orbitMiddleState := 255, orbitMiddleCentral := 1, conjugatorInverseState := 178, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 194, orbitPenultimateCentral := 0 },
    { classIndex := 12, conjugatorState := 204, orbitMiddleState := 255, orbitMiddleCentral := 2, conjugatorInverseState := 178, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 194, orbitPenultimateCentral := 1 },
    { classIndex := 13, conjugatorState := 204, orbitMiddleState := 255, orbitMiddleCentral := 3, conjugatorInverseState := 178, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 194, orbitPenultimateCentral := 2 },
    { classIndex := 14, conjugatorState := 204, orbitMiddleState := 255, orbitMiddleCentral := 4, conjugatorInverseState := 178, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 194, orbitPenultimateCentral := 3 },
    { classIndex := 9, conjugatorState := 204, orbitMiddleState := 255, orbitMiddleCentral := 5, conjugatorInverseState := 178, conjugatorInverseCentral := 5, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 194, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 25. -/
def alternatingSixSchurConjugacyDatumRow025 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 163, orbitMiddleState := 164, orbitMiddleCentral := 3, conjugatorInverseState := 181, conjugatorInverseCentral := 1, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 1, orbitPenultimateState := 97, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 163, orbitMiddleState := 164, orbitMiddleCentral := 4, conjugatorInverseState := 181, conjugatorInverseCentral := 1, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 1, orbitPenultimateState := 97, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 163, orbitMiddleState := 164, orbitMiddleCentral := 5, conjugatorInverseState := 181, conjugatorInverseCentral := 1, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 1, orbitPenultimateState := 97, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 163, orbitMiddleState := 164, orbitMiddleCentral := 0, conjugatorInverseState := 181, conjugatorInverseCentral := 1, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 1, orbitPenultimateState := 97, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 163, orbitMiddleState := 164, orbitMiddleCentral := 1, conjugatorInverseState := 181, conjugatorInverseCentral := 1, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 1, orbitPenultimateState := 97, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 163, orbitMiddleState := 164, orbitMiddleCentral := 2, conjugatorInverseState := 181, conjugatorInverseCentral := 1, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 1, orbitPenultimateState := 97, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 26. -/
def alternatingSixSchurConjugacyDatumRow026 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 15, conjugatorState := 6, orbitMiddleState := 7, orbitMiddleCentral := 1, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 14, orbitPenultimateCentral := 1 },
    { classIndex := 16, conjugatorState := 6, orbitMiddleState := 7, orbitMiddleCentral := 2, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 14, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 6, orbitMiddleState := 7, orbitMiddleCentral := 3, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 14, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 6, orbitMiddleState := 7, orbitMiddleCentral := 4, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 14, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 6, orbitMiddleState := 7, orbitMiddleCentral := 5, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 14, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 6, orbitMiddleState := 7, orbitMiddleCentral := 0, conjugatorInverseState := 5, conjugatorInverseCentral := 5, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 5, orbitPenultimateState := 14, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 27. -/
def alternatingSixSchurConjugacyDatumRow027 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 222, orbitMiddleState := 267, orbitMiddleCentral := 1, conjugatorInverseState := 217, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 4, orbitPenultimateState := 109, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 222, orbitMiddleState := 267, orbitMiddleCentral := 2, conjugatorInverseState := 217, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 4, orbitPenultimateState := 109, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 222, orbitMiddleState := 267, orbitMiddleCentral := 3, conjugatorInverseState := 217, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 4, orbitPenultimateState := 109, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 222, orbitMiddleState := 267, orbitMiddleCentral := 4, conjugatorInverseState := 217, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 4, orbitPenultimateState := 109, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 222, orbitMiddleState := 267, orbitMiddleCentral := 5, conjugatorInverseState := 217, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 4, orbitPenultimateState := 109, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 222, orbitMiddleState := 267, orbitMiddleCentral := 0, conjugatorInverseState := 217, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 4, orbitPenultimateState := 109, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 28. -/
def alternatingSixSchurConjugacyDatumRow028 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 15, conjugatorState := 3, orbitMiddleState := 15, orbitMiddleCentral := 0, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 15, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 3, orbitMiddleState := 15, orbitMiddleCentral := 1, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 15, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 3, orbitMiddleState := 15, orbitMiddleCentral := 2, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 15, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 3, orbitMiddleState := 15, orbitMiddleCentral := 3, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 15, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 3, orbitMiddleState := 15, orbitMiddleCentral := 4, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 15, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 3, orbitMiddleState := 15, orbitMiddleCentral := 5, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 15, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 29. -/
def alternatingSixSchurConjugacyDatumRow029 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 285, orbitMiddleState := 320, orbitMiddleCentral := 5, conjugatorInverseState := 282, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 142, orbitPenultimateCentral := 0 },
    { classIndex := 23, conjugatorState := 285, orbitMiddleState := 320, orbitMiddleCentral := 0, conjugatorInverseState := 282, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 142, orbitPenultimateCentral := 1 },
    { classIndex := 24, conjugatorState := 285, orbitMiddleState := 320, orbitMiddleCentral := 1, conjugatorInverseState := 282, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 142, orbitPenultimateCentral := 2 },
    { classIndex := 25, conjugatorState := 285, orbitMiddleState := 320, orbitMiddleCentral := 2, conjugatorInverseState := 282, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 142, orbitPenultimateCentral := 3 },
    { classIndex := 26, conjugatorState := 285, orbitMiddleState := 320, orbitMiddleCentral := 3, conjugatorInverseState := 282, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 142, orbitPenultimateCentral := 4 },
    { classIndex := 21, conjugatorState := 285, orbitMiddleState := 320, orbitMiddleCentral := 4, conjugatorInverseState := 282, conjugatorInverseCentral := 4, inverseFactorLeftState := 38, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 142, orbitPenultimateCentral := 5 }
  ]


end GroupTheory
end McKayConjecture
