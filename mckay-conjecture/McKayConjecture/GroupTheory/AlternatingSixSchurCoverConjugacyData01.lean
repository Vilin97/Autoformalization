/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 10–19

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 10. -/
def alternatingSixSchurConjugacyDatumRow010 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 0, orbitMiddleState := 10, orbitMiddleCentral := 0, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 10, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 0, orbitMiddleState := 10, orbitMiddleCentral := 1, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 10, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 0, orbitMiddleState := 10, orbitMiddleCentral := 2, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 10, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 0, orbitMiddleState := 10, orbitMiddleCentral := 3, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 10, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 0, orbitMiddleState := 10, orbitMiddleCentral := 4, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 10, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 0, orbitMiddleState := 10, orbitMiddleCentral := 5, conjugatorInverseState := 0, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 0, inverseFactorRightCentral := 0, orbitPenultimateState := 10, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 11. -/
def alternatingSixSchurConjugacyDatumRow011 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 322, orbitMiddleState := 349, orbitMiddleCentral := 1, conjugatorInverseState := 306, conjugatorInverseCentral := 0, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 64, inverseFactorRightCentral := 0, orbitPenultimateState := 177, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 322, orbitMiddleState := 349, orbitMiddleCentral := 2, conjugatorInverseState := 306, conjugatorInverseCentral := 0, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 64, inverseFactorRightCentral := 0, orbitPenultimateState := 177, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 322, orbitMiddleState := 349, orbitMiddleCentral := 3, conjugatorInverseState := 306, conjugatorInverseCentral := 0, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 64, inverseFactorRightCentral := 0, orbitPenultimateState := 177, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 322, orbitMiddleState := 349, orbitMiddleCentral := 4, conjugatorInverseState := 306, conjugatorInverseCentral := 0, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 64, inverseFactorRightCentral := 0, orbitPenultimateState := 177, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 322, orbitMiddleState := 349, orbitMiddleCentral := 5, conjugatorInverseState := 306, conjugatorInverseCentral := 0, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 64, inverseFactorRightCentral := 0, orbitPenultimateState := 177, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 322, orbitMiddleState := 349, orbitMiddleCentral := 0, conjugatorInverseState := 306, conjugatorInverseCentral := 0, inverseFactorLeftState := 51, inverseFactorLeftCentral := 0, inverseFactorRightState := 64, inverseFactorRightCentral := 0, orbitPenultimateState := 177, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 12. -/
def alternatingSixSchurConjugacyDatumRow012 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 2, orbitMiddleState := 23, orbitMiddleCentral := 0, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 23, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 2, orbitMiddleState := 23, orbitMiddleCentral := 1, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 23, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 2, orbitMiddleState := 23, orbitMiddleCentral := 2, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 23, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 2, orbitMiddleState := 23, orbitMiddleCentral := 3, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 23, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 2, orbitMiddleState := 23, orbitMiddleCentral := 4, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 23, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 2, orbitMiddleState := 23, orbitMiddleCentral := 5, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 23, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 13. -/
def alternatingSixSchurConjugacyDatumRow013 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 2, orbitMiddleState := 6, orbitMiddleCentral := 0, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 6, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 2, orbitMiddleState := 6, orbitMiddleCentral := 1, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 6, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 2, orbitMiddleState := 6, orbitMiddleCentral := 2, conjugatorInverseState := 3, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 3, inverseFactorRightCentral := 0, orbitPenultimateState := 6, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 51, orbitMiddleState := 78, orbitMiddleCentral := 0, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 63, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 51, orbitMiddleState := 78, orbitMiddleCentral := 1, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 63, orbitPenultimateCentral := 5 },
    { classIndex := 8, conjugatorState := 51, orbitMiddleState := 78, orbitMiddleCentral := 2, conjugatorInverseState := 71, conjugatorInverseCentral := 3, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 63, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 14. -/
def alternatingSixSchurConjugacyDatumRow014 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 1, orbitMiddleState := 7, orbitMiddleCentral := 1, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 7, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 1, orbitMiddleState := 7, orbitMiddleCentral := 2, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 7, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 1, orbitMiddleState := 7, orbitMiddleCentral := 3, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 7, orbitPenultimateCentral := 3 },
    { classIndex := 24, conjugatorState := 1, orbitMiddleState := 7, orbitMiddleCentral := 4, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 7, orbitPenultimateCentral := 4 },
    { classIndex := 25, conjugatorState := 1, orbitMiddleState := 7, orbitMiddleCentral := 5, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 7, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 1, orbitMiddleState := 7, orbitMiddleCentral := 0, conjugatorInverseState := 1, conjugatorInverseCentral := 5, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 7, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 15. -/
def alternatingSixSchurConjugacyDatumRow015 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 6, conjugatorState := 3, orbitMiddleState := 8, orbitMiddleCentral := 0, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 8, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 3, orbitMiddleState := 8, orbitMiddleCentral := 1, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 8, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 3, orbitMiddleState := 8, orbitMiddleCentral := 2, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 8, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 57, orbitMiddleState := 86, orbitMiddleCentral := 0, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 71, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 57, orbitMiddleState := 86, orbitMiddleCentral := 1, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 71, orbitPenultimateCentral := 5 },
    { classIndex := 8, conjugatorState := 57, orbitMiddleState := 86, orbitMiddleCentral := 2, conjugatorInverseState := 63, conjugatorInverseCentral := 3, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 71, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 16. -/
def alternatingSixSchurConjugacyDatumRow016 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 3, orbitMiddleState := 28, orbitMiddleCentral := 3, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 28, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 3, orbitMiddleState := 28, orbitMiddleCentral := 4, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 28, orbitPenultimateCentral := 4 },
    { classIndex := 26, conjugatorState := 3, orbitMiddleState := 28, orbitMiddleCentral := 5, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 28, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 3, orbitMiddleState := 28, orbitMiddleCentral := 0, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 28, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 3, orbitMiddleState := 28, orbitMiddleCentral := 1, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 28, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 3, orbitMiddleState := 28, orbitMiddleCentral := 2, conjugatorInverseState := 2, conjugatorInverseCentral := 0, inverseFactorLeftState := 0, inverseFactorLeftCentral := 0, inverseFactorRightState := 2, inverseFactorRightCentral := 0, orbitPenultimateState := 28, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 17. -/
def alternatingSixSchurConjugacyDatumRow017 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 284, orbitMiddleState := 311, orbitMiddleCentral := 1, conjugatorInverseState := 297, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 218, orbitPenultimateCentral := 5 },
    { classIndex := 25, conjugatorState := 284, orbitMiddleState := 311, orbitMiddleCentral := 2, conjugatorInverseState := 297, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 218, orbitPenultimateCentral := 0 },
    { classIndex := 26, conjugatorState := 284, orbitMiddleState := 311, orbitMiddleCentral := 3, conjugatorInverseState := 297, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 218, orbitPenultimateCentral := 1 },
    { classIndex := 21, conjugatorState := 284, orbitMiddleState := 311, orbitMiddleCentral := 4, conjugatorInverseState := 297, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 218, orbitPenultimateCentral := 2 },
    { classIndex := 22, conjugatorState := 284, orbitMiddleState := 311, orbitMiddleCentral := 5, conjugatorInverseState := 297, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 218, orbitPenultimateCentral := 3 },
    { classIndex := 23, conjugatorState := 284, orbitMiddleState := 311, orbitMiddleCentral := 0, conjugatorInverseState := 297, conjugatorInverseCentral := 4, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 57, inverseFactorRightCentral := 4, orbitPenultimateState := 218, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 18. -/
def alternatingSixSchurConjugacyDatumRow018 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 230, orbitMiddleState := 274, orbitMiddleCentral := 0, conjugatorInverseState := 235, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 167, orbitPenultimateCentral := 5 },
    { classIndex := 11, conjugatorState := 230, orbitMiddleState := 274, orbitMiddleCentral := 1, conjugatorInverseState := 235, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 167, orbitPenultimateCentral := 0 },
    { classIndex := 12, conjugatorState := 230, orbitMiddleState := 274, orbitMiddleCentral := 2, conjugatorInverseState := 235, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 167, orbitPenultimateCentral := 1 },
    { classIndex := 13, conjugatorState := 230, orbitMiddleState := 274, orbitMiddleCentral := 3, conjugatorInverseState := 235, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 167, orbitPenultimateCentral := 2 },
    { classIndex := 14, conjugatorState := 230, orbitMiddleState := 274, orbitMiddleCentral := 4, conjugatorInverseState := 235, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 167, orbitPenultimateCentral := 3 },
    { classIndex := 9, conjugatorState := 230, orbitMiddleState := 274, orbitMiddleCentral := 5, conjugatorInverseState := 235, conjugatorInverseCentral := 4, inverseFactorLeftState := 36, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 4, orbitPenultimateState := 167, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 19. -/
def alternatingSixSchurConjugacyDatumRow019 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 139, orbitMiddleState := 190, orbitMiddleCentral := 2, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 121, orbitPenultimateCentral := 4 },
    { classIndex := 6, conjugatorState := 43, orbitMiddleState := 67, orbitMiddleCentral := 0, conjugatorInverseState := 43, conjugatorInverseCentral := 5, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 5, orbitPenultimateState := 82, orbitPenultimateCentral := 4 },
    { classIndex := 7, conjugatorState := 43, orbitMiddleState := 67, orbitMiddleCentral := 1, conjugatorInverseState := 43, conjugatorInverseCentral := 5, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 5, orbitPenultimateState := 82, orbitPenultimateCentral := 5 },
    { classIndex := 8, conjugatorState := 43, orbitMiddleState := 67, orbitMiddleCentral := 2, conjugatorInverseState := 43, conjugatorInverseCentral := 5, inverseFactorLeftState := 7, inverseFactorLeftCentral := 0, inverseFactorRightState := 10, inverseFactorRightCentral := 5, orbitPenultimateState := 82, orbitPenultimateCentral := 0 },
    { classIndex := 6, conjugatorState := 139, orbitMiddleState := 190, orbitMiddleCentral := 0, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 121, orbitPenultimateCentral := 2 },
    { classIndex := 7, conjugatorState := 139, orbitMiddleState := 190, orbitMiddleCentral := 1, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 121, orbitPenultimateCentral := 3 }
  ]


end GroupTheory
end McKayConjecture
