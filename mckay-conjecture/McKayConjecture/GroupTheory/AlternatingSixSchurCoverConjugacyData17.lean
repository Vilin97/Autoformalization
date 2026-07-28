/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 170–179

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 170. -/
def alternatingSixSchurConjugacyDatumRow170 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 9, orbitMiddleState := 100, orbitMiddleCentral := 3, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 144, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 9, orbitMiddleState := 100, orbitMiddleCentral := 4, conjugatorInverseState := 11, conjugatorInverseCentral := 4, inverseFactorLeftState := 1, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 144, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 180, orbitMiddleState := 327, orbitMiddleCentral := 0, conjugatorInverseState := 200, conjugatorInverseCentral := 5, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 5, orbitPenultimateState := 343, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 180, orbitMiddleState := 327, orbitMiddleCentral := 1, conjugatorInverseState := 200, conjugatorInverseCentral := 5, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 41, inverseFactorRightCentral := 5, orbitPenultimateState := 343, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 136, orbitMiddleState := 151, orbitMiddleCentral := 5, conjugatorInverseState := 150, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 232, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 136, orbitMiddleState := 151, orbitMiddleCentral := 0, conjugatorInverseState := 150, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 26, inverseFactorRightCentral := 0, orbitPenultimateState := 232, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 171. -/
def alternatingSixSchurConjugacyDatumRow171 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 76, orbitMiddleState := 216, orbitMiddleCentral := 1, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 75, orbitPenultimateCentral := 2 },
    { classIndex := 21, conjugatorState := 76, orbitMiddleState := 216, orbitMiddleCentral := 2, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 75, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 76, orbitMiddleState := 216, orbitMiddleCentral := 3, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 75, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 76, orbitMiddleState := 216, orbitMiddleCentral := 4, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 75, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 76, orbitMiddleState := 216, orbitMiddleCentral := 5, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 75, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 76, orbitMiddleState := 216, orbitMiddleCentral := 0, conjugatorInverseState := 109, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 0, orbitPenultimateState := 75, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 172. -/
def alternatingSixSchurConjugacyDatumRow172 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 186, orbitMiddleState := 240, orbitMiddleCentral := 5, conjugatorInverseState := 166, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 186, orbitMiddleState := 240, orbitMiddleCentral := 0, conjugatorInverseState := 166, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 186, orbitMiddleState := 240, orbitMiddleCentral := 1, conjugatorInverseState := 166, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 186, orbitMiddleState := 240, orbitMiddleCentral := 2, conjugatorInverseState := 166, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 186, orbitMiddleState := 240, orbitMiddleCentral := 3, conjugatorInverseState := 166, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 186, orbitMiddleState := 240, orbitMiddleCentral := 4, conjugatorInverseState := 166, conjugatorInverseCentral := 5, inverseFactorLeftState := 18, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 354, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 173. -/
def alternatingSixSchurConjugacyDatumRow173 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 150, orbitMiddleState := 276, orbitMiddleCentral := 4, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 150, orbitMiddleState := 276, orbitMiddleCentral := 5, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 150, orbitMiddleState := 276, orbitMiddleCentral := 0, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 150, orbitMiddleState := 276, orbitMiddleCentral := 1, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 150, orbitMiddleState := 276, orbitMiddleCentral := 2, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 150, orbitMiddleState := 276, orbitMiddleCentral := 3, conjugatorInverseState := 136, conjugatorInverseCentral := 0, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 0, orbitPenultimateState := 86, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 174. -/
def alternatingSixSchurConjugacyDatumRow174 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 12, orbitMiddleState := 57, orbitMiddleCentral := 4, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 85, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 119, orbitMiddleState := 169, orbitMiddleCentral := 5, conjugatorInverseState := 121, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 146, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 119, orbitMiddleState := 169, orbitMiddleCentral := 0, conjugatorInverseState := 121, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 24, inverseFactorRightCentral := 5, orbitPenultimateState := 146, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 216, orbitMiddleState := 254, orbitMiddleCentral := 5, conjugatorInverseState := 255, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 102, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 216, orbitMiddleState := 254, orbitMiddleCentral := 0, conjugatorInverseState := 255, conjugatorInverseCentral := 4, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 44, inverseFactorRightCentral := 4, orbitPenultimateState := 102, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 12, orbitMiddleState := 57, orbitMiddleCentral := 3, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 85, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 175. -/
def alternatingSixSchurConjugacyDatumRow175 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 72, orbitMiddleState := 208, orbitMiddleCentral := 1, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 71, orbitPenultimateCentral := 2 },
    { classIndex := 21, conjugatorState := 72, orbitMiddleState := 208, orbitMiddleCentral := 2, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 71, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 72, orbitMiddleState := 208, orbitMiddleCentral := 3, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 71, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 72, orbitMiddleState := 208, orbitMiddleCentral := 4, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 71, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 72, orbitMiddleState := 208, orbitMiddleCentral := 5, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 71, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 72, orbitMiddleState := 208, orbitMiddleCentral := 0, conjugatorInverseState := 72, conjugatorInverseCentral := 1, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 12, inverseFactorRightCentral := 1, orbitPenultimateState := 71, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 176. -/
def alternatingSixSchurConjugacyDatumRow176 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 40, orbitMiddleState := 318, orbitMiddleCentral := 3, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 312, orbitPenultimateCentral := 1 },
    { classIndex := 30, conjugatorState := 40, orbitMiddleState := 318, orbitMiddleCentral := 4, conjugatorInverseState := 46, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 4, orbitPenultimateState := 312, orbitPenultimateCentral := 2 },
    { classIndex := 29, conjugatorState := 5, orbitMiddleState := 175, orbitMiddleCentral := 0, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 126, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 5, orbitMiddleState := 175, orbitMiddleCentral := 1, conjugatorInverseState := 6, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 1, inverseFactorRightCentral := 5, orbitPenultimateState := 126, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 169, orbitMiddleState := 330, orbitMiddleCentral := 3, conjugatorInverseState := 184, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 151, orbitPenultimateCentral := 5 },
    { classIndex := 30, conjugatorState := 169, orbitMiddleState := 330, orbitMiddleCentral := 4, conjugatorInverseState := 184, conjugatorInverseCentral := 5, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 47, inverseFactorRightCentral := 5, orbitPenultimateState := 151, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 177. -/
def alternatingSixSchurConjugacyDatumRow177 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 12, orbitMiddleState := 128, orbitMiddleCentral := 1, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 87, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 69, orbitMiddleState := 276, orbitMiddleCentral := 1, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 311, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 69, orbitMiddleState := 276, orbitMiddleCentral := 2, conjugatorInverseState := 59, conjugatorInverseCentral := 3, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 3, orbitPenultimateState := 311, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 240, orbitMiddleState := 272, orbitMiddleCentral := 1, conjugatorInverseState := 258, conjugatorInverseCentral := 5, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 129, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 240, orbitMiddleState := 272, orbitMiddleCentral := 2, conjugatorInverseState := 258, conjugatorInverseCentral := 5, inverseFactorLeftState := 46, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 5, orbitPenultimateState := 129, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 12, orbitMiddleState := 128, orbitMiddleCentral := 0, conjugatorInverseState := 16, conjugatorInverseCentral := 5, inverseFactorLeftState := 3, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 87, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 178. -/
def alternatingSixSchurConjugacyDatumRow178 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 173, orbitMiddleState := 309, orbitMiddleCentral := 4, conjugatorInverseState := 210, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 228, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 173, orbitMiddleState := 309, orbitMiddleCentral := 5, conjugatorInverseState := 210, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 228, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 173, orbitMiddleState := 309, orbitMiddleCentral := 0, conjugatorInverseState := 210, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 228, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 173, orbitMiddleState := 309, orbitMiddleCentral := 1, conjugatorInverseState := 210, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 228, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 173, orbitMiddleState := 309, orbitMiddleCentral := 2, conjugatorInverseState := 210, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 228, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 173, orbitMiddleState := 309, orbitMiddleCentral := 3, conjugatorInverseState := 210, conjugatorInverseCentral := 5, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 35, inverseFactorRightCentral := 5, orbitPenultimateState := 228, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 179. -/
def alternatingSixSchurConjugacyDatumRow179 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 21, orbitMiddleState := 37, orbitMiddleCentral := 2, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 89, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 81, orbitMiddleState := 121, orbitMiddleCentral := 0, conjugatorInverseState := 97, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 181, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 81, orbitMiddleState := 121, orbitMiddleCentral := 1, conjugatorInverseState := 97, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 181, orbitPenultimateCentral := 1 },
    { classIndex := 8, conjugatorState := 81, orbitMiddleState := 121, orbitMiddleCentral := 2, conjugatorInverseState := 97, conjugatorInverseCentral := 0, inverseFactorLeftState := 13, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 181, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 21, orbitMiddleState := 37, orbitMiddleCentral := 0, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 89, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 21, orbitMiddleState := 37, orbitMiddleCentral := 1, conjugatorInverseState := 22, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 4, orbitPenultimateState := 89, orbitPenultimateCentral := 1 }
  ]


end GroupTheory
end McKayConjecture
