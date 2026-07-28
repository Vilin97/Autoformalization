/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 160–169

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 160. -/
def alternatingSixSchurConjugacyDatumRow160 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 8, conjugatorState := 17, orbitMiddleState := 30, orbitMiddleCentral := 2, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 75, orbitPenultimateCentral := 2 },
    { classIndex := 6, conjugatorState := 83, orbitMiddleState := 122, orbitMiddleCentral := 0, conjugatorInverseState := 104, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 158, orbitPenultimateCentral := 3 },
    { classIndex := 7, conjugatorState := 83, orbitMiddleState := 122, orbitMiddleCentral := 1, conjugatorInverseState := 104, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 158, orbitPenultimateCentral := 4 },
    { classIndex := 8, conjugatorState := 83, orbitMiddleState := 122, orbitMiddleCentral := 2, conjugatorInverseState := 104, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 158, orbitPenultimateCentral := 5 },
    { classIndex := 6, conjugatorState := 17, orbitMiddleState := 30, orbitMiddleCentral := 0, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 75, orbitPenultimateCentral := 0 },
    { classIndex := 7, conjugatorState := 17, orbitMiddleState := 30, orbitMiddleCentral := 1, conjugatorInverseState := 29, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 75, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 161. -/
def alternatingSixSchurConjugacyDatumRow161 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 166, orbitMiddleState := 306, orbitMiddleCentral := 4, conjugatorInverseState := 186, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 224, orbitPenultimateCentral := 5 },
    { classIndex := 26, conjugatorState := 166, orbitMiddleState := 306, orbitMiddleCentral := 5, conjugatorInverseState := 186, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 224, orbitPenultimateCentral := 0 },
    { classIndex := 21, conjugatorState := 166, orbitMiddleState := 306, orbitMiddleCentral := 0, conjugatorInverseState := 186, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 224, orbitPenultimateCentral := 1 },
    { classIndex := 22, conjugatorState := 166, orbitMiddleState := 306, orbitMiddleCentral := 1, conjugatorInverseState := 186, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 224, orbitPenultimateCentral := 2 },
    { classIndex := 23, conjugatorState := 166, orbitMiddleState := 306, orbitMiddleCentral := 2, conjugatorInverseState := 186, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 224, orbitPenultimateCentral := 3 },
    { classIndex := 24, conjugatorState := 166, orbitMiddleState := 306, orbitMiddleCentral := 3, conjugatorInverseState := 186, conjugatorInverseCentral := 5, inverseFactorLeftState := 23, inverseFactorLeftCentral := 0, inverseFactorRightState := 32, inverseFactorRightCentral := 5, orbitPenultimateState := 224, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 162. -/
def alternatingSixSchurConjugacyDatumRow162 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 27, conjugatorState := 30, orbitMiddleState := 87, orbitMiddleCentral := 0, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 177, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 30, orbitMiddleState := 87, orbitMiddleCentral := 1, conjugatorInverseState := 37, conjugatorInverseCentral := 3, inverseFactorLeftState := 5, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 177, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 239, orbitMiddleState := 314, orbitMiddleCentral := 3, conjugatorInverseState := 229, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 4, orbitPenultimateState := 328, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 239, orbitMiddleState := 314, orbitMiddleCentral := 4, conjugatorInverseState := 229, conjugatorInverseCentral := 4, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 34, inverseFactorRightCentral := 4, orbitPenultimateState := 328, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 64, orbitMiddleState := 339, orbitMiddleCentral := 2, conjugatorInverseState := 66, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 304, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 64, orbitMiddleState := 339, orbitMiddleCentral := 3, conjugatorInverseState := 66, conjugatorInverseCentral := 1, inverseFactorLeftState := 14, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 304, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 163. -/
def alternatingSixSchurConjugacyDatumRow163 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 18, orbitMiddleState := 190, orbitMiddleCentral := 5, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 164, orbitPenultimateCentral := 2 },
    { classIndex := 27, conjugatorState := 106, orbitMiddleState := 298, orbitMiddleCentral := 3, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 297, orbitPenultimateCentral := 4 },
    { classIndex := 28, conjugatorState := 106, orbitMiddleState := 298, orbitMiddleCentral := 4, conjugatorInverseState := 90, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 20, inverseFactorRightCentral := 3, orbitPenultimateState := 297, orbitPenultimateCentral := 5 },
    { classIndex := 27, conjugatorState := 250, orbitMiddleState := 318, orbitMiddleCentral := 4, conjugatorInverseState := 254, conjugatorInverseCentral := 2, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 43, inverseFactorRightCentral := 2, orbitPenultimateState := 187, orbitPenultimateCentral := 2 },
    { classIndex := 28, conjugatorState := 250, orbitMiddleState := 318, orbitMiddleCentral := 5, conjugatorInverseState := 254, conjugatorInverseCentral := 2, inverseFactorLeftState := 44, inverseFactorLeftCentral := 0, inverseFactorRightState := 43, inverseFactorRightCentral := 2, orbitPenultimateState := 187, orbitPenultimateCentral := 3 },
    { classIndex := 27, conjugatorState := 18, orbitMiddleState := 190, orbitMiddleCentral := 4, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 164, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 164. -/
def alternatingSixSchurConjugacyDatumRow164 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 62, orbitMiddleState := 188, orbitMiddleCentral := 4, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 138, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 62, orbitMiddleState := 188, orbitMiddleCentral := 5, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 138, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 62, orbitMiddleState := 188, orbitMiddleCentral := 0, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 138, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 62, orbitMiddleState := 188, orbitMiddleCentral := 1, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 138, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 62, orbitMiddleState := 188, orbitMiddleCentral := 2, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 138, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 62, orbitMiddleState := 188, orbitMiddleCentral := 3, conjugatorInverseState := 62, conjugatorInverseCentral := 1, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 13, inverseFactorRightCentral := 1, orbitPenultimateState := 138, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 165. -/
def alternatingSixSchurConjugacyDatumRow165 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 29, conjugatorState := 18, orbitMiddleState := 95, orbitMiddleCentral := 4, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 189, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 18, orbitMiddleState := 95, orbitMiddleCentral := 5, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 189, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 235, orbitMiddleState := 245, orbitMiddleCentral := 5, conjugatorInverseState := 230, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 235, orbitMiddleState := 245, orbitMiddleCentral := 0, conjugatorInverseState := 230, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 4, orbitPenultimateState := 99, orbitPenultimateCentral := 3 },
    { classIndex := 29, conjugatorState := 83, orbitMiddleState := 350, orbitMiddleCentral := 1, conjugatorInverseState := 104, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 286, orbitPenultimateCentral := 2 },
    { classIndex := 30, conjugatorState := 83, orbitMiddleState := 350, orbitMiddleCentral := 2, conjugatorInverseState := 104, conjugatorInverseCentral := 0, inverseFactorLeftState := 15, inverseFactorLeftCentral := 0, inverseFactorRightState := 19, inverseFactorRightCentral := 0, orbitPenultimateState := 286, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 166. -/
def alternatingSixSchurConjugacyDatumRow166 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 139, orbitMiddleState := 266, orbitMiddleCentral := 1, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 78, orbitPenultimateCentral := 5 },
    { classIndex := 21, conjugatorState := 139, orbitMiddleState := 266, orbitMiddleCentral := 2, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 78, orbitPenultimateCentral := 0 },
    { classIndex := 22, conjugatorState := 139, orbitMiddleState := 266, orbitMiddleCentral := 3, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 78, orbitPenultimateCentral := 1 },
    { classIndex := 23, conjugatorState := 139, orbitMiddleState := 266, orbitMiddleCentral := 4, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 78, orbitPenultimateCentral := 2 },
    { classIndex := 24, conjugatorState := 139, orbitMiddleState := 266, orbitMiddleCentral := 5, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 78, orbitPenultimateCentral := 3 },
    { classIndex := 25, conjugatorState := 139, orbitMiddleState := 266, orbitMiddleCentral := 0, conjugatorInverseState := 153, conjugatorInverseCentral := 0, inverseFactorLeftState := 28, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 0, orbitPenultimateState := 78, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 167. -/
def alternatingSixSchurConjugacyDatumRow167 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 12, conjugatorState := 19, orbitMiddleState := 33, orbitMiddleCentral := 3, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 80, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 19, orbitMiddleState := 33, orbitMiddleCentral := 4, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 80, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 19, orbitMiddleState := 33, orbitMiddleCentral := 5, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 80, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 19, orbitMiddleState := 33, orbitMiddleCentral := 0, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 80, orbitPenultimateCentral := 2 },
    { classIndex := 10, conjugatorState := 19, orbitMiddleState := 33, orbitMiddleCentral := 1, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 80, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 19, orbitMiddleState := 33, orbitMiddleCentral := 2, conjugatorInverseState := 19, conjugatorInverseCentral := 1, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 6, inverseFactorRightCentral := 1, orbitPenultimateState := 80, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 168. -/
def alternatingSixSchurConjugacyDatumRow168 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 25, conjugatorState := 88, orbitMiddleState := 236, orbitMiddleCentral := 4, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 180, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 88, orbitMiddleState := 236, orbitMiddleCentral := 5, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 180, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 88, orbitMiddleState := 236, orbitMiddleCentral := 0, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 180, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 88, orbitMiddleState := 236, orbitMiddleCentral := 1, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 180, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 88, orbitMiddleState := 236, orbitMiddleCentral := 2, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 180, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 88, orbitMiddleState := 236, orbitMiddleCentral := 3, conjugatorInverseState := 92, conjugatorInverseCentral := 0, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 22, inverseFactorRightCentral := 0, orbitPenultimateState := 180, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 169. -/
def alternatingSixSchurConjugacyDatumRow169 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 37, orbitMiddleState := 54, orbitMiddleCentral := 0, conjugatorInverseState := 30, conjugatorInverseCentral := 3, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 101, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 137, orbitMiddleState := 166, orbitMiddleCentral := 2, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 167, orbitPenultimateCentral := 3 },
    { classIndex := 30, conjugatorState := 137, orbitMiddleState := 166, orbitMiddleCentral := 3, conjugatorInverseState := 131, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 18, inverseFactorRightCentral := 2, orbitPenultimateState := 167, orbitPenultimateCentral := 4 },
    { classIndex := 29, conjugatorState := 158, orbitMiddleState := 293, orbitMiddleCentral := 2, conjugatorInverseState := 176, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 1, orbitPenultimateState := 339, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 158, orbitMiddleState := 293, orbitMiddleCentral := 3, conjugatorInverseState := 176, conjugatorInverseCentral := 1, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 37, inverseFactorRightCentral := 1, orbitPenultimateState := 339, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 37, orbitMiddleState := 54, orbitMiddleCentral := 5, conjugatorInverseState := 30, conjugatorInverseCentral := 3, inverseFactorLeftState := 4, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 101, orbitPenultimateCentral := 4 }
  ]


end GroupTheory
end McKayConjecture
