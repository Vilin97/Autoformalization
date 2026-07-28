/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 220–229

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 220. -/
def alternatingSixSchurConjugacyDatumRow220 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 253, orbitMiddleState := 280, orbitMiddleCentral := 2, conjugatorInverseState := 233, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 0 },
    { classIndex := 10, conjugatorState := 253, orbitMiddleState := 280, orbitMiddleCentral := 3, conjugatorInverseState := 233, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 253, orbitMiddleState := 280, orbitMiddleCentral := 4, conjugatorInverseState := 233, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 253, orbitMiddleState := 280, orbitMiddleCentral := 5, conjugatorInverseState := 233, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 253, orbitMiddleState := 280, orbitMiddleCentral := 0, conjugatorInverseState := 233, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 253, orbitMiddleState := 280, orbitMiddleCentral := 1, conjugatorInverseState := 233, conjugatorInverseCentral := 4, inverseFactorLeftState := 35, inverseFactorLeftCentral := 0, inverseFactorRightState := 48, inverseFactorRightCentral := 4, orbitPenultimateState := 131, orbitPenultimateCentral := 5 }
  ]

/-- Certificate data above normal-word state 221. -/
def alternatingSixSchurConjugacyDatumRow221 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 22, conjugatorState := 112, orbitMiddleState := 262, orbitMiddleCentral := 1, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 111, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 112, orbitMiddleState := 262, orbitMiddleCentral := 2, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 111, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 112, orbitMiddleState := 262, orbitMiddleCentral := 3, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 111, orbitPenultimateCentral := 1 },
    { classIndex := 25, conjugatorState := 112, orbitMiddleState := 262, orbitMiddleCentral := 4, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 111, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 112, orbitMiddleState := 262, orbitMiddleCentral := 5, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 111, orbitPenultimateCentral := 3 },
    { classIndex := 21, conjugatorState := 112, orbitMiddleState := 262, orbitMiddleCentral := 0, conjugatorInverseState := 152, conjugatorInverseCentral := 2, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 29, inverseFactorRightCentral := 2, orbitPenultimateState := 111, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 222. -/
def alternatingSixSchurConjugacyDatumRow222 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 17, conjugatorState := 18, orbitMiddleState := 51, orbitMiddleCentral := 2, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 119, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 18, orbitMiddleState := 51, orbitMiddleCentral := 3, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 119, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 18, orbitMiddleState := 51, orbitMiddleCentral := 4, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 119, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 18, orbitMiddleState := 51, orbitMiddleCentral := 5, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 119, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 18, orbitMiddleState := 51, orbitMiddleCentral := 0, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 119, orbitPenultimateCentral := 0 },
    { classIndex := 16, conjugatorState := 18, orbitMiddleState := 51, orbitMiddleCentral := 1, conjugatorInverseState := 24, conjugatorInverseCentral := 4, inverseFactorLeftState := 6, inverseFactorLeftCentral := 0, inverseFactorRightState := 8, inverseFactorRightCentral := 4, orbitPenultimateState := 119, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 223. -/
def alternatingSixSchurConjugacyDatumRow223 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 132, orbitMiddleState := 133, orbitMiddleCentral := 2, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 274, orbitPenultimateCentral := 2 },
    { classIndex := 17, conjugatorState := 132, orbitMiddleState := 133, orbitMiddleCentral := 3, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 274, orbitPenultimateCentral := 3 },
    { classIndex := 18, conjugatorState := 132, orbitMiddleState := 133, orbitMiddleCentral := 4, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 274, orbitPenultimateCentral := 4 },
    { classIndex := 19, conjugatorState := 132, orbitMiddleState := 133, orbitMiddleCentral := 5, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 274, orbitPenultimateCentral := 5 },
    { classIndex := 20, conjugatorState := 132, orbitMiddleState := 133, orbitMiddleCentral := 0, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 274, orbitPenultimateCentral := 0 },
    { classIndex := 15, conjugatorState := 132, orbitMiddleState := 133, orbitMiddleCentral := 1, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 274, orbitPenultimateCentral := 1 }
  ]

/-- Certificate data above normal-word state 224. -/
def alternatingSixSchurConjugacyDatumRow224 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 207, orbitMiddleState := 231, orbitMiddleCentral := 2, conjugatorInverseState := 168, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 230, orbitPenultimateCentral := 3 },
    { classIndex := 10, conjugatorState := 207, orbitMiddleState := 231, orbitMiddleCentral := 3, conjugatorInverseState := 168, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 230, orbitPenultimateCentral := 4 },
    { classIndex := 11, conjugatorState := 207, orbitMiddleState := 231, orbitMiddleCentral := 4, conjugatorInverseState := 168, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 230, orbitPenultimateCentral := 5 },
    { classIndex := 12, conjugatorState := 207, orbitMiddleState := 231, orbitMiddleCentral := 5, conjugatorInverseState := 168, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 230, orbitPenultimateCentral := 0 },
    { classIndex := 13, conjugatorState := 207, orbitMiddleState := 231, orbitMiddleCentral := 0, conjugatorInverseState := 168, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 230, orbitPenultimateCentral := 1 },
    { classIndex := 14, conjugatorState := 207, orbitMiddleState := 231, orbitMiddleCentral := 1, conjugatorInverseState := 168, conjugatorInverseCentral := 5, inverseFactorLeftState := 19, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 230, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 225. -/
def alternatingSixSchurConjugacyDatumRow225 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 9, conjugatorState := 247, orbitMiddleState := 283, orbitMiddleCentral := 0, conjugatorInverseState := 219, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 4, orbitPenultimateState := 280, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 247, orbitMiddleState := 283, orbitMiddleCentral := 1, conjugatorInverseState := 219, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 4, orbitPenultimateState := 280, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 247, orbitMiddleState := 283, orbitMiddleCentral := 2, conjugatorInverseState := 219, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 4, orbitPenultimateState := 280, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 247, orbitMiddleState := 283, orbitMiddleCentral := 3, conjugatorInverseState := 219, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 4, orbitPenultimateState := 280, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 247, orbitMiddleState := 283, orbitMiddleCentral := 4, conjugatorInverseState := 219, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 4, orbitPenultimateState := 280, orbitPenultimateCentral := 3 },
    { classIndex := 14, conjugatorState := 247, orbitMiddleState := 283, orbitMiddleCentral := 5, conjugatorInverseState := 219, conjugatorInverseCentral := 4, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 36, inverseFactorRightCentral := 4, orbitPenultimateState := 280, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 226. -/
def alternatingSixSchurConjugacyDatumRow226 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 28, conjugatorState := 133, orbitMiddleState := 330, orbitMiddleCentral := 0, conjugatorInverseState := 143, conjugatorInverseCentral := 0, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 0, orbitPenultimateState := 291, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 33, orbitMiddleState := 118, orbitMiddleCentral := 3, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 220, orbitPenultimateCentral := 0 },
    { classIndex := 28, conjugatorState := 33, orbitMiddleState := 118, orbitMiddleCentral := 4, conjugatorInverseState := 47, conjugatorInverseCentral := 1, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 1, orbitPenultimateState := 220, orbitPenultimateCentral := 1 },
    { classIndex := 27, conjugatorState := 205, orbitMiddleState := 235, orbitMiddleCentral := 2, conjugatorInverseState := 199, conjugatorInverseCentral := 3, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 3, orbitPenultimateState := 336, orbitPenultimateCentral := 3 },
    { classIndex := 28, conjugatorState := 205, orbitMiddleState := 235, orbitMiddleCentral := 3, conjugatorInverseState := 199, conjugatorInverseCentral := 3, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 3, orbitPenultimateState := 336, orbitPenultimateCentral := 4 },
    { classIndex := 27, conjugatorState := 133, orbitMiddleState := 330, orbitMiddleCentral := 5, conjugatorInverseState := 143, conjugatorInverseCentral := 0, inverseFactorLeftState := 25, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 0, orbitPenultimateState := 291, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 227. -/
def alternatingSixSchurConjugacyDatumRow227 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 30, conjugatorState := 178, orbitMiddleState := 328, orbitMiddleCentral := 3, conjugatorInverseState := 204, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 5, orbitPenultimateState := 149, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 45, orbitMiddleState := 82, orbitMiddleCentral := 2, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 144, orbitPenultimateCentral := 4 },
    { classIndex := 30, conjugatorState := 45, orbitMiddleState := 82, orbitMiddleCentral := 3, conjugatorInverseState := 48, conjugatorInverseCentral := 4, inverseFactorLeftState := 8, inverseFactorLeftCentral := 0, inverseFactorRightState := 15, inverseFactorRightCentral := 4, orbitPenultimateState := 144, orbitPenultimateCentral := 5 },
    { classIndex := 29, conjugatorState := 155, orbitMiddleState := 242, orbitMiddleCentral := 0, conjugatorInverseState := 130, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 290, orbitPenultimateCentral := 0 },
    { classIndex := 30, conjugatorState := 155, orbitMiddleState := 242, orbitMiddleCentral := 1, conjugatorInverseState := 130, conjugatorInverseCentral := 2, inverseFactorLeftState := 21, inverseFactorLeftCentral := 0, inverseFactorRightState := 17, inverseFactorRightCentral := 2, orbitPenultimateState := 290, orbitPenultimateCentral := 1 },
    { classIndex := 29, conjugatorState := 178, orbitMiddleState := 328, orbitMiddleCentral := 2, conjugatorInverseState := 204, conjugatorInverseCentral := 5, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 42, inverseFactorRightCentral := 5, orbitPenultimateState := 149, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 228. -/
def alternatingSixSchurConjugacyDatumRow228 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 11, conjugatorState := 132, orbitMiddleState := 182, orbitMiddleCentral := 2, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 270, orbitPenultimateCentral := 3 },
    { classIndex := 12, conjugatorState := 132, orbitMiddleState := 182, orbitMiddleCentral := 3, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 270, orbitPenultimateCentral := 4 },
    { classIndex := 13, conjugatorState := 132, orbitMiddleState := 182, orbitMiddleCentral := 4, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 270, orbitPenultimateCentral := 5 },
    { classIndex := 14, conjugatorState := 132, orbitMiddleState := 182, orbitMiddleCentral := 5, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 270, orbitPenultimateCentral := 0 },
    { classIndex := 9, conjugatorState := 132, orbitMiddleState := 182, orbitMiddleCentral := 0, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 270, orbitPenultimateCentral := 1 },
    { classIndex := 10, conjugatorState := 132, orbitMiddleState := 182, orbitMiddleCentral := 1, conjugatorInverseState := 126, conjugatorInverseCentral := 2, inverseFactorLeftState := 20, inverseFactorLeftCentral := 0, inverseFactorRightState := 21, inverseFactorRightCentral := 2, orbitPenultimateState := 270, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 229. -/
def alternatingSixSchurConjugacyDatumRow229 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 20, conjugatorState := 256, orbitMiddleState := 328, orbitMiddleCentral := 5, conjugatorInverseState := 244, conjugatorInverseCentral := 5, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 307, orbitPenultimateCentral := 3 },
    { classIndex := 15, conjugatorState := 256, orbitMiddleState := 328, orbitMiddleCentral := 0, conjugatorInverseState := 244, conjugatorInverseCentral := 5, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 307, orbitPenultimateCentral := 4 },
    { classIndex := 16, conjugatorState := 256, orbitMiddleState := 328, orbitMiddleCentral := 1, conjugatorInverseState := 244, conjugatorInverseCentral := 5, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 307, orbitPenultimateCentral := 5 },
    { classIndex := 17, conjugatorState := 256, orbitMiddleState := 328, orbitMiddleCentral := 2, conjugatorInverseState := 244, conjugatorInverseCentral := 5, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 307, orbitPenultimateCentral := 0 },
    { classIndex := 18, conjugatorState := 256, orbitMiddleState := 328, orbitMiddleCentral := 3, conjugatorInverseState := 244, conjugatorInverseCentral := 5, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 307, orbitPenultimateCentral := 1 },
    { classIndex := 19, conjugatorState := 256, orbitMiddleState := 328, orbitMiddleCentral := 4, conjugatorInverseState := 244, conjugatorInverseCentral := 5, inverseFactorLeftState := 40, inverseFactorLeftCentral := 0, inverseFactorRightState := 40, inverseFactorRightCentral := 5, orbitPenultimateState := 307, orbitPenultimateCentral := 2 }
  ]


end GroupTheory
end McKayConjecture
