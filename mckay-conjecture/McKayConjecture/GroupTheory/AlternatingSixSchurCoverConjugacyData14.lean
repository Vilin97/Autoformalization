/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyCertificateTypes

/-!
# Sixfold-cover conjugacy data, states 140–149

Generated class labels and orbit witnesses for one block
of normal-word states.  The accompanying check modules
verify the data against the group law.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- Certificate data above normal-word state 140. -/
def alternatingSixSchurConjugacyDatumRow140 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 16, conjugatorState := 13, orbitMiddleState := 40, orbitMiddleCentral := 1, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 1 },
    { classIndex := 17, conjugatorState := 13, orbitMiddleState := 40, orbitMiddleCentral := 2, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 2 },
    { classIndex := 18, conjugatorState := 13, orbitMiddleState := 40, orbitMiddleCentral := 3, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 3 },
    { classIndex := 19, conjugatorState := 13, orbitMiddleState := 40, orbitMiddleCentral := 4, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 4 },
    { classIndex := 20, conjugatorState := 13, orbitMiddleState := 40, orbitMiddleCentral := 5, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 5 },
    { classIndex := 15, conjugatorState := 13, orbitMiddleState := 40, orbitMiddleCentral := 0, conjugatorInverseState := 13, conjugatorInverseCentral := 5, inverseFactorLeftState := 2, inverseFactorLeftCentral := 0, inverseFactorRightState := 5, inverseFactorRightCentral := 5, orbitPenultimateState := 64, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 141. -/
def alternatingSixSchurConjugacyDatumRow141 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 24, conjugatorState := 147, orbitMiddleState := 182, orbitMiddleCentral := 0, conjugatorInverseState := 138, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 5 },
    { classIndex := 25, conjugatorState := 147, orbitMiddleState := 182, orbitMiddleCentral := 1, conjugatorInverseState := 138, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 0 },
    { classIndex := 26, conjugatorState := 147, orbitMiddleState := 182, orbitMiddleCentral := 2, conjugatorInverseState := 138, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 1 },
    { classIndex := 21, conjugatorState := 147, orbitMiddleState := 182, orbitMiddleCentral := 3, conjugatorInverseState := 138, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 2 },
    { classIndex := 22, conjugatorState := 147, orbitMiddleState := 182, orbitMiddleCentral := 4, conjugatorInverseState := 138, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 3 },
    { classIndex := 23, conjugatorState := 147, orbitMiddleState := 182, orbitMiddleCentral := 5, conjugatorInverseState := 138, conjugatorInverseCentral := 0, inverseFactorLeftState := 24, inverseFactorLeftCentral := 0, inverseFactorRightState := 23, inverseFactorRightCentral := 0, orbitPenultimateState := 202, orbitPenultimateCentral := 4 }
  ]

/-- Certificate data above normal-word state 142. -/
def alternatingSixSchurConjugacyDatumRow142 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 270, orbitMiddleState := 302, orbitMiddleCentral := 5, conjugatorInverseState := 265, conjugatorInverseCentral := 3, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 58, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 270, orbitMiddleState := 302, orbitMiddleCentral := 0, conjugatorInverseState := 265, conjugatorInverseCentral := 3, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 58, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 270, orbitMiddleState := 302, orbitMiddleCentral := 1, conjugatorInverseState := 265, conjugatorInverseCentral := 3, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 58, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 270, orbitMiddleState := 302, orbitMiddleCentral := 2, conjugatorInverseState := 265, conjugatorInverseCentral := 3, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 58, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 270, orbitMiddleState := 302, orbitMiddleCentral := 3, conjugatorInverseState := 265, conjugatorInverseCentral := 3, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 58, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 270, orbitMiddleState := 302, orbitMiddleCentral := 4, conjugatorInverseState := 265, conjugatorInverseCentral := 3, inverseFactorLeftState := 31, inverseFactorLeftCentral := 0, inverseFactorRightState := 58, inverseFactorRightCentral := 3, orbitPenultimateState := 300, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 143. -/
def alternatingSixSchurConjugacyDatumRow143 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 55, orbitMiddleState := 83, orbitMiddleCentral := 1, conjugatorInverseState := 50, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 198, orbitPenultimateCentral := 3 },
    { classIndex := 11, conjugatorState := 55, orbitMiddleState := 83, orbitMiddleCentral := 2, conjugatorInverseState := 50, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 198, orbitPenultimateCentral := 4 },
    { classIndex := 12, conjugatorState := 55, orbitMiddleState := 83, orbitMiddleCentral := 3, conjugatorInverseState := 50, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 198, orbitPenultimateCentral := 5 },
    { classIndex := 13, conjugatorState := 55, orbitMiddleState := 83, orbitMiddleCentral := 4, conjugatorInverseState := 50, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 198, orbitPenultimateCentral := 0 },
    { classIndex := 14, conjugatorState := 55, orbitMiddleState := 83, orbitMiddleCentral := 5, conjugatorInverseState := 50, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 198, orbitPenultimateCentral := 1 },
    { classIndex := 9, conjugatorState := 55, orbitMiddleState := 83, orbitMiddleCentral := 0, conjugatorInverseState := 50, conjugatorInverseCentral := 0, inverseFactorLeftState := 9, inverseFactorLeftCentral := 0, inverseFactorRightState := 14, inverseFactorRightCentral := 0, orbitPenultimateState := 198, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 144. -/
def alternatingSixSchurConjugacyDatumRow144 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 26, conjugatorState := 52, orbitMiddleState := 81, orbitMiddleCentral := 0, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 1 },
    { classIndex := 21, conjugatorState := 52, orbitMiddleState := 81, orbitMiddleCentral := 1, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 2 },
    { classIndex := 22, conjugatorState := 52, orbitMiddleState := 81, orbitMiddleCentral := 2, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 3 },
    { classIndex := 23, conjugatorState := 52, orbitMiddleState := 81, orbitMiddleCentral := 3, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 4 },
    { classIndex := 24, conjugatorState := 52, orbitMiddleState := 81, orbitMiddleCentral := 4, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 5 },
    { classIndex := 25, conjugatorState := 52, orbitMiddleState := 81, orbitMiddleCentral := 5, conjugatorInverseState := 60, conjugatorInverseCentral := 3, inverseFactorLeftState := 12, inverseFactorLeftCentral := 0, inverseFactorRightState := 11, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 145. -/
def alternatingSixSchurConjugacyDatumRow145 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 56, orbitMiddleState := 83, orbitMiddleCentral := 0, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 4 },
    { classIndex := 22, conjugatorState := 56, orbitMiddleState := 83, orbitMiddleCentral := 1, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 5 },
    { classIndex := 23, conjugatorState := 56, orbitMiddleState := 83, orbitMiddleCentral := 2, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 0 },
    { classIndex := 24, conjugatorState := 56, orbitMiddleState := 83, orbitMiddleCentral := 3, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 1 },
    { classIndex := 25, conjugatorState := 56, orbitMiddleState := 83, orbitMiddleCentral := 4, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 2 },
    { classIndex := 26, conjugatorState := 56, orbitMiddleState := 83, orbitMiddleCentral := 5, conjugatorInverseState := 74, conjugatorInverseCentral := 3, inverseFactorLeftState := 16, inverseFactorLeftCentral := 0, inverseFactorRightState := 9, inverseFactorRightCentral := 3, orbitPenultimateState := 54, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 146. -/
def alternatingSixSchurConjugacyDatumRow146 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 14, conjugatorState := 277, orbitMiddleState := 311, orbitMiddleCentral := 5, conjugatorInverseState := 272, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 53, inverseFactorRightCentral := 3, orbitPenultimateState := 350, orbitPenultimateCentral := 4 },
    { classIndex := 9, conjugatorState := 277, orbitMiddleState := 311, orbitMiddleCentral := 0, conjugatorInverseState := 272, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 53, inverseFactorRightCentral := 3, orbitPenultimateState := 350, orbitPenultimateCentral := 5 },
    { classIndex := 10, conjugatorState := 277, orbitMiddleState := 311, orbitMiddleCentral := 1, conjugatorInverseState := 272, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 53, inverseFactorRightCentral := 3, orbitPenultimateState := 350, orbitPenultimateCentral := 0 },
    { classIndex := 11, conjugatorState := 277, orbitMiddleState := 311, orbitMiddleCentral := 2, conjugatorInverseState := 272, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 53, inverseFactorRightCentral := 3, orbitPenultimateState := 350, orbitPenultimateCentral := 1 },
    { classIndex := 12, conjugatorState := 277, orbitMiddleState := 311, orbitMiddleCentral := 3, conjugatorInverseState := 272, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 53, inverseFactorRightCentral := 3, orbitPenultimateState := 350, orbitPenultimateCentral := 2 },
    { classIndex := 13, conjugatorState := 277, orbitMiddleState := 311, orbitMiddleCentral := 4, conjugatorInverseState := 272, conjugatorInverseCentral := 3, inverseFactorLeftState := 34, inverseFactorLeftCentral := 0, inverseFactorRightState := 53, inverseFactorRightCentral := 3, orbitPenultimateState := 350, orbitPenultimateCentral := 3 }
  ]

/-- Certificate data above normal-word state 147. -/
def alternatingSixSchurConjugacyDatumRow147 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 10, conjugatorState := 107, orbitMiddleState := 152, orbitMiddleCentral := 3, conjugatorInverseState := 87, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 207, orbitPenultimateCentral := 1 },
    { classIndex := 11, conjugatorState := 107, orbitMiddleState := 152, orbitMiddleCentral := 4, conjugatorInverseState := 87, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 207, orbitPenultimateCentral := 2 },
    { classIndex := 12, conjugatorState := 107, orbitMiddleState := 152, orbitMiddleCentral := 5, conjugatorInverseState := 87, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 207, orbitPenultimateCentral := 3 },
    { classIndex := 13, conjugatorState := 107, orbitMiddleState := 152, orbitMiddleCentral := 0, conjugatorInverseState := 87, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 207, orbitPenultimateCentral := 4 },
    { classIndex := 14, conjugatorState := 107, orbitMiddleState := 152, orbitMiddleCentral := 1, conjugatorInverseState := 87, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 207, orbitPenultimateCentral := 5 },
    { classIndex := 9, conjugatorState := 107, orbitMiddleState := 152, orbitMiddleCentral := 2, conjugatorInverseState := 87, conjugatorInverseCentral := 0, inverseFactorLeftState := 11, inverseFactorLeftCentral := 0, inverseFactorRightState := 25, inverseFactorRightCentral := 0, orbitPenultimateState := 207, orbitPenultimateCentral := 0 }
  ]

/-- Certificate data above normal-word state 148. -/
def alternatingSixSchurConjugacyDatumRow148 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 21, conjugatorState := 142, orbitMiddleState := 213, orbitMiddleCentral := 3, conjugatorInverseState := 151, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 3 },
    { classIndex := 22, conjugatorState := 142, orbitMiddleState := 213, orbitMiddleCentral := 4, conjugatorInverseState := 151, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 4 },
    { classIndex := 23, conjugatorState := 142, orbitMiddleState := 213, orbitMiddleCentral := 5, conjugatorInverseState := 151, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 5 },
    { classIndex := 24, conjugatorState := 142, orbitMiddleState := 213, orbitMiddleCentral := 0, conjugatorInverseState := 151, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 0 },
    { classIndex := 25, conjugatorState := 142, orbitMiddleState := 213, orbitMiddleCentral := 1, conjugatorInverseState := 151, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 1 },
    { classIndex := 26, conjugatorState := 142, orbitMiddleState := 213, orbitMiddleCentral := 2, conjugatorInverseState := 151, conjugatorInverseCentral := 0, inverseFactorLeftState := 27, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 194, orbitPenultimateCentral := 2 }
  ]

/-- Certificate data above normal-word state 149. -/
def alternatingSixSchurConjugacyDatumRow149 :
    Fin 6 → AlternatingSixSchurConjugacyDatum :=
  ![
    { classIndex := 18, conjugatorState := 143, orbitMiddleState := 250, orbitMiddleCentral := 3, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 257, orbitPenultimateCentral := 5 },
    { classIndex := 19, conjugatorState := 143, orbitMiddleState := 250, orbitMiddleCentral := 4, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 257, orbitPenultimateCentral := 0 },
    { classIndex := 20, conjugatorState := 143, orbitMiddleState := 250, orbitMiddleCentral := 5, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 257, orbitPenultimateCentral := 1 },
    { classIndex := 15, conjugatorState := 143, orbitMiddleState := 250, orbitMiddleCentral := 0, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 257, orbitPenultimateCentral := 2 },
    { classIndex := 16, conjugatorState := 143, orbitMiddleState := 250, orbitMiddleCentral := 1, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 257, orbitPenultimateCentral := 3 },
    { classIndex := 17, conjugatorState := 143, orbitMiddleState := 250, orbitMiddleCentral := 2, conjugatorInverseState := 133, conjugatorInverseCentral := 0, inverseFactorLeftState := 22, inverseFactorLeftCentral := 0, inverseFactorRightState := 28, inverseFactorRightCentral := 0, orbitPenultimateState := 257, orbitPenultimateCentral := 4 }
  ]


end GroupTheory
end McKayConjecture
