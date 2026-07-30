/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAutomorphisms

/-!
# Exact class-action data for the two audited outer automorphisms

The seven base words are the identity, `a`, `b`, `ab`, `ab²`, and the two
long representatives with states 77 and 79.  The accompanying central
coordinate records the factor used by each of the 31 checked class
representatives.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- Evaluate one of the seven class-representative base words at two
coordinates. -/
def alternatingSixSchurOuterClassBaseImage
    (a b : AlternatingSixSchurCoordinates) :
    Fin 7 → AlternatingSixSchurCoordinates :=
  ![
    1,
    a,
    b,
    a * b,
    a * b * b,
    a * b * a * b * b * a * b⁻¹,
    a * b * a * b⁻¹ * a * b * b
  ]

/-- Base-word selector for the 31 checked representatives. -/
def alternatingSixSchurOuterClassBaseIndex :
    Fin 31 → Fin 7 :=
  ![
    0, 0, 0, 0, 0, 0,
    1, 1, 1,
    2, 2, 2, 2, 2, 2,
    3, 3, 3, 3, 3, 3,
    4, 4, 4, 4, 4, 4,
    5, 5,
    6, 6
  ]

/-- Central-coordinate selector for the 31 checked representatives. -/
def alternatingSixSchurOuterClassCentralIndex :
    Fin 31 → Fin 6 :=
  ![
    0, 1, 2, 3, 4, 5,
    0, 1, 2,
    0, 1, 2, 3, 4, 5,
    0, 1, 2, 3, 4, 5,
    0, 1, 2, 3, 4, 5,
    0, 1,
    0, 1
  ]

/-- Coordinate of the source generator `a`. -/
def alternatingSixSchurOuterClassSourceA :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedPresentationGeneratorCoordinates 0

/-- Coordinate of the source generator `b`. -/
def alternatingSixSchurOuterClassSourceB :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedPresentationGeneratorCoordinates 1

/-- The canonical representative splits into its base word and central
coordinate. -/
theorem alternatingSixSchurClassRepresentative_eq_outerBase_mul_central
    (index : Fin 31) :
    alternatingSixSchurClassRepresentative index =
      alternatingSixSchurOuterClassBaseImage
          alternatingSixSchurOuterClassSourceA
          alternatingSixSchurOuterClassSourceB
          (alternatingSixSchurOuterClassBaseIndex index) *
        alternatingSixSchurAuditedCoordinate 0
          (ZMod.finEquiv 6
            (alternatingSixSchurOuterClassCentralIndex index)) := by
  fin_cases index <;> decide

/-- Exact class permutation induced by the first audited automorphism. -/
def alternatingSixSchurAlphaOneClassIndexAction :
    Equiv.Perm (Fin 31) :=
  Equiv.ofBijective
    ![
      0, 5, 4, 3, 2, 1,
      8, 7, 6,
      12, 11, 10, 9, 14, 13,
      21, 26, 25, 24, 23, 22,
      15, 20, 19, 18, 17, 16,
      27, 28, 29, 30
    ]
    (by decide)

/-- Exact class permutation induced by the second audited automorphism. -/
def alternatingSixSchurAlphaTwoClassIndexAction :
    Equiv.Perm (Fin 31) :=
  Equiv.ofBijective
    ![
      0, 5, 4, 3, 2, 1,
      8, 7, 6,
      9, 14, 13, 12, 11, 10,
      19, 18, 17, 16, 15, 20,
      23, 22, 21, 26, 25, 24,
      29, 30, 27, 28
    ]
    (by decide)

/-- Both coordinate automorphisms invert the central coordinate. -/
def alternatingSixSchurOuterClassInvertedCentral
    (index : Fin 31) :
    ZMod 6 :=
  -(ZMod.finEquiv 6
      (alternatingSixSchurOuterClassCentralIndex index))

/-- Predicted image coordinate of a representative under `alpha1`. -/
def alternatingSixSchurAlphaOneClassRepresentativeImage
    (index : Fin 31) :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurOuterClassBaseImage
      (alternatingSixSchurAlphaOneGeneratorCoordinates 0)
      (alternatingSixSchurAlphaOneGeneratorCoordinates 1)
      (alternatingSixSchurOuterClassBaseIndex index) *
    alternatingSixSchurAuditedCoordinate 0
      (alternatingSixSchurOuterClassInvertedCentral index)

/-- Predicted image coordinate of a representative under `alpha2`. -/
def alternatingSixSchurAlphaTwoClassRepresentativeImage
    (index : Fin 31) :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurOuterClassBaseImage
      (alternatingSixSchurAlphaTwoGeneratorCoordinates 0)
      (alternatingSixSchurAlphaTwoGeneratorCoordinates 1)
      (alternatingSixSchurOuterClassBaseIndex index) *
    alternatingSixSchurAuditedCoordinate 0
      (alternatingSixSchurOuterClassInvertedCentral index)

end GroupTheory
end McKayConjecture
