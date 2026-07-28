/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverCoordinateModel
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverRepresentation

/-!
# Presentation-generator data for two outer automorphisms of `6.A₆`

The reproducible GAP audit `scripts/a6_outer_action_audit.g` constructs the
exact six-generator presentation used by this project, proves that it is
isomorphic to GAP's Schur cover, and then expresses the unique lifts of the
two standard outer automorphisms in the project's shortlex coordinates.

The source generator coordinates are

* `a = (1,0)` and `b = (2,0)`;
* `k₀ = (0,1)`, `k₁ = (0,3)`, `k₂ = (0,5)`, and `k₃ = (0,1)`.

For orientation, shortlex state `52` is
`a b a b⁻¹ a b⁻¹`, state `63` is `b a b⁻¹ a b a`, and state `317` is
`b a b² a b a b⁻¹ a b a b`.

The GAP audit verifies the presentation alignment and the source
isomorphism externally.  Lean checks below that both six-tuples satisfy
all presentation relations, then packages the induced homomorphisms.
The companion outer-automorphism check modules prove bijectivity.
Matching these automorphisms with the copied CTblLib character
permutations remains a separate obligation.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- Coordinates of `a`, `b`, and `k₀,…,k₃` under the presentation
alignment independently audited in GAP. -/
def alternatingSixSchurAuditedPresentationGeneratorCoordinates :
    Fin 6 → AlternatingSixSchurCoordinates :=
  ![
    { state := 1, central := 0 },
    { state := 2, central := 0 },
    { state := 0, central := 1 },
    { state := 0, central := 3 },
    { state := 0, central := 5 },
    { state := 0, central := 1 }
  ]

/-- Audited images of the six presentation generators under the lift of
the outer generator associated with `A6.2_1`. -/
def alternatingSixSchurAlphaOneGeneratorCoordinates :
    Fin 6 → AlternatingSixSchurCoordinates :=
  ![
    { state := 1, central := 2 },
    { state := 63, central := 2 },
    { state := 0, central := 5 },
    { state := 0, central := 3 },
    { state := 0, central := 1 },
    { state := 0, central := 5 }
  ]

/-- Audited images of the six presentation generators under the lift of
the outer generator associated with `A6.2_2`. -/
def alternatingSixSchurAlphaTwoGeneratorCoordinates :
    Fin 6 → AlternatingSixSchurCoordinates :=
  ![
    { state := 317, central := 1 },
    { state := 52, central := 4 },
    { state := 0, central := 5 },
    { state := 0, central := 3 },
    { state := 0, central := 1 },
    { state := 0, central := 5 }
  ]

/-- A compact constructor for audited coordinate certificates. -/
def alternatingSixSchurAuditedCoordinate
    (state : Fin 360) (central : ZMod 6) :
    AlternatingSixSchurCoordinates :=
  { state := state, central := central }

/-- Four checked multiplication steps suffice to certify a fifth power
without forcing the kernel to normalize one large nested computation. -/
theorem pow_five_eq_of_mul_chain
    {G : Type*} [Group G]
    (x xTwo xThree xFour xFive : G)
    (hTwo : x * x = xTwo)
    (hThree : xTwo * x = xThree)
    (hFour : xThree * x = xFour)
    (hFive : xFour * x = xFive) :
    x ^ 5 = xFive := by
  calc
    x ^ 5 = (((x * x) * x) * x) * x := by
      simp only [pow_succ, pow_zero, one_mul]
    _ = ((xTwo * x) * x) * x := by rw [hTwo]
    _ = (xThree * x) * x := by rw [hThree]
    _ = xFour * x := by rw [hFour]
    _ = xFive := hFive

/-- A coordinate with shortlex state zero is central. -/
theorem alternatingSixSchurCoordinate_state_zero_commute
    (central : ZMod 6)
    (coordinate : AlternatingSixSchurCoordinates) :
    Commute
      ({ state := 0, central := central } :
        AlternatingSixSchurCoordinates)
      coordinate := by
  have hcentral :
      AlternatingSixSchurCoordinates.evaluate
          ({ state := 0, central := central } :
            AlternatingSixSchurCoordinates) =
        AlternatingSixSchurCoordinates.centralValue central := by
    change
      alternatingSixSchurNormalElement 0 *
          AlternatingSixSchurCoordinates.centralValue central =
        AlternatingSixSchurCoordinates.centralValue central
    change
      alternatingSixSchurWord [] *
          AlternatingSixSchurCoordinates.centralValue central =
        AlternatingSixSchurCoordinates.centralValue central
    rw [alternatingSixSchurWord_nil, one_mul]
  apply AlternatingSixSchurCoordinates.evaluate_bijective.injective
  rw [AlternatingSixSchurCoordinates.evaluate_mul,
    AlternatingSixSchurCoordinates.evaluate_mul, hcentral]
  exact
    (AlternatingSixSchurCoordinates.centralValue_commute
      central
      (AlternatingSixSchurCoordinates.evaluate coordinate)).eq

/-!
The four base-relator checks for each audited assignment are deliberately
split into small coordinate calculations.  This keeps kernel reduction at
the default resource limits: every `decide` below checks at most one
coordinate multiplication.
-/

theorem alternatingSixSchurAlphaOne_baseRelator_zero :
    alternatingSixSchurAlphaOneGeneratorCoordinates 0 ^ 2 =
      alternatingSixSchurAlphaOneGeneratorCoordinates 2 := by
  decide

theorem alternatingSixSchurAlphaOne_baseRelator_one :
    alternatingSixSchurAlphaOneGeneratorCoordinates 1 ^ 4 =
      alternatingSixSchurAlphaOneGeneratorCoordinates 3 := by
  decide

theorem alternatingSixSchurAlphaOne_baseRelator_two :
    (alternatingSixSchurAlphaOneGeneratorCoordinates 0 *
        alternatingSixSchurAlphaOneGeneratorCoordinates 1) ^ 5 =
      alternatingSixSchurAlphaOneGeneratorCoordinates 4 := by
  rw [show
    alternatingSixSchurAlphaOneGeneratorCoordinates 0 *
        alternatingSixSchurAlphaOneGeneratorCoordinates 1 =
      alternatingSixSchurAuditedCoordinate 78 4 by decide]
  exact
    pow_five_eq_of_mul_chain
      (alternatingSixSchurAuditedCoordinate 78 4)
      (alternatingSixSchurAuditedCoordinate 299 4)
      (alternatingSixSchurAuditedCoordinate 281 1)
      (alternatingSixSchurAuditedCoordinate 86 5)
      (alternatingSixSchurAuditedCoordinate 0 1)
      (by decide) (by decide) (by decide) (by decide)

theorem alternatingSixSchurAlphaOne_baseRelator_three :
    (alternatingSixSchurAlphaOneGeneratorCoordinates 0 *
        alternatingSixSchurAlphaOneGeneratorCoordinates 1 ^ 2) ^ 5 =
      alternatingSixSchurAlphaOneGeneratorCoordinates 5 := by
  rw [show
    alternatingSixSchurAlphaOneGeneratorCoordinates 1 ^ 2 =
      alternatingSixSchurAuditedCoordinate 312 5 by decide]
  rw [show
    alternatingSixSchurAlphaOneGeneratorCoordinates 0 *
        alternatingSixSchurAuditedCoordinate 312 5 =
      alternatingSixSchurAuditedCoordinate 297 2 by decide]
  exact
    pow_five_eq_of_mul_chain
      (alternatingSixSchurAuditedCoordinate 297 2)
      (alternatingSixSchurAuditedCoordinate 213 1)
      (alternatingSixSchurAuditedCoordinate 182 0)
      (alternatingSixSchurAuditedCoordinate 284 1)
      (alternatingSixSchurAuditedCoordinate 0 5)
      (by decide) (by decide) (by decide) (by decide)

theorem alternatingSixSchurAlphaTwo_baseRelator_zero :
    alternatingSixSchurAlphaTwoGeneratorCoordinates 0 ^ 2 =
      alternatingSixSchurAlphaTwoGeneratorCoordinates 2 := by
  decide

theorem alternatingSixSchurAlphaTwo_baseRelator_one :
    alternatingSixSchurAlphaTwoGeneratorCoordinates 1 ^ 4 =
      alternatingSixSchurAlphaTwoGeneratorCoordinates 3 := by
  decide

theorem alternatingSixSchurAlphaTwo_baseRelator_two :
    (alternatingSixSchurAlphaTwoGeneratorCoordinates 0 *
        alternatingSixSchurAlphaTwoGeneratorCoordinates 1) ^ 5 =
      alternatingSixSchurAlphaTwoGeneratorCoordinates 4 := by
  rw [show
    alternatingSixSchurAlphaTwoGeneratorCoordinates 0 *
        alternatingSixSchurAlphaTwoGeneratorCoordinates 1 =
      alternatingSixSchurAuditedCoordinate 284 2 by decide]
  exact
    pow_five_eq_of_mul_chain
      (alternatingSixSchurAuditedCoordinate 284 2)
      (alternatingSixSchurAuditedCoordinate 182 1)
      (alternatingSixSchurAuditedCoordinate 213 2)
      (alternatingSixSchurAuditedCoordinate 297 3)
      (alternatingSixSchurAuditedCoordinate 0 1)
      (by decide) (by decide) (by decide) (by decide)

theorem alternatingSixSchurAlphaTwo_baseRelator_three :
    (alternatingSixSchurAlphaTwoGeneratorCoordinates 0 *
        alternatingSixSchurAlphaTwoGeneratorCoordinates 1 ^ 2) ^ 5 =
      alternatingSixSchurAlphaTwoGeneratorCoordinates 5 := by
  rw [show
    alternatingSixSchurAlphaTwoGeneratorCoordinates 1 ^ 2 =
      alternatingSixSchurAuditedCoordinate 307 2 by decide]
  rw [show
    alternatingSixSchurAlphaTwoGeneratorCoordinates 0 =
      alternatingSixSchurAuditedCoordinate 317 1 by rfl]
  rw [show
    alternatingSixSchurAuditedCoordinate 307 2 =
      alternatingSixSchurAuditedCoordinate 52 0 *
        alternatingSixSchurAuditedCoordinate 52 2 by decide]
  rw [← mul_assoc]
  rw [show
    alternatingSixSchurAuditedCoordinate 317 1 *
        alternatingSixSchurAuditedCoordinate 52 0 =
      alternatingSixSchurAuditedCoordinate 284 4 by decide]
  rw [show
    alternatingSixSchurAuditedCoordinate 284 4 *
        alternatingSixSchurAuditedCoordinate 52 2 =
      alternatingSixSchurAuditedCoordinate 175 3 by decide]
  exact
    pow_five_eq_of_mul_chain
      (alternatingSixSchurAuditedCoordinate 175 3)
      (alternatingSixSchurAuditedCoordinate 291 5)
      (alternatingSixSchurAuditedCoordinate 269 1)
      (alternatingSixSchurAuditedCoordinate 195 1)
      (alternatingSixSchurAuditedCoordinate 0 5)
      (by decide) (by decide) (by decide) (by decide)

/-- Lean verification that the audited `alpha1` generator images satisfy
all relations of the Schur-cover presentation. -/
def alternatingSixSchurAlphaOneRepresentationData :
    AlternatingSixSchurRepresentationData
      AlternatingSixSchurCoordinates where
  generator := alternatingSixSchurAlphaOneGeneratorCoordinates
  baseRelator_eq i := by
    fin_cases i
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaOne_baseRelator_zero
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaOne_baseRelator_one
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaOne_baseRelator_two
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaOne_baseRelator_three
  centrality i j := by
    fin_cases i <;>
      apply alternatingSixSchurCoordinate_state_zero_commute
  lattice_one := by decide
  lattice_two := by decide

/-- Lean verification that the audited `alpha2` generator images satisfy
all relations of the Schur-cover presentation. -/
def alternatingSixSchurAlphaTwoRepresentationData :
    AlternatingSixSchurRepresentationData
      AlternatingSixSchurCoordinates where
  generator := alternatingSixSchurAlphaTwoGeneratorCoordinates
  baseRelator_eq i := by
    fin_cases i
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaTwo_baseRelator_zero
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaTwo_baseRelator_one
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaTwo_baseRelator_two
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          alternatingSixSchurAlphaTwo_baseRelator_three
  centrality i j := by
    fin_cases i <;>
      apply alternatingSixSchurCoordinate_state_zero_commute
  lattice_one := by decide
  lattice_two := by decide

/-- The coordinate endomorphism induced by the first audited generator
assignment. -/
def alternatingSixSchurAlphaOneEndomorphism :
    AlternatingSixSchurCoordinates →*
      AlternatingSixSchurCoordinates :=
  alternatingSixSchurAlphaOneRepresentationData.toMonoidHom.comp
    AlternatingSixSchurCoordinates.evaluateHom

/-- The coordinate endomorphism induced by the second audited generator
assignment.  Its GAP representative has order eight; only its action
modulo inner automorphisms has order two. -/
def alternatingSixSchurAlphaTwoEndomorphism :
    AlternatingSixSchurCoordinates →*
      AlternatingSixSchurCoordinates :=
  alternatingSixSchurAlphaTwoRepresentationData.toMonoidHom.comp
    AlternatingSixSchurCoordinates.evaluateHom

end GroupTheory
end McKayConjecture
