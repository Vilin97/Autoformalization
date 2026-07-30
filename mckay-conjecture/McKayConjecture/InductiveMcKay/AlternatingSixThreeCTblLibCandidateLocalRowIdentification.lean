/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibAmbientPositionBlocks
import McKayConjecture.InductiveMcKay.AutomorphismStabilizerCorrectionRowIndependence

/-!
# An invariant-safe candidate for the local CTblLib rows of three-local `A₆`

This file records a proposed local CTblLib ordering suggested by the
coordinate character table of the actual Sylow-three normalizer.  The eight
linear rows are ordered by frequencies

`[0, 4, 2, 6, 1, 3, 5, 7]`,

and the four degree-four rows are ordered lexicographically by their orbit
and extension coordinates.  The candidate is compatible with the CTblLib
degree and central-sign blocks.  Its semantic status remains explicit: both
actual-normalizer generator bridges are reduced below to eleven seed
equations and are not asserted unconditionally.

The file also records a fully computable correction of each audited outer
automorphism at the explicit Schur-coordinate Sylow subgroup.  Transporting
these calculations through the noncomputable fixed-Sylow conjugacy and then
evaluating the coordinate characters is the remaining semantic step.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeCandidateLocalFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ### The candidate local position equivalence -/

/-- A proposed invariant-safe CTblLib local position order. -/
def alternatingSixThreeCTblLibCandidateLocalPositionEquiv :
    Fin 12 ≃ AlternatingSixThreeConcreteNormalizerRow :=
  Equiv.ofBijective
    ![Sum.inl 0,
      Sum.inl 4,
      Sum.inl 2,
      Sum.inl 6,
      Sum.inl 1,
      Sum.inl 3,
      Sum.inl 5,
      Sum.inl 7,
      Sum.inr (0, 0),
      Sum.inr (0, 1),
      Sum.inr (1, 0),
      Sum.inr (1, 1)]
    (by decide)

/-- The local ordinary-character degree advertised by CTblLib. -/
def alternatingSixCTblLibThreeLocalDegree : Fin 12 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4]

/-- The central scalar exponent advertised by a coordinate local row.
For linear rows it is the parity of the cyclic-eight frequency; for the
degree-four rows it is the extension coordinate. -/
def alternatingSixThreeConcreteNormalizerRowCentralExponent :
    AlternatingSixThreeConcreteNormalizerRow → Fin 6
  | Sum.inl j => if Even j.val then 0 else 3
  | Sum.inr r => if r.2 = 0 then 0 else 3

/-- The candidate ordering has exactly the CTblLib local degrees. -/
theorem alternatingSixThreeCTblLibCandidateLocalPositionEquiv_degree
    (i : Fin 12) :
    alternatingSixThreeConcreteNormalizerRowDegree
        (alternatingSixThreeCTblLibCandidateLocalPositionEquiv i) =
      alternatingSixCTblLibThreeLocalDegree i := by
  fin_cases i <;>
    simp [
      alternatingSixThreeCTblLibCandidateLocalPositionEquiv,
      alternatingSixCTblLibThreeLocalDegree
    ]

/-- The candidate ordering has exactly the audited CTblLib central signs. -/
theorem
    alternatingSixThreeCTblLibCandidateLocalPositionEquiv_centralExponent
    (i : Fin 12) :
    alternatingSixThreeConcreteNormalizerRowCentralExponent
        (alternatingSixThreeCTblLibCandidateLocalPositionEquiv i) =
      alternatingSixCTblLibThreePPrimeActionData.localCentralExponent i := by
  fin_cases i <;>
    decide

/-- Pair the candidate local order with the reproduced ATLAS-aligned
ambient order. -/
def alternatingSixThreeCTblLibCandidateRowIdentification :
    AlternatingSixThreeCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixThreeAtlasAlignedAmbientPositionEquiv
  localPositionEquiv :=
    alternatingSixThreeCTblLibCandidateLocalPositionEquiv

theorem alternatingSixThreeCTblLibCandidateRowIdentification_hasTrivial :
    alternatingSixThreeCTblLibCandidateRowIdentification
      |>.HasSemanticTrivialPosition := by
  constructor <;>
    rfl

/-! ### Computable corrections at the explicit Schur Sylow -/

private def explicitThreeZ : AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedCoordinate 0 2

private def explicitThreeX : AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedCoordinate 276 1

private def explicitThreeY : AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedCoordinate 200 1

private def explicitThreeT : AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedCoordinate 224 0

/-- An explicit correction for the first audited automorphism at the
computable Sylow-three subgroup. -/
def alternatingSixThreeExplicitAlphaOneCorrection :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedCoordinate 1 0

/-- An explicit correction for the second audited automorphism at the
computable Sylow-three subgroup. -/
def alternatingSixThreeExplicitAlphaTwoCorrection :
    AlternatingSixSchurCoordinates :=
  alternatingSixSchurAuditedCoordinate 5 0

private def explicitCorrectedAlphaOne
    (g : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  alternatingSixThreeExplicitAlphaOneCorrection *
      alternatingSixSchurAlphaOneEndomorphism g *
    alternatingSixThreeExplicitAlphaOneCorrection⁻¹

private def explicitCorrectedAlphaTwo
    (g : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  alternatingSixThreeExplicitAlphaTwoCorrection *
      alternatingSixSchurAlphaTwoEndomorphism g *
    alternatingSixThreeExplicitAlphaTwoCorrection⁻¹

/-- The first explicit correction inverts `Z`. -/
theorem alternatingSixThreeExplicitCorrectedAlphaOne_Z :
    explicitCorrectedAlphaOne explicitThreeZ = explicitThreeZ ^ 2 := by
  decide

/-- The first explicit correction sends `X` to `ZX`. -/
theorem alternatingSixThreeExplicitCorrectedAlphaOne_X :
    explicitCorrectedAlphaOne explicitThreeX =
      explicitThreeZ * explicitThreeX := by
  decide

/-- The second explicit correction inverts `Z`. -/
theorem alternatingSixThreeExplicitCorrectedAlphaTwo_Z :
    explicitCorrectedAlphaTwo explicitThreeZ = explicitThreeZ ^ 2 := by
  decide

/-! ### Exact semantic remainder -/

namespace AlternatingSixThreeCTblLibRowIdentification

variable (identification : AlternatingSixThreeCTblLibRowIdentification)

/-- The first local bridge restricted to the nontrivial CT positions. -/
def LocalCorrectedAlphaOneBridgeAwayFromTrivial : Prop :=
  ∀ i : Fin 12, i ≠ 0 →
    alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
        (identification.localPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.localAlphaOne i)

/-- The second local bridge restricted to the nontrivial CT positions. -/
def LocalCorrectedAlphaTwoBridgeAwayFromTrivial : Prop :=
  ∀ i : Fin 12, i ≠ 0 →
    alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
        (identification.localPositionEquiv i) =
      identification.localPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.localAlphaTwo i)

theorem localCorrectedAlphaOneBridge_iff_awayFromTrivial
    (htrivial : identification.HasSemanticTrivialPosition) :
    identification.LocalCorrectedAlphaOneBridge ↔
      identification.LocalCorrectedAlphaOneBridgeAwayFromTrivial := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : i = 0
    · subst i
      exact identification.localCorrectedAlphaOneBridge_zero htrivial
    · exact h i hi

theorem localCorrectedAlphaTwoBridge_iff_awayFromTrivial
    (htrivial : identification.HasSemanticTrivialPosition) :
    identification.LocalCorrectedAlphaTwoBridge ↔
      identification.LocalCorrectedAlphaTwoBridgeAwayFromTrivial := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : i = 0
    · subst i
      exact identification.localCorrectedAlphaTwoBridge_zero htrivial
    · exact h i hi

end AlternatingSixThreeCTblLibRowIdentification

/-- For the candidate identification, the first semantic local bridge is
exactly the eleven nontrivial row equations. -/
theorem
    alternatingSixThreeCTblLibCandidate_localAlphaOneBridge_iff_elevenSeeds :
    (alternatingSixThreeCTblLibCandidateRowIdentification
      |>.LocalCorrectedAlphaOneBridge) ↔
      (alternatingSixThreeCTblLibCandidateRowIdentification
        |>.LocalCorrectedAlphaOneBridgeAwayFromTrivial) :=
  alternatingSixThreeCTblLibCandidateRowIdentification
    |>.localCorrectedAlphaOneBridge_iff_awayFromTrivial
      alternatingSixThreeCTblLibCandidateRowIdentification_hasTrivial

/-- For the candidate identification, the second semantic local bridge is
exactly the eleven nontrivial row equations. -/
theorem
    alternatingSixThreeCTblLibCandidate_localAlphaTwoBridge_iff_elevenSeeds :
    (alternatingSixThreeCTblLibCandidateRowIdentification
      |>.LocalCorrectedAlphaTwoBridge) ↔
      (alternatingSixThreeCTblLibCandidateRowIdentification
        |>.LocalCorrectedAlphaTwoBridgeAwayFromTrivial) :=
  alternatingSixThreeCTblLibCandidateRowIdentification
    |>.localCorrectedAlphaTwoBridge_iff_awayFromTrivial
      alternatingSixThreeCTblLibCandidateRowIdentification_hasTrivial

end InductiveMcKay
end McKayConjecture
