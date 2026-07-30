/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import McKayConjecture.Character.InverseConjugate
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibSemanticTrivialRow
import McKayConjecture.InductiveMcKay.AlternatingSixThreeDisplayedRowBridge

/-!
# Invariant-safe ambient CT positions for the three-local `A₆` table

The project's arithmetic order of its twelve `3'`-degree rows is not the
stored CTblLib order.  This file records the CTblLib degree vector and uses
degree together with the already audited central exponent to isolate the
only possible project rows at each CT position.

The resulting blocks are two singletons and five pairs.  An alignment
reproduced from the presentation-to-ATLAS comparison is also recorded; the
only ambiguity among the quotient-fusion-compatible CTblLib alignments on
these twelve rows is the order of `row24` and `row25`.  Both variants satisfy
the invariant checks below.

These are finite position constraints, not yet semantic equalities between
CTblLib characters and constructed Lean characters.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeAmbientPositionBlocksFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

private theorem alternatingSixAmbientCanonicalCentralGenerator_eq_schurCoordinate :
    alternatingSixAmbientCanonicalCentralGenerator =
      alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2) := by
  rw [alternatingSixAmbientCanonicalCentralGenerator,
    alternatingSixAmbientCanonicalGeneratorA]
  change
    (alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates 0)) ^ 2 =
      alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2)
  rw [← map_pow]
  congr 1

private theorem
    alternatingSixSchurAlphaOneAutomorphism_symm_centralGeneratorCoordinate :
    alternatingSixSchurAlphaOneAutomorphism.symm
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2) =
      (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2)⁻¹ := by
  apply alternatingSixSchurAlphaOneAutomorphism.injective
  rw [alternatingSixSchurAlphaOneAutomorphism.apply_symm_apply, map_inv]
  change
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2 =
      (alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2))⁻¹
  rw [alternatingSixSchurAlphaOneEndomorphism_generator]
  decide

private theorem
    alternatingSixSchurAlphaTwoAutomorphism_symm_centralGeneratorCoordinate :
    alternatingSixSchurAlphaTwoAutomorphism.symm
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2) =
      (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2)⁻¹ := by
  apply alternatingSixSchurAlphaTwoAutomorphism.injective
  rw [alternatingSixSchurAlphaTwoAutomorphism.apply_symm_apply, map_inv]
  change
    alternatingSixSchurAuditedPresentationGeneratorCoordinates 2 =
      (alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAuditedPresentationGeneratorCoordinates 2))⁻¹
  rw [alternatingSixSchurAlphaTwoEndomorphism_generator]
  decide

private theorem
    alternatingSixUniversalCoverTransportedAlphaOne_symm_centralGenerator :
    alternatingSixUniversalCoverTransportedAlphaOne.symm
        alternatingSixAmbientCanonicalCentralGenerator =
      alternatingSixAmbientCanonicalCentralGenerator⁻¹ := by
  rw [alternatingSixAmbientCanonicalCentralGenerator_eq_schurCoordinate]
  simpa [
    alternatingSixUniversalCoverTransportedAlphaOne,
    alternatingSixUniversalCoverAutomorphismOfSchur,
    MulAut.congr
  ] using congrArg alternatingSixSchurCoordinatesEquivUniversalCover
    alternatingSixSchurAlphaOneAutomorphism_symm_centralGeneratorCoordinate

private theorem
    alternatingSixUniversalCoverTransportedAlphaTwo_symm_centralGenerator :
    alternatingSixUniversalCoverTransportedAlphaTwo.symm
        alternatingSixAmbientCanonicalCentralGenerator =
      alternatingSixAmbientCanonicalCentralGenerator⁻¹ := by
  rw [alternatingSixAmbientCanonicalCentralGenerator_eq_schurCoordinate]
  simpa [
    alternatingSixUniversalCoverTransportedAlphaTwo,
    alternatingSixUniversalCoverAutomorphismOfSchur,
    MulAut.congr
  ] using congrArg alternatingSixSchurCoordinatesEquivUniversalCover
    alternatingSixSchurAlphaTwoAutomorphism_symm_centralGeneratorCoordinate

/-- Degrees of CTblLib rows
`[1,2,3,4,5,7,8,9,10,11,12,13]` of `6.A6`. -/
def alternatingSixCTblLibThreeAmbientDegree : Fin 12 → ℕ :=
  ![1, 5, 5, 8, 8, 10, 4, 4, 8, 8, 10, 10]

/-- The degree/central-exponent signature of an audited ambient CT
position. -/
def alternatingSixCTblLibThreeAmbientSignature
    (i : Fin 12) : ℕ × ℕ :=
  (alternatingSixCTblLibThreeAmbientDegree i,
    (alternatingSixCTblLibThreePPrimeActionData.ambientCentralExponent i).val)

/-- The degree/central-exponent signature advertised by a constructed
ambient row. -/
def alternatingSixThreeConstructedAmbientSignature
    (r : AlternatingSixAmbientPPrimeRowIndex 3) : ℕ × ℕ :=
  (r.1.dimension, r.1.scalarPattern.exponent 0 / 20)

/-- A proposed ambient CT-position equivalence is invariant-safe when it
preserves the audited degree and central-exponent signatures. -/
def AlternatingSixThreeAmbientPositionSignatureCompatible
    (e : Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 3) : Prop :=
  ∀ i,
    alternatingSixThreeConstructedAmbientSignature (e i) =
      alternatingSixCTblLibThreeAmbientSignature i

/-- All constructed ambient rows whose elementary signature is compatible
with a given CT position. -/
def alternatingSixThreeExpectedAmbientRowsAtCTPosition
    (i : Fin 12) : Finset AlternatingSixAmbientOrdinaryRow :=
  Finset.univ.filter fun r ↦
    (r.dimension, r.scalarPattern.exponent 0 / 20) =
      alternatingSixCTblLibThreeAmbientSignature i

/-- The invariant-safe CT-position blocks: the trivial and degree-ten
central-trivial positions are singletons, and the other ten positions form
five equal-signature pairs. -/
theorem alternatingSixThreeExpectedAmbientRowsAtCTPosition_eq
    (i : Fin 12) :
    alternatingSixThreeExpectedAmbientRowsAtCTPosition i =
      ![{.row01},
        {.row08, .row09},
        {.row08, .row09},
        {.row16, .row17},
        {.row16, .row17},
        {.row23},
        {.row06, .row07},
        {.row06, .row07},
        {.row18, .row19},
        {.row18, .row19},
        {.row24, .row25},
        {.row24, .row25}] i := by
  fin_cases i <;>
    decide

/-- Signature compatibility places every proposed image in the exact finite
block displayed above. -/
theorem alternatingSixThreeAmbientPosition_mem_expected
    (e : Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 3)
    (h : AlternatingSixThreeAmbientPositionSignatureCompatible e)
    (i : Fin 12) :
    (e i).1 ∈ alternatingSixThreeExpectedAmbientRowsAtCTPosition i := by
  rw [alternatingSixThreeExpectedAmbientRowsAtCTPosition,
    Finset.mem_filter]
  exact ⟨Finset.mem_univ _, h i⟩

/-- A presentation/ATLAS-aligned ambient CT-position equivalence.  The
last two images choose one of the two fusion-compatible orientations. -/
def alternatingSixThreeAtlasAlignedAmbientPositionEquiv :
    Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 3 :=
  Equiv.ofBijective
    ![⟨.row01, by decide⟩,
      ⟨.row08, by decide⟩,
      ⟨.row09, by decide⟩,
      ⟨.row16, by decide⟩,
      ⟨.row17, by decide⟩,
      ⟨.row23, by decide⟩,
      ⟨.row07, by decide⟩,
      ⟨.row06, by decide⟩,
      ⟨.row18, by decide⟩,
      ⟨.row19, by decide⟩,
      ⟨.row25, by decide⟩,
      ⟨.row24, by decide⟩]
    (by decide)

/-- The alternate quotient-fusion-compatible orientation differs only by
interchanging `row24` and `row25`. -/
def alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate :
    Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 3 :=
  Equiv.ofBijective
    ![⟨.row01, by decide⟩,
      ⟨.row08, by decide⟩,
      ⟨.row09, by decide⟩,
      ⟨.row16, by decide⟩,
      ⟨.row17, by decide⟩,
      ⟨.row23, by decide⟩,
      ⟨.row07, by decide⟩,
      ⟨.row06, by decide⟩,
      ⟨.row18, by decide⟩,
      ⟨.row19, by decide⟩,
      ⟨.row24, by decide⟩,
      ⟨.row25, by decide⟩]
    (by decide)

theorem alternatingSixThreeAtlasAlignedAmbientPositionEquiv_signatureCompatible :
    AlternatingSixThreeAmbientPositionSignatureCompatible
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv := by
  intro i
  fin_cases i <;>
    decide

theorem
    alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate_signatureCompatible :
    AlternatingSixThreeAmbientPositionSignatureCompatible
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate := by
  intro i
  fin_cases i <;>
    decide

/-- Signature compatibility already identifies zero-based CT position five
with the unique constructed degree-ten row having trivial central scalar. -/
theorem alternatingSixThreeAmbientPosition_five_eq_row23_of_signatureCompatible
    (e : Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 3)
    (h : AlternatingSixThreeAmbientPositionSignatureCompatible e) :
    e 5 =
      (⟨.row23, by decide⟩ :
        AlternatingSixAmbientPPrimeRowIndex 3) := by
  apply Subtype.ext
  have hmem :=
    alternatingSixThreeAmbientPosition_mem_expected e h (5 : Fin 12)
  rw [alternatingSixThreeExpectedAmbientRowsAtCTPosition_eq] at hmem
  simpa using hmem

/-- Genuine ambient row actions preserve the recorded representation
dimension. -/
theorem alternatingSixThreeAmbientPPrimeRowPermutation_dimension
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    (alternatingSixAmbientPPrimeRowPermutation T 3 a r).1.dimension =
      r.1.dimension := by
  calc
    (alternatingSixAmbientPPrimeRowPermutation T 3 a r).1.dimension =
        (alternatingSixAmbientPPrimeCharacterEquiv T 3
          (alternatingSixAmbientPPrimeRowPermutation T 3 a r)).1.degree := by
      rw [alternatingSixAmbientPPrimeCharacterEquiv_degree]
    _ =
        (a • alternatingSixAmbientPPrimeCharacterEquiv T 3 r).1.degree := by
      rw [alternatingSixAmbientPPrimeRowPermutation_character]
    _ =
        (alternatingSixAmbientPPrimeCharacterEquiv T 3 r).1.degree := by
      rfl
    _ = r.1.dimension := by
      rw [alternatingSixAmbientPPrimeCharacterEquiv_degree]

/-- Any ambient automorphism that inverts the canonical central generator
fixes the unique degree-ten row with trivial central scalar. -/
theorem alternatingSixThreeAmbientRow23_fixed_of_symm_centralGenerator_eq_inv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (ha :
      a.symm alternatingSixAmbientCanonicalCentralGenerator =
        alternatingSixAmbientCanonicalCentralGenerator⁻¹) :
    alternatingSixAmbientPPrimeRowPermutation T 3 a
        (⟨.row23, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row23, by decide⟩ := by
  let r : AlternatingSixAmbientPPrimeRowIndex 3 :=
    ⟨.row23, by decide⟩
  let s : AlternatingSixAmbientPPrimeRowIndex 3 :=
    alternatingSixAmbientPPrimeRowPermutation T 3 a r
  have hsCharacter :
      alternatingSixAmbientPPrimeCharacterEquiv T 3 s =
        a • alternatingSixAmbientPPrimeCharacterEquiv T 3 r := by
    dsimp only [s]
    exact alternatingSixAmbientPPrimeRowPermutation_character T 3 a r
  have hdegree : s.1.dimension = 10 := by
    dsimp only [s]
    simpa only [r, AlternatingSixAmbientOrdinaryRow.dimension] using
      alternatingSixThreeAmbientPPrimeRowPermutation_dimension T a r
  have hsourceCentral :=
    alternatingSixAmbientPPrimeCharacterEquiv_values_centralGenerator T 3 r
  rw [alternatingSixAmbientPPrimeCharacterEquiv_degree] at hsourceCentral
  have hsourceInverse :
      (alternatingSixAmbientPPrimeCharacterEquiv T 3 r).1.values
          alternatingSixAmbientCanonicalCentralGenerator⁻¹ =
        (10 : ℂ) := by
    rw [IrreducibleCharacter.value_inv_eq_conj, hsourceCentral]
    norm_num [
      r,
      AlternatingSixAmbientOrdinaryRow.dimension,
      AlternatingSixAmbientOrdinaryRow.scalarPattern,
      AlternatingSixAmbientScalarPattern.exponent
    ]
    exact Complex.conj_natCast 10
  have htargetValue :
      (alternatingSixAmbientPPrimeCharacterEquiv T 3 s).1.values
          alternatingSixAmbientCanonicalCentralGenerator =
        (10 : ℂ) := by
    have hvalues :=
      congrArg
        (fun χ : PPrimeIrreducibleCharacter
            AlternatingSixUniversalCover 3 ↦
          χ.1.values alternatingSixAmbientCanonicalCentralGenerator)
        hsCharacter
    change
      (alternatingSixAmbientPPrimeCharacterEquiv T 3 s).1.values
          alternatingSixAmbientCanonicalCentralGenerator =
        (alternatingSixAmbientPPrimeCharacterEquiv T 3 r).1.values
          (a.symm alternatingSixAmbientCanonicalCentralGenerator)
      at hvalues
    rw [ha, hsourceInverse] at hvalues
    exact hvalues
  have htargetCentral :=
    alternatingSixAmbientPPrimeCharacterEquiv_values_centralGenerator T 3 s
  rw [alternatingSixAmbientPPrimeCharacterEquiv_degree, hdegree] at htargetCentral
  have hfirstScalar :
      alternatingSixComplexCyclotomicRoot ^
          s.1.scalarPattern.exponent 0 =
        1 := by
    apply mul_left_cancel₀ (by norm_num : (10 : ℂ) ≠ 0)
    calc
      (10 : ℂ) *
            alternatingSixComplexCyclotomicRoot ^
              s.1.scalarPattern.exponent 0 =
          (alternatingSixAmbientPPrimeCharacterEquiv T 3 s).1.values
            alternatingSixAmbientCanonicalCentralGenerator := by
        simpa using htargetCentral.symm
      _ = 10 := htargetValue
      _ = 10 * 1 := by norm_num
  have hpattern :
      s.1.scalarPattern = .trivial := by
    apply AlternatingSixAmbientScalarPattern.firstScalar_injective
    simpa [AlternatingSixAmbientScalarPattern.exponent] using hfirstScalar
  apply Subtype.ext
  change s.1 = .row23
  cases hs : s.1 <;>
    simp_all [
      AlternatingSixAmbientOrdinaryRow.dimension,
      AlternatingSixAmbientOrdinaryRow.scalarPattern
    ]

@[simp]
theorem alternatingSixThreeAmbientAlphaOneRow23_fixed
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation T 3
        (⟨.row23, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row23, by decide⟩ := by
  exact
    alternatingSixThreeAmbientRow23_fixed_of_symm_centralGenerator_eq_inv
      T alternatingSixUniversalCoverTransportedAlphaOne
      alternatingSixUniversalCoverTransportedAlphaOne_symm_centralGenerator

@[simp]
theorem alternatingSixThreeAmbientAlphaTwoRow23_fixed
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 3
        (⟨.row23, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row23, by decide⟩ := by
  exact
    alternatingSixThreeAmbientRow23_fixed_of_symm_centralGenerator_eq_inv
      T alternatingSixUniversalCoverTransportedAlphaTwo
      alternatingSixUniversalCoverTransportedAlphaTwo_symm_centralGenerator

@[simp]
theorem alternatingSixThreeAmbientCorrectedAlphaOneRow23_fixed
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (⟨.row23, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row23, by decide⟩ := by
  rw [alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq]
  exact alternatingSixThreeAmbientAlphaOneRow23_fixed T

@[simp]
theorem alternatingSixThreeAmbientCorrectedAlphaTwoRow23_fixed
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (⟨.row23, by decide⟩ :
          AlternatingSixAmbientPPrimeRowIndex 3) =
      ⟨.row23, by decide⟩ := by
  rw [alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq]
  exact alternatingSixThreeAmbientAlphaTwoRow23_fixed T

namespace AlternatingSixThreeCTblLibRowIdentification

variable
  (identification : AlternatingSixThreeCTblLibRowIdentification)

/-- The proposed ambient CT identification sends the second singleton
signature block, zero-based CT position five, to the constructed row
`row23`. -/
def HasSemanticAmbientRow23Position : Prop :=
  identification.ambientPositionEquiv 5 =
    (⟨.row23, by decide⟩ :
      AlternatingSixAmbientPPrimeRowIndex 3)

/-- Signature compatibility supplies the semantic row-23 singleton
position automatically. -/
theorem hasSemanticAmbientRow23Position_of_signatureCompatible
    (h :
      AlternatingSixThreeAmbientPositionSignatureCompatible
        identification.ambientPositionEquiv) :
    identification.HasSemanticAmbientRow23Position :=
  alternatingSixThreeAmbientPosition_five_eq_row23_of_signatureCompatible
    identification.ambientPositionEquiv h

/-- The first corrected ambient bridge holds at zero-based CT position five
for every signature-safe identification. -/
theorem ambientCorrectedAlphaOneBridge_five
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.HasSemanticAmbientRow23Position) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (identification.ambientPositionEquiv 5) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne 5) := by
  calc
    _ =
        alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 3)
          (⟨.row23, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 3) :=
      congrArg
        (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 3))
        h
    _ = ⟨.row23, by decide⟩ :=
      alternatingSixThreeAmbientCorrectedAlphaOneRow23_fixed T
    _ = identification.ambientPositionEquiv 5 := h.symm
    _ =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne 5) := by
      rfl

/-- The second corrected ambient bridge holds at zero-based CT position five
for every signature-safe identification. -/
theorem ambientCorrectedAlphaTwoBridge_five
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : identification.HasSemanticAmbientRow23Position) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (identification.ambientPositionEquiv 5) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo 5) := by
  calc
    _ =
        alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
          (alternatingSixUniversalCoverSylow 3)
          (⟨.row23, by decide⟩ :
            AlternatingSixAmbientPPrimeRowIndex 3) :=
      congrArg
        (alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
          (alternatingSixUniversalCoverSylow 3))
        h
    _ = ⟨.row23, by decide⟩ :=
      alternatingSixThreeAmbientCorrectedAlphaTwoRow23_fixed T
    _ = identification.ambientPositionEquiv 5 := h.symm
    _ =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo 5) := by
      rfl

/-- The exact first ambient bridge obligation left after removing the two
singleton signature positions. -/
def AmbientCorrectedAlphaOneBridgeAwayFromSingletons
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 12, i ≠ 0 → i ≠ 5 →
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (identification.ambientPositionEquiv i) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i)

/-- The exact second ambient bridge obligation left after removing the two
singleton signature positions. -/
def AmbientCorrectedAlphaTwoBridgeAwayFromSingletons
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    Prop :=
  ∀ i : Fin 12, i ≠ 0 → i ≠ 5 →
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
        (alternatingSixUniversalCoverSylow 3)
        (identification.ambientPositionEquiv i) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i)

/-- Once the two singleton-position equalities are supplied, the first full
ambient bridge is equivalent to the ten remaining position equalities. -/
theorem ambientCorrectedAlphaOneBridge_iff_awayFromSingletons
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hzero :
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 3)
          (identification.ambientPositionEquiv 0) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne 0))
    (hfive :
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 3)
          (identification.ambientPositionEquiv 5) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne 5)) :
    identification.AmbientCorrectedAlphaOneBridge T ↔
      identification.AmbientCorrectedAlphaOneBridgeAwayFromSingletons T := by
  constructor
  · intro h i _ _
    exact h i
  · intro h i
    by_cases hi0 : i = 0
    · subst i
      exact hzero
    by_cases hi5 : i = 5
    · subst i
      exact hfive
    exact h i hi0 hi5

/-- Once the two singleton-position equalities are supplied, the second full
ambient bridge is equivalent to the ten remaining position equalities. -/
theorem ambientCorrectedAlphaTwoBridge_iff_awayFromSingletons
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hzero :
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
          (alternatingSixUniversalCoverSylow 3)
          (identification.ambientPositionEquiv 0) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo 0))
    (hfive :
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T
          (alternatingSixUniversalCoverSylow 3)
          (identification.ambientPositionEquiv 5) =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo 5)) :
    identification.AmbientCorrectedAlphaTwoBridge T ↔
      identification.AmbientCorrectedAlphaTwoBridgeAwayFromSingletons T := by
  constructor
  · intro h i _ _
    exact h i
  · intro h i
    by_cases hi0 : i = 0
    · subst i
      exact hzero
    by_cases hi5 : i = 5
    · subst i
      exact hfive
    exact h i hi0 hi5

/-- For the completed table, a semantically correct trivial position and a
signature-safe ambient identification reduce the first bridge exactly to
the ten non-singleton positions. -/
theorem ambientCorrectedAlphaOneBridge_iff_awayFromSingletons_of_signatures
    (htrivial : identification.HasSemanticTrivialPosition)
    (hsignature :
      AlternatingSixThreeAmbientPositionSignatureCompatible
        identification.ambientPositionEquiv) :
    identification.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate ↔
      identification.AmbientCorrectedAlphaOneBridgeAwayFromSingletons
        alternatingSixAmbientOrdinaryCharacterTableCertificate :=
  identification.ambientCorrectedAlphaOneBridge_iff_awayFromSingletons
    alternatingSixAmbientOrdinaryCharacterTableCertificate
    (identification.ambientCorrectedAlphaOneBridge_zero htrivial)
    (identification.ambientCorrectedAlphaOneBridge_five
      alternatingSixAmbientOrdinaryCharacterTableCertificate
      (identification.hasSemanticAmbientRow23Position_of_signatureCompatible
        hsignature))

/-- For the completed table, a semantically correct trivial position and a
signature-safe ambient identification reduce the second bridge exactly to
the ten non-singleton positions. -/
theorem ambientCorrectedAlphaTwoBridge_iff_awayFromSingletons_of_signatures
    (htrivial : identification.HasSemanticTrivialPosition)
    (hsignature :
      AlternatingSixThreeAmbientPositionSignatureCompatible
        identification.ambientPositionEquiv) :
    identification.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate ↔
      identification.AmbientCorrectedAlphaTwoBridgeAwayFromSingletons
        alternatingSixAmbientOrdinaryCharacterTableCertificate :=
  identification.ambientCorrectedAlphaTwoBridge_iff_awayFromSingletons
    alternatingSixAmbientOrdinaryCharacterTableCertificate
    (identification.ambientCorrectedAlphaTwoBridge_zero htrivial)
    (identification.ambientCorrectedAlphaTwoBridge_five
      alternatingSixAmbientOrdinaryCharacterTableCertificate
      (identification.hasSemanticAmbientRow23Position_of_signatureCompatible
        hsignature))

end AlternatingSixThreeCTblLibRowIdentification

/-- A concrete parameterized CT identification using the reproduced
ATLAS-aligned ambient order and the project's existing local order.  This is
identification data, not a claim that the local order is semantically the
CTblLib order. -/
def alternatingSixThreeAtlasAlignedCTblLibRowIdentification :
    AlternatingSixThreeCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixThreeAtlasAlignedAmbientPositionEquiv
  localPositionEquiv :=
    alternatingSixThreeConcreteNormalizerRowIndexEquiv

/-- The alternate concrete identification changes only the unresolved
ambient `row24`/`row25` orientation. -/
def alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate :
    AlternatingSixThreeCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate
  localPositionEquiv :=
    alternatingSixThreeConcreteNormalizerRowIndexEquiv

theorem alternatingSixThreeAtlasAlignedCTblLibRowIdentification_hasTrivial :
    alternatingSixThreeAtlasAlignedCTblLibRowIdentification
      |>.HasSemanticTrivialPosition := by
  constructor <;>
    rfl

theorem
    alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate_hasTrivial :
    alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
      |>.HasSemanticTrivialPosition := by
  constructor <;>
    rfl

/-- For the first concrete ATLAS-aligned candidate, the first ambient
semantic bridge is now exactly the ten non-singleton position equalities. -/
theorem alternatingSixThreeAtlasAligned_ambientAlphaOneBridge_iff_remaining :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.AmbientCorrectedAlphaOneBridgeAwayFromSingletons
          alternatingSixAmbientOrdinaryCharacterTableCertificate) :=
  alternatingSixThreeAtlasAlignedCTblLibRowIdentification
    |>.ambientCorrectedAlphaOneBridge_iff_awayFromSingletons_of_signatures
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification_hasTrivial
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv_signatureCompatible

/-- For the first concrete ATLAS-aligned candidate, the second ambient
semantic bridge is now exactly the ten non-singleton position equalities. -/
theorem alternatingSixThreeAtlasAligned_ambientAlphaTwoBridge_iff_remaining :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentification
        |>.AmbientCorrectedAlphaTwoBridgeAwayFromSingletons
          alternatingSixAmbientOrdinaryCharacterTableCertificate) :=
  alternatingSixThreeAtlasAlignedCTblLibRowIdentification
    |>.ambientCorrectedAlphaTwoBridge_iff_awayFromSingletons_of_signatures
      alternatingSixThreeAtlasAlignedCTblLibRowIdentification_hasTrivial
      alternatingSixThreeAtlasAlignedAmbientPositionEquiv_signatureCompatible

/-- The same ten-position reduction holds for the alternate unresolved
`row24`/`row25` orientation and the first generator. -/
theorem
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaOneBridge_iff_remaining :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
      |>.AmbientCorrectedAlphaOneBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.AmbientCorrectedAlphaOneBridgeAwayFromSingletons
          alternatingSixAmbientOrdinaryCharacterTableCertificate) :=
  alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
    |>.ambientCorrectedAlphaOneBridge_iff_awayFromSingletons_of_signatures
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate_hasTrivial
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate_signatureCompatible

/-- The same ten-position reduction holds for the alternate unresolved
`row24`/`row25` orientation and the second generator. -/
theorem
    alternatingSixThreeAtlasAlignedAlternate_ambientAlphaTwoBridge_iff_remaining :
    (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
      |>.AmbientCorrectedAlphaTwoBridge
        alternatingSixAmbientOrdinaryCharacterTableCertificate) ↔
      (alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
        |>.AmbientCorrectedAlphaTwoBridgeAwayFromSingletons
          alternatingSixAmbientOrdinaryCharacterTableCertificate) :=
  alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate
    |>.ambientCorrectedAlphaTwoBridge_iff_awayFromSingletons_of_signatures
      alternatingSixThreeAtlasAlignedCTblLibRowIdentificationAlternate_hasTrivial
      alternatingSixThreeAtlasAlignedAmbientPositionEquivAlternate_signatureCompatible

/-- In particular, the old arithmetic display order cannot be the semantic
CTblLib position identification for the first ambient generator: at CT
position nine it would send constructed degree eight to degree ten. -/
theorem alternatingSixThreeRecorded_not_ambientCorrectedAlphaOneBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    ¬ (alternatingSixThreeRecordedCTblLibRowIdentification
        |>.AmbientCorrectedAlphaOneBridge T) := by
  intro h
  let r :=
    alternatingSixThreeRecordedCTblLibRowIdentification
      |>.ambientPositionEquiv (8 : Fin 12)
  have hdegree :=
    alternatingSixThreeAmbientPPrimeRowPermutation_dimension T
      (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 3) :
          MulAut AlternatingSixUniversalCover)
      r
  have hrow :
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 3) r =
        alternatingSixThreeRecordedCTblLibRowIdentification.ambientPositionEquiv
            (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne
              (8 : Fin 12)) :=
    h 8
  have hdegree' :
      (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T
          (alternatingSixUniversalCoverSylow 3) r).1.dimension =
        r.1.dimension :=
    hdegree
  rw [hrow] at hdegree'
  have hrDegree : r.1.dimension = 8 := by
    rfl
  have htargetDegree :
      (alternatingSixThreeRecordedCTblLibRowIdentification.ambientPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne
          (8 : Fin 12))).1.dimension = 10 := by
    rfl
  omega

end InductiveMcKay
end McKayConjecture
