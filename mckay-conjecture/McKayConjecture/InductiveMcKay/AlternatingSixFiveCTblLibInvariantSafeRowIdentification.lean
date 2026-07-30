/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibParameterizedRowBridge
import McKayConjecture.InductiveMcKay.AlternatingSixFiveInnerInertia
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibInvariantSafeRowIdentification

/-!
# An invariant-safe five-local CTblLib position orientation

The arithmetic ordering of the project's twenty-four prime-to-five ambient
rows is not compatible with the audited CTblLib generator permutations.
This file records a different finite orientation compatible with two
immediately checkable semantic invariants:

* both audited permutations preserve the displayed character degree; and
* the positionwise central exponents agree with the project's powers of the
  distinguished primitive sixth root.

The choices within the remaining equal-degree, equal-central-scalar blocks
are only an orientation convention.  Consequently the equivalences below
are not asserted to be the true CTblLib row order.  The final section reduces
each ambient semantic bridge for this convention to an exact finite
`24 × 31` equality of already constructed character values.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveCTblLibInvariantSafeFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ### Finite invariant-safe position data -/

/-- The raw invariant-safe orientation of the twenty-four ambient
prime-to-five positions.  This is coordinate data and is not claimed to be
the true CTblLib row identification. -/
def alternatingSixFiveCTblLibInvariantSafeAmbientPosition :
    Fin 24 → AlternatingSixAmbientPPrimeRowIndex 5 :=
  ![⟨.row01, by decide⟩,
    ⟨.row16, by decide⟩,
    ⟨.row17, by decide⟩,
    ⟨.row20, by decide⟩,
    ⟨.row06, by decide⟩,
    ⟨.row07, by decide⟩,
    ⟨.row18, by decide⟩,
    ⟨.row19, by decide⟩,
    ⟨.row04, by decide⟩,
    ⟨.row02, by decide⟩,
    ⟨.row05, by decide⟩,
    ⟨.row03, by decide⟩,
    ⟨.row11, by decide⟩,
    ⟨.row10, by decide⟩,
    ⟨.row22, by decide⟩,
    ⟨.row21, by decide⟩,
    ⟨.row14, by decide⟩,
    ⟨.row12, by decide⟩,
    ⟨.row15, by decide⟩,
    ⟨.row13, by decide⟩,
    ⟨.atlasTwelvePowerTwo, by decide⟩,
    ⟨.atlasTwelvePowerOne, by decide⟩,
    ⟨.atlasTwelvePowerEleven, by decide⟩,
    ⟨.atlasTwelvePowerSeven, by decide⟩]

/-- The raw invariant-safe orientation visits every prime-to-five ambient
row exactly once. -/
theorem alternatingSixFiveCTblLibInvariantSafeAmbientPosition_bijective :
    Function.Bijective
      alternatingSixFiveCTblLibInvariantSafeAmbientPosition := by
  decide

/-- The invariant-safe ambient position orientation as an equivalence. -/
def alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv :
    Fin 24 ≃ AlternatingSixAmbientPPrimeRowIndex 5 :=
  Equiv.ofBijective
    alternatingSixFiveCTblLibInvariantSafeAmbientPosition
    alternatingSixFiveCTblLibInvariantSafeAmbientPosition_bijective

/-- The twelve audited free-orbit positions, in increasing position order. -/
def alternatingSixFiveCTblLibInvariantSafeOuterFreePositionEquiv :
    Fin 12 ≃ {i : Fin 24 // AlternatingSixFiveOuterFreeCTPosition i} :=
  Equiv.ofBijective
    ![⟨8, by decide⟩,
      ⟨9, by decide⟩,
      ⟨10, by decide⟩,
      ⟨11, by decide⟩,
      ⟨16, by decide⟩,
      ⟨17, by decide⟩,
      ⟨18, by decide⟩,
      ⟨19, by decide⟩,
      ⟨20, by decide⟩,
      ⟨21, by decide⟩,
      ⟨22, by decide⟩,
      ⟨23, by decide⟩]
    (by decide)

/-- Ambient rows carried by the audited free-orbit positions in the chosen
invariant-safe orientation. -/
def alternatingSixFiveCTblLibInvariantSafeOuterFreeAmbientRow :
    Fin 12 → AlternatingSixAmbientOrdinaryRow :=
  ![.row04, .row02, .row05, .row03,
    .row14, .row12, .row15, .row13,
    .atlasTwelvePowerTwo, .atlasTwelvePowerOne,
    .atlasTwelvePowerEleven, .atlasTwelvePowerSeven]

/-- Under the invariant-safe orientation, the audited free-orbit positions
are exactly the four rows `row02`--`row05`, the four rows
`row12`--`row15`, and the four ATLAS degree-twelve rows, in the displayed
orientation order. -/
theorem
    alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv_outerFree
    (i : Fin 12) :
    (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv
        (alternatingSixFiveCTblLibInvariantSafeOuterFreePositionEquiv i).1).1 =
      alternatingSixFiveCTblLibInvariantSafeOuterFreeAmbientRow i := by
  fin_cases i <;>
    rfl

/-- The project central exponent read at one invariant-safe five-local
position. -/
def alternatingSixFiveCTblLibInvariantSafeAmbientCentralExponent
    (i : Fin 24) : Fin 6 :=
  alternatingSixAmbientScalarPatternExponentModSix
    ((alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv i).1.scalarPattern)

/-- The invariant-safe position orientation has the audited ambient central
exponent at every position. -/
theorem
    alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv_centralExponent
    (i : Fin 24) :
    alternatingSixFiveCTblLibInvariantSafeAmbientCentralExponent i =
      alternatingSixCTblLibFivePPrimeActionData.ambientCentralExponent i := by
  fin_cases i <;>
    rfl

/-- The first audited finite generator preserves project character degree
under the invariant-safe orientation. -/
theorem
    alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv_alphaOne_dimension
    (i : Fin 24) :
    (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i)).1.dimension =
      (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv i).1.dimension := by
  fin_cases i <;>
    rfl

/-- The second audited finite generator preserves project character degree
under the invariant-safe orientation. -/
theorem
    alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv_alphaTwo_dimension
    (i : Fin 24) :
    (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)).1.dimension =
      (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv i).1.dimension := by
  fin_cases i <;>
    rfl

/-- Both audited outer generators invert the positionwise central exponent
under the invariant-safe orientation. -/
theorem
    alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv_generators_centralExponent
    (i : Fin 24) :
    (alternatingSixFiveCTblLibInvariantSafeAmbientCentralExponent
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i)).val =
        (6 -
          (alternatingSixFiveCTblLibInvariantSafeAmbientCentralExponent i).val) %
            6 ∧
      (alternatingSixFiveCTblLibInvariantSafeAmbientCentralExponent
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)).val =
        (6 -
          (alternatingSixFiveCTblLibInvariantSafeAmbientCentralExponent i).val) %
            6 := by
  fin_cases i <;>
    decide

/-! ### The induced local orientation -/

/-- Use the audited candidate and the existing central-block matching to
orient the local positions once the invariant-safe ambient orientation has
been chosen.  This remains coordinate data, not a CTblLib identity claim. -/
def alternatingSixFiveCTblLibInvariantSafeRowIdentification :
    AlternatingSixFiveCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv
  localPositionEquiv :=
    alternatingSixCTblLibFivePPrimeActionData.candidate.symm.trans
      (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv.trans
        alternatingSixAmbientFivePPrimeCentralBlockRowEquiv)

/-- Central exponent of a concrete five-normalizer row, read from its proved
central block in the same sixth-root convention as the ambient patterns. -/
def alternatingSixFiveConcreteNormalizerRowCentralExponent
    (r : AlternatingSixFiveConcreteNormalizerRow) : Fin 6 :=
  alternatingSixAmbientScalarPatternExponentModSix
    (alternatingSixFiveConcreteNormalizerCentralBlock r)

/-- Executable inverse vector for the audited five-local candidate. -/
theorem alternatingSixCTblLibFive_candidate_symm_apply
    (i : Fin 24) :
    alternatingSixCTblLibFivePPrimeActionData.candidate.symm i =
      ![0, 12, 13, 3, 14, 15, 4, 16, 19, 5, 18, 17,
        6, 20, 21, 1, 8, 9, 2, 10, 11, 7, 22, 23] i := by
  apply alternatingSixCTblLibFivePPrimeActionData.candidate.injective
  rw [alternatingSixCTblLibFivePPrimeActionData.candidate.apply_symm_apply]
  fin_cases i <;>
    rfl

/-- The induced local orientation has the audited local central exponent at
every position. -/
theorem
    alternatingSixFiveCTblLibInvariantSafeRowIdentification_localCentralExponent
    (i : Fin 24) :
    alternatingSixFiveConcreteNormalizerRowCentralExponent
        (alternatingSixFiveCTblLibInvariantSafeRowIdentification
          |>.localPositionEquiv i) =
      alternatingSixCTblLibFivePPrimeActionData.localCentralExponent i := by
  change
    alternatingSixAmbientScalarPatternExponentModSix
        (alternatingSixFiveConcreteNormalizerCentralBlock
          (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv
            (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv
              (alternatingSixCTblLibFivePPrimeActionData.candidate.symm i)))) =
      alternatingSixCTblLibFivePPrimeActionData.localCentralExponent i
  rw [
    alternatingSixAmbientFivePPrimeCentralBlockRowEquiv_preserves_centralBlock,
    alternatingSixCTblLibFive_candidate_symm_apply
  ]
  fin_cases i <;>
    rfl

/-- Transporting the audited candidate through the invariant-safe
orientation recovers the existing central-block row matching. -/
theorem alternatingSixFiveCTblLibInvariantSafeRowIdentification_candidate :
    (alternatingSixFiveCTblLibInvariantSafeRowIdentification
      |>.candidateAmbientLocalRowEquiv) =
      alternatingSixAmbientFivePPrimeCentralBlockRowEquiv := by
  apply Equiv.ext
  intro r
  simp [
    AlternatingSixFiveCTblLibRowIdentification.candidateAmbientLocalRowEquiv,
    alternatingSixFiveCTblLibInvariantSafeRowIdentification
  ]

/-! ### Exact finite class-value reduction of the ambient bridges -/

/-- For an arbitrary proposed five-local position equivalence, the first
ambient semantic bridge is exactly a finite equality on the 31 checked class
representatives. -/
theorem
    AlternatingSixFiveCTblLibRowIdentification.ambientAlphaOneBridge_iff_classValues
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    identification.AmbientCorrectedAlphaOneBridge T ↔
      ∀ (i : Fin 24) (j : Fin 31),
        (T.toFiniteCharacterTableCertificate.character
            (identification.ambientPositionEquiv
              (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i)).1).values
            (alternatingSixUniversalCoverClassRepresentative j) =
          (T.toFiniteCharacterTableCertificate.character
              (identification.ambientPositionEquiv i).1).values
            (alternatingSixUniversalCoverClassRepresentative
              (alternatingSixAlphaOneConjugacyClassPermutation.symm j)) := by
  constructor
  · intro h i j
    rw [← h i]
    simpa only [
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq
    ] using
      alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        T 5 (identification.ambientPositionEquiv i) j
  · intro h i
    apply Subtype.ext
    apply alternatingSixAmbientOrdinaryRow_eq_of_values_classRepresentative_eq T
    intro j
    rw [alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq]
    exact
      (alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        T 5 (identification.ambientPositionEquiv i) j).trans
          (h i j).symm

/-- For an arbitrary proposed five-local position equivalence, the second
ambient semantic bridge is exactly a finite equality on the 31 checked class
representatives. -/
theorem
    AlternatingSixFiveCTblLibRowIdentification.ambientAlphaTwoBridge_iff_classValues
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    identification.AmbientCorrectedAlphaTwoBridge T ↔
      ∀ (i : Fin 24) (j : Fin 31),
        (T.toFiniteCharacterTableCertificate.character
            (identification.ambientPositionEquiv
              (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)).1).values
            (alternatingSixUniversalCoverClassRepresentative j) =
          (T.toFiniteCharacterTableCertificate.character
              (identification.ambientPositionEquiv i).1).values
            (alternatingSixUniversalCoverClassRepresentative
              (alternatingSixAlphaTwoConjugacyClassPermutation.symm j)) := by
  constructor
  · intro h i j
    rw [← h i]
    simpa only [
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq
    ] using
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        T 5 (identification.ambientPositionEquiv i) j
  · intro h i
    apply Subtype.ext
    apply alternatingSixAmbientOrdinaryRow_eq_of_values_classRepresentative_eq T
    intro j
    rw [alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq]
    exact
      (alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        T 5 (identification.ambientPositionEquiv i) j).trans
          (h i j).symm

end InductiveMcKay
end McKayConjecture
