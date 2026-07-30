/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAutomorphismClassValues
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibParameterizedRowBridge

/-!
# An invariant-safe two-local CTblLib position orientation

The arithmetic ordering of the project's twelve odd-dimensional ambient
rows is not compatible with the audited CTblLib generator permutations.
This file records a different finite orientation which is compatible with
the two immediately checkable semantic invariants:

* both audited permutations preserve the displayed character degree; and
* the positionwise central exponents agree with the project's powers of the
  distinguished primitive sixth root.

The choices inside equal-degree, equal-central-scalar pairs are only an
orientation convention.  Consequently the equivalences below are not
asserted to be the true CTblLib row order.  The final section reduces each
ambient semantic bridge for this convention to an exact finite
`12 × 31` equality of already constructed character values.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoCTblLibInvariantSafeFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-! ### Finite invariant-safe position data -/

/-- Express the first central scalar pattern as a power of
`ζ₁₂₀ ^ 20`, hence as an exponent modulo six. -/
def alternatingSixAmbientScalarPatternExponentModSix :
    AlternatingSixAmbientScalarPattern → Fin 6
  | .trivial => 0
  | .orderThreePositive => 4
  | .orderThreeNegative => 2
  | .orderTwo => 3
  | .orderSixPositive => 1
  | .orderSixNegative => 5

/-- The finite exponent really encodes the first advertised central
scalar, with no choice of a new complex root. -/
theorem alternatingSixAmbientScalarPattern_firstScalar_eq_modSix
    (pattern : AlternatingSixAmbientScalarPattern) :
    alternatingSixComplexCyclotomicRoot ^ pattern.exponent 0 =
      (alternatingSixComplexCyclotomicRoot ^ 20) ^
        (alternatingSixAmbientScalarPatternExponentModSix pattern).val := by
  cases pattern <;>
    simp [
      AlternatingSixAmbientScalarPattern.exponent,
      alternatingSixAmbientScalarPatternExponentModSix,
      ← pow_mul
    ]

/-- A position orientation matching the audited degree and central-scalar
blocks.

The order chosen inside the pairs `row08/row09`, `row02/row03`,
`row04/row05`, `row21/row22`, and `row30/row31` is conventional.  This
definition therefore makes no claim about CTblLib row identity. -/
def alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv :
    Fin 12 ≃ AlternatingSixAmbientPPrimeRowIndex 2 :=
  Equiv.ofBijective
    ![⟨.row01, by decide⟩,
      ⟨.row08, by decide⟩,
      ⟨.row09, by decide⟩,
      ⟨.row20, by decide⟩,
      ⟨.row04, by decide⟩,
      ⟨.row02, by decide⟩,
      ⟨.row05, by decide⟩,
      ⟨.row03, by decide⟩,
      ⟨.row22, by decide⟩,
      ⟨.row21, by decide⟩,
      ⟨.row31, by decide⟩,
      ⟨.row30, by decide⟩]
    (by decide)

/-- The project central exponent read at one invariant-safe position. -/
def alternatingSixTwoCTblLibInvariantSafeAmbientCentralExponent
    (i : Fin 12) : Fin 6 :=
  alternatingSixAmbientScalarPatternExponentModSix
    ((alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv i).1.scalarPattern)

/-- The invariant-safe position orientation has the audited ambient
central exponent at every position. -/
theorem
    alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv_centralExponent
    (i : Fin 12) :
    alternatingSixTwoCTblLibInvariantSafeAmbientCentralExponent i =
      alternatingSixCTblLibTwoPPrimeActionData.ambientCentralExponent i := by
  fin_cases i <;>
    rfl

/-- The first audited finite generator preserves project character degree
under the invariant-safe orientation. -/
theorem
    alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv_alphaOne_dimension
    (i : Fin 12) :
    (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaOne i)).1.dimension =
      (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv i).1.dimension := by
  fin_cases i <;>
    rfl

/-- The second audited finite generator preserves project character degree
under the invariant-safe orientation. -/
theorem
    alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv_alphaTwo_dimension
    (i : Fin 12) :
    (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaTwo i)).1.dimension =
      (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv i).1.dimension := by
  fin_cases i <;>
    rfl

/-- Both audited outer generators invert the positionwise central
exponent under the invariant-safe orientation. -/
theorem
    alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv_generators_centralExponent
    (i : Fin 12) :
    (alternatingSixTwoCTblLibInvariantSafeAmbientCentralExponent
        (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaOne i)).val =
        (6 -
          (alternatingSixTwoCTblLibInvariantSafeAmbientCentralExponent i).val) %
            6 ∧
      (alternatingSixTwoCTblLibInvariantSafeAmbientCentralExponent
        (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaTwo i)).val =
        (6 -
          (alternatingSixTwoCTblLibInvariantSafeAmbientCentralExponent i).val) %
            6 := by
  fin_cases i <;>
    decide

/-- Use the audited candidate and the existing central-block matching to
orient the local positions once the invariant-safe ambient orientation has
been chosen.  This is again coordinate data, not a CTblLib identity claim. -/
def alternatingSixTwoCTblLibInvariantSafeRowIdentification :
    AlternatingSixTwoCTblLibRowIdentification where
  ambientPositionEquiv :=
    alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
  localPositionEquiv :=
    alternatingSixCTblLibTwoPPrimeActionData.candidate.symm.trans
      (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv.trans
        alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow)

/-- Central exponent carried by the cyclic-three coordinate of a concrete
normalizer row, in the same sixth-root convention as the ambient patterns. -/
def alternatingSixTwoConcreteNormalizerRowCentralExponent
    (r : AlternatingSixTwoConcreteNormalizerRow) : Fin 6 :=
  ![0, 4, 2] r.1

/-- Executable inverse vector for the audited two-local candidate. -/
theorem alternatingSixCTblLibTwo_candidate_symm_apply
    (i : Fin 12) :
    alternatingSixCTblLibTwoPPrimeActionData.candidate.symm i =
      ![0, 1, 2, 3, 7, 4, 5, 6, 9, 8, 11, 10] i := by
  apply alternatingSixCTblLibTwoPPrimeActionData.candidate.injective
  rw [alternatingSixCTblLibTwoPPrimeActionData.candidate.apply_symm_apply]
  fin_cases i <;>
    rfl

/-- The invariant-safe local orientation has the audited local central
exponent at every position. -/
theorem
    alternatingSixTwoCTblLibInvariantSafeRowIdentification_localCentralExponent
    (i : Fin 12) :
    alternatingSixTwoConcreteNormalizerRowCentralExponent
        (alternatingSixTwoCTblLibInvariantSafeRowIdentification
          |>.localPositionEquiv i) =
      alternatingSixCTblLibTwoPPrimeActionData.localCentralExponent i := by
  change
    alternatingSixTwoConcreteNormalizerRowCentralExponent
        (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
          (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
            (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm i))) =
      alternatingSixCTblLibTwoPPrimeActionData.localCentralExponent i
  rw [alternatingSixCTblLibTwo_candidate_symm_apply]
  fin_cases i <;>
    rfl

/-- Transporting the audited candidate through the invariant-safe
orientation still recovers the existing central-block row matching. -/
theorem alternatingSixTwoCTblLibInvariantSafeRowIdentification_candidate :
    (alternatingSixTwoCTblLibInvariantSafeRowIdentification
      |>.candidateAmbientLocalRowEquiv) =
      alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow := by
  apply Equiv.ext
  intro r
  simp [
    AlternatingSixTwoCTblLibRowIdentification.candidateAmbientLocalRowEquiv,
    alternatingSixTwoCTblLibInvariantSafeRowIdentification
  ]

/-! ### Exact finite class-value reduction of the ambient bridges -/

/-- Equality on the 31 checked class representatives identifies two rows of
any completed ambient ordinary character table. -/
theorem alternatingSixAmbientOrdinaryRow_eq_of_values_classRepresentative_eq
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    {r s : AlternatingSixAmbientOrdinaryRow}
    (h :
      ∀ j : Fin 31,
        (T.toFiniteCharacterTableCertificate.character r).values
            (alternatingSixUniversalCoverClassRepresentative j) =
          (T.toFiniteCharacterTableCertificate.character s).values
            (alternatingSixUniversalCoverClassRepresentative j)) :
    r = s := by
  apply T.toFiniteCharacterTableCertificate.row_injective
  apply IrreducibleCharacter.ext
  funext g
  let j : Fin 31 :=
    alternatingSixUniversalCoverClassIndexEquiv.symm
      (ConjClasses.mk g)
  have hj :
      ConjClasses.mk
          (alternatingSixUniversalCoverClassRepresentative j) =
        ConjClasses.mk g := by
    change alternatingSixUniversalCoverClassIndexEquiv j = ConjClasses.mk g
    exact alternatingSixUniversalCoverClassIndexEquiv.apply_symm_apply _
  have hconj :
      IsConj
        (alternatingSixUniversalCoverClassRepresentative j) g :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hj
  calc
    (T.toFiniteCharacterTableCertificate.character r).values g =
        (T.toFiniteCharacterTableCertificate.character r).values
          (alternatingSixUniversalCoverClassRepresentative j) :=
      (T.toFiniteCharacterTableCertificate.character r)
        |>.values_eq_of_isConj hconj.symm
    _ =
        (T.toFiniteCharacterTableCertificate.character s).values
          (alternatingSixUniversalCoverClassRepresentative j) :=
      h j
    _ = (T.toFiniteCharacterTableCertificate.character s).values g :=
      (T.toFiniteCharacterTableCertificate.character s)
        |>.values_eq_of_isConj hconj

/-- For an arbitrary proposed position equivalence, the first ambient
semantic bridge is exactly a finite equality on the 31 checked class
representatives. -/
theorem
    AlternatingSixTwoCTblLibRowIdentification.ambientAlphaOneBridge_iff_classValues
    (identification : AlternatingSixTwoCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    identification.AmbientCorrectedAlphaOneBridge T ↔
      ∀ (i : Fin 12) (j : Fin 31),
        (T.toFiniteCharacterTableCertificate.character
            (identification.ambientPositionEquiv
              (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaOne i)).1).values
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
        T 2 (identification.ambientPositionEquiv i) j
  · intro h i
    apply Subtype.ext
    apply alternatingSixAmbientOrdinaryRow_eq_of_values_classRepresentative_eq T
    intro j
    rw [alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq]
    exact
      (alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
        T 2 (identification.ambientPositionEquiv i) j).trans
          (h i j).symm

/-- For an arbitrary proposed position equivalence, the second ambient
semantic bridge is exactly a finite equality on the 31 checked class
representatives. -/
theorem
    AlternatingSixTwoCTblLibRowIdentification.ambientAlphaTwoBridge_iff_classValues
    (identification : AlternatingSixTwoCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    identification.AmbientCorrectedAlphaTwoBridge T ↔
      ∀ (i : Fin 12) (j : Fin 31),
        (T.toFiniteCharacterTableCertificate.character
            (identification.ambientPositionEquiv
              (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaTwo i)).1).values
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
        T 2 (identification.ambientPositionEquiv i) j
  · intro h i
    apply Subtype.ext
    apply alternatingSixAmbientOrdinaryRow_eq_of_values_classRepresentative_eq T
    intro j
    rw [alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq]
    exact
      (alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
        T 2 (identification.ambientPositionEquiv i) j).trans
          (h i j).symm

end InductiveMcKay
end McKayConjecture
