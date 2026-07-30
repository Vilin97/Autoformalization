/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoInvariantSafeLocalSignObstructions

/-!
# A corrected finite orientation of the two-local CTblLib rows

The invariant-safe orientation was obtained by transporting an ambient
central-block convention, and its local generator bridges are false.  The
audited local permutations themselves force a different quaternion-sign
layout.

This file records that layout.  The four positions with trivial cyclic
coordinate are ordered as

`(0,0,0), (0,1,0), (0,1,1), (0,0,1)`.

In each nontrivial cyclic block, positions paired by the first audited
generator have the same quaternion sign.  The second generator then has
the shear pattern

`(u,v) ↦ (u,u+v)`.

The cyclic coordinate and all rows with `u = 0` are proved
unconditionally from the genuine actual-normalizer action.  The two full
finite bridges are reduced to six explicit seed equations, one for each
corrected generator and cyclic coordinate.  These seeds are the exact
remaining semantic calculation; the row order itself contains no
ambient-table convention.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoCorrectedLocalRowIdentificationFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-! ### Rows with trivial first quaternion sign -/

/-- The first genuine corrected action has the forced value on both rows
whose first quaternion sign is trivial. -/
theorem
    alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_zeroFst
    (j : Fin 3) (v : Fin 2) :
    alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
        (j, ((0 : Fin 2), v)) =
      (-j, ((0 : Fin 2), v)) := by
  fin_cases v
  · apply Prod.ext
    · exact
        alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_fst
          (j, ((0 : Fin 2), (0 : Fin 2)))
    · simpa [
        alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
      ] using
        alternatingSixTwoActualNormalizerRowPermutation_quaternion_zero
          (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
            (alternatingSixUniversalCoverSylow 2)) j
  · apply Prod.ext
    · exact
        alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_fst
          (j, ((0 : Fin 2), (1 : Fin 2)))
    · apply Prod.ext
      · exact
          alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
            (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
              (alternatingSixUniversalCoverSylow 2))
            (j, ((0 : Fin 2), (1 : Fin 2)))
      · apply Fin.eq_one_of_ne_zero
        intro hv
        exfalso
        change
          (alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
            (j, ((0 : Fin 2), (1 : Fin 2)))).2.2 =
            (0 : Fin 2) at hv
        have hzero :
              alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
                  (j, ((0 : Fin 2), (0 : Fin 2))) =
                (-j, ((0 : Fin 2), (0 : Fin 2))) := by
            apply Prod.ext
            · exact
                alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_fst
                  (j, ((0 : Fin 2), (0 : Fin 2)))
            · simpa [
                alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
              ] using
                alternatingSixTwoActualNormalizerRowPermutation_quaternion_zero
                  (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
                    (alternatingSixUniversalCoverSylow 2)) j
        have heq :
              alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
                  (j, ((0 : Fin 2), (1 : Fin 2))) =
                alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
                  (j, ((0 : Fin 2), (0 : Fin 2))) := by
          rw [hzero]
          apply Prod.ext
          · exact
              alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_fst
                (j, ((0 : Fin 2), (1 : Fin 2)))
          · apply Prod.ext
            · simpa [
                alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
              ] using
                alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
                  (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
                    (alternatingSixUniversalCoverSylow 2))
                  (j, ((0 : Fin 2), (1 : Fin 2)))
            · exact hv
        have hsource :=
          alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
            |>.injective heq
        exact (by decide : (1 : Fin 2) ≠ 0)
          (congrArg (fun r => r.2.2) hsource)

/-- The second genuine corrected action has the forced value on both rows
whose first quaternion sign is trivial. -/
theorem
    alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_zeroFst
    (j : Fin 3) (v : Fin 2) :
    alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
        (j, ((0 : Fin 2), v)) =
      (-j, ((0 : Fin 2), v)) := by
  fin_cases v
  · apply Prod.ext
    · exact
        alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_fst
          (j, ((0 : Fin 2), (0 : Fin 2)))
    · simpa [
        alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
      ] using
        alternatingSixTwoActualNormalizerRowPermutation_quaternion_zero
          (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
            (alternatingSixUniversalCoverSylow 2)) j
  · apply Prod.ext
    · exact
        alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_fst
          (j, ((0 : Fin 2), (1 : Fin 2)))
    · apply Prod.ext
      · exact
          alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
            (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
              (alternatingSixUniversalCoverSylow 2))
            (j, ((0 : Fin 2), (1 : Fin 2)))
      · apply Fin.eq_one_of_ne_zero
        intro hv
        exfalso
        change
          (alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
            (j, ((0 : Fin 2), (1 : Fin 2)))).2.2 =
            (0 : Fin 2) at hv
        have hzero :
              alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
                  (j, ((0 : Fin 2), (0 : Fin 2))) =
                (-j, ((0 : Fin 2), (0 : Fin 2))) := by
            apply Prod.ext
            · exact
                alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_fst
                  (j, ((0 : Fin 2), (0 : Fin 2)))
            · simpa [
                alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
              ] using
                alternatingSixTwoActualNormalizerRowPermutation_quaternion_zero
                  (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
                    (alternatingSixUniversalCoverSylow 2)) j
        have heq :
              alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
                  (j, ((0 : Fin 2), (1 : Fin 2))) =
                alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
                  (j, ((0 : Fin 2), (0 : Fin 2))) := by
          rw [hzero]
          apply Prod.ext
          · exact
              alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_fst
                (j, ((0 : Fin 2), (1 : Fin 2)))
          · apply Prod.ext
            · simpa [
                alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
              ] using
                alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
                  (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
                    (alternatingSixUniversalCoverSylow 2))
                  (j, ((0 : Fin 2), (1 : Fin 2)))
            · exact hv
        have hsource :=
          alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
            |>.injective heq
        exact (by decide : (1 : Fin 2) ≠ 0)
          (congrArg (fun r => r.2.2) hsource)

/-! ### Corrected finite local positions -/

/-- The local row order forced by the two audited permutation patterns,
up to the harmless choice of an orientation inside each two-element
sign block. -/
def alternatingSixTwoCTblLibCorrectedLocalPositionEquiv :
    Fin 12 ≃ AlternatingSixTwoConcreteNormalizerRow :=
  Equiv.ofBijective
    ![((0 : Fin 3), ((0 : Fin 2), (0 : Fin 2))),
      ((0 : Fin 3), ((1 : Fin 2), (0 : Fin 2))),
      ((0 : Fin 3), ((1 : Fin 2), (1 : Fin 2))),
      ((0 : Fin 3), ((0 : Fin 2), (1 : Fin 2))),
      ((1 : Fin 3), ((1 : Fin 2), (0 : Fin 2))),
      ((2 : Fin 3), ((1 : Fin 2), (0 : Fin 2))),
      ((1 : Fin 3), ((1 : Fin 2), (1 : Fin 2))),
      ((2 : Fin 3), ((1 : Fin 2), (1 : Fin 2))),
      ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2))),
      ((2 : Fin 3), ((0 : Fin 2), (0 : Fin 2))),
      ((1 : Fin 3), ((0 : Fin 2), (1 : Fin 2))),
      ((2 : Fin 3), ((0 : Fin 2), (1 : Fin 2)))]
    (by decide)

/-- The corrected local order still has exactly the central exponents
recorded by the CTblLib audit. -/
theorem alternatingSixTwoCTblLibCorrectedLocalPositionEquiv_centralExponent
    (i : Fin 12) :
    alternatingSixTwoConcreteNormalizerRowCentralExponent
        (alternatingSixTwoCTblLibCorrectedLocalPositionEquiv i) =
      alternatingSixCTblLibTwoPPrimeActionData.localCentralExponent i := by
  fin_cases i <;>
    rfl

/-! ### Six residual seed equations -/

/-- Once the first corrected generator has the expected value on the
`(1,0)` sign row in one cyclic block, injectivity forces its value on the
other `u = 1` row in that block. -/
theorem
    alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_oneFst_one
    (j : Fin 3)
    (h :
      alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
          (j, ((1 : Fin 2), (0 : Fin 2))) =
        (-j, ((1 : Fin 2), (0 : Fin 2)))) :
    alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
        (j, ((1 : Fin 2), (1 : Fin 2))) =
      (-j, ((1 : Fin 2), (1 : Fin 2))) := by
  apply Prod.ext
  · exact
      alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_fst
        (j, ((1 : Fin 2), (1 : Fin 2)))
  · apply Prod.ext
    · simpa [
        alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
      ] using
        alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
          (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
            (alternatingSixUniversalCoverSylow 2))
          (j, ((1 : Fin 2), (1 : Fin 2)))
    · apply Fin.eq_one_of_ne_zero
      intro hv
      have heq :
          alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
              (j, ((1 : Fin 2), (1 : Fin 2))) =
            alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
              (j, ((1 : Fin 2), (0 : Fin 2))) := by
        rw [h]
        apply Prod.ext
        · exact
            alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_fst
              (j, ((1 : Fin 2), (1 : Fin 2)))
        · apply Prod.ext
          · simpa [
              alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
            ] using
              alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
                (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
                  (alternatingSixUniversalCoverSylow 2))
                (j, ((1 : Fin 2), (1 : Fin 2)))
          · exact hv
      have hsource :=
        alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
          |>.injective heq
      exact (by decide : (1 : Fin 2) ≠ 0)
        (congrArg (fun r => r.2.2) hsource)

/-- Once the second corrected generator shears the `(1,0)` row in one
cyclic block, injectivity forces the reverse shear on `(1,1)`. -/
theorem
    alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_oneFst_one
    (j : Fin 3)
    (h :
      alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
          (j, ((1 : Fin 2), (0 : Fin 2))) =
        (-j, ((1 : Fin 2), (1 : Fin 2)))) :
    alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
        (j, ((1 : Fin 2), (1 : Fin 2))) =
      (-j, ((1 : Fin 2), (0 : Fin 2))) := by
  apply Prod.ext
  · exact
      alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_fst
        (j, ((1 : Fin 2), (1 : Fin 2)))
  · apply Prod.ext
    · simpa [
        alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
      ] using
        alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
          (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
            (alternatingSixUniversalCoverSylow 2))
          (j, ((1 : Fin 2), (1 : Fin 2)))
    · by_contra hv
      have hvOne :
          (alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
            (j, ((1 : Fin 2), (1 : Fin 2)))).2.2 =
              (1 : Fin 2) :=
        Fin.eq_one_of_ne_zero _ hv
      have heq :
          alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
              (j, ((1 : Fin 2), (1 : Fin 2))) =
            alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
              (j, ((1 : Fin 2), (0 : Fin 2))) := by
        rw [h]
        apply Prod.ext
        · exact
            alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_fst
              (j, ((1 : Fin 2), (1 : Fin 2)))
        · apply Prod.ext
          · simpa [
              alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
            ] using
              alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
                (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
                  (alternatingSixUniversalCoverSylow 2))
                (j, ((1 : Fin 2), (1 : Fin 2)))
          · exact hvOne
      have hsource :=
        alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
          |>.injective heq
      exact (by decide : (1 : Fin 2) ≠ 0)
        (congrArg (fun r => r.2.2) hsource)

/-- The three still-unknown first-generator values, one in each cyclic
block.  All other first-generator values follow formally. -/
def AlternatingSixTwoCorrectedLocalAlphaOneSeedEquations : Prop :=
  alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
      ((0 : Fin 3), ((1 : Fin 2), (0 : Fin 2))) =
    ((0 : Fin 3), ((1 : Fin 2), (0 : Fin 2))) ∧
  alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
      ((1 : Fin 3), ((1 : Fin 2), (0 : Fin 2))) =
    ((2 : Fin 3), ((1 : Fin 2), (0 : Fin 2))) ∧
  alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
      ((2 : Fin 3), ((1 : Fin 2), (0 : Fin 2))) =
    ((1 : Fin 3), ((1 : Fin 2), (0 : Fin 2)))

/-- The three still-unknown second-generator values, one in each cyclic
block.  All other second-generator values follow formally. -/
def AlternatingSixTwoCorrectedLocalAlphaTwoSeedEquations : Prop :=
  alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
      ((0 : Fin 3), ((1 : Fin 2), (0 : Fin 2))) =
    ((0 : Fin 3), ((1 : Fin 2), (1 : Fin 2))) ∧
  alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
      ((1 : Fin 3), ((1 : Fin 2), (0 : Fin 2))) =
    ((2 : Fin 3), ((1 : Fin 2), (1 : Fin 2))) ∧
  alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
      ((2 : Fin 3), ((1 : Fin 2), (0 : Fin 2))) =
    ((1 : Fin 3), ((1 : Fin 2), (1 : Fin 2)))

/-- The first corrected local CTblLib bridge for the new position order. -/
def AlternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge : Prop :=
  ∀ i : Fin 12,
    alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
        (alternatingSixTwoCTblLibCorrectedLocalPositionEquiv i) =
      alternatingSixTwoCTblLibCorrectedLocalPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.localAlphaOne i)

/-- The second corrected local CTblLib bridge for the new position order. -/
def AlternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge : Prop :=
  ∀ i : Fin 12,
    alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
        (alternatingSixTwoCTblLibCorrectedLocalPositionEquiv i) =
      alternatingSixTwoCTblLibCorrectedLocalPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.localAlphaTwo i)

/-- The twelve first-generator row equations are equivalent to only the
three nontrivial-sign seeds. -/
theorem alternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge_iff_seeds :
    AlternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge ↔
      AlternatingSixTwoCorrectedLocalAlphaOneSeedEquations := by
  constructor
  · intro h
    exact ⟨by
        simpa [
          AlternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge,
          alternatingSixTwoCTblLibCorrectedLocalPositionEquiv,
          alternatingSixCTblLibTwoPPrimeActionData
        ] using h (1 : Fin 12),
      by
        simpa [
          AlternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge,
          alternatingSixTwoCTblLibCorrectedLocalPositionEquiv,
          alternatingSixCTblLibTwoPPrimeActionData
        ] using h (4 : Fin 12),
      by
        simpa [
          AlternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge,
          alternatingSixTwoCTblLibCorrectedLocalPositionEquiv,
          alternatingSixCTblLibTwoPPrimeActionData
        ] using h (5 : Fin 12)⟩
  · rintro ⟨hZero, hOne, hTwo⟩ i
    have hZeroOne :=
      alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_oneFst_one
        (0 : Fin 3) hZero
    have hOneOne :=
      alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_oneFst_one
        (1 : Fin 3) hOne
    have hTwoOne :=
      alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_oneFst_one
        (2 : Fin 3) hTwo
    fin_cases i <;>
      simp only [
        alternatingSixTwoCTblLibCorrectedLocalPositionEquiv,
        alternatingSixCTblLibTwoPPrimeActionData
      ] <;>
      first
      | exact hZero
      | exact hOne
      | exact hTwo
      | exact hZeroOne
      | exact hOneOne
      | exact hTwoOne
      | apply
          alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_zeroFst

/-- The twelve second-generator row equations are equivalent to only the
three shear seeds. -/
theorem alternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge_iff_seeds :
    AlternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge ↔
      AlternatingSixTwoCorrectedLocalAlphaTwoSeedEquations := by
  constructor
  · intro h
    exact ⟨by
        simpa [
          AlternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge,
          alternatingSixTwoCTblLibCorrectedLocalPositionEquiv,
          alternatingSixCTblLibTwoPPrimeActionData
        ] using h (1 : Fin 12),
      by
        simpa [
          AlternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge,
          alternatingSixTwoCTblLibCorrectedLocalPositionEquiv,
          alternatingSixCTblLibTwoPPrimeActionData
        ] using h (4 : Fin 12),
      by
        simpa [
          AlternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge,
          alternatingSixTwoCTblLibCorrectedLocalPositionEquiv,
          alternatingSixCTblLibTwoPPrimeActionData
        ] using h (5 : Fin 12)⟩
  · rintro ⟨hZero, hOne, hTwo⟩ i
    have hZeroOne :=
      alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_oneFst_one
        (0 : Fin 3) hZero
    have hOneOne :=
      alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_oneFst_one
        (1 : Fin 3) hOne
    have hTwoOne :=
      alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_oneFst_one
        (2 : Fin 3) hTwo
    fin_cases i <;>
      simp only [
        alternatingSixTwoCTblLibCorrectedLocalPositionEquiv,
        alternatingSixCTblLibTwoPPrimeActionData
      ] <;>
      first
      | exact hZero
      | exact hOne
      | exact hTwo
      | exact hZeroOne
      | exact hOneOne
      | exact hTwoOne
      | apply
          alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_zeroFst

/-- Both corrected finite bridges hold exactly when the six semantic seed
values have the expected identity/shear pattern. -/
theorem alternatingSixTwoCTblLibCorrectedLocalBridges_iff_sixSeeds :
    (AlternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge ∧
        AlternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge) ↔
      (AlternatingSixTwoCorrectedLocalAlphaOneSeedEquations ∧
        AlternatingSixTwoCorrectedLocalAlphaTwoSeedEquations) := by
  rw [
    alternatingSixTwoCTblLibCorrectedLocalAlphaOneBridge_iff_seeds,
    alternatingSixTwoCTblLibCorrectedLocalAlphaTwoBridge_iff_seeds
  ]

end InductiveMcKay
end McKayConjecture
