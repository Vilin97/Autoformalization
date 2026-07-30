/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibParameterizedRowBridge

/-!
# Degree obstructions to the engineered five-local CTblLib positions

The five-local central-block identification was engineered so that
transporting the audited finite candidate recovers the existing algebraic
row matching.  Its ambient position equivalence is merely the arithmetic
ordering of the project's twenty-four prime-to-five rows.

That ordering cannot be CTblLib's semantic order.  Under it, the first
audited ambient generator would send a degree-four row to a degree-six row,
and the second would send a degree-three row to a degree-four row.  Genuine
automorphisms preserve character degree, so both ambient bridge predicates
are false.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveCTblLibCentralBlockObstructionFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- At engineered position six, the first audited permutation would send
the degree-four `row07` to the degree-six `row10`. -/
theorem
    alternatingSixFiveCentralBlockCTblLibRowIdentification_not_ambientAlphaOneBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    ¬ (alternatingSixFiveCentralBlockCTblLibRowIdentification
        |>.AmbientCorrectedAlphaOneBridge T) := by
  intro h
  let r :=
    alternatingSixFiveCentralBlockCTblLibRowIdentification
      |>.ambientPositionEquiv (6 : Fin 24)
  have hdegree :=
    alternatingSixAmbientPPrimeRowPermutation_dimension T 5
      (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 5) :
        MulAut AlternatingSixUniversalCover)
      r
  have hrow :
      alternatingSixAmbientPPrimeRowPermutation T 5
          (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
            (alternatingSixUniversalCoverSylow 5) :
            MulAut AlternatingSixUniversalCover)
          r =
        (alternatingSixFiveCentralBlockCTblLibRowIdentification
          |>.ambientPositionEquiv
            (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne
              (6 : Fin 24))) := by
    exact h 6
  rw [hrow] at hdegree
  have hrDegree : r.1.dimension = 4 := by
    rfl
  have htargetDegree :
      ((alternatingSixFiveCentralBlockCTblLibRowIdentification
        |>.ambientPositionEquiv
          (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne
            (6 : Fin 24))).1.dimension) = 6 := by
    rfl
  omega

/-- At engineered position four, the second audited permutation would send
the degree-three `row05` to the degree-four `row06`. -/
theorem
    alternatingSixFiveCentralBlockCTblLibRowIdentification_not_ambientAlphaTwoBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    ¬ (alternatingSixFiveCentralBlockCTblLibRowIdentification
        |>.AmbientCorrectedAlphaTwoBridge T) := by
  intro h
  let r :=
    alternatingSixFiveCentralBlockCTblLibRowIdentification
      |>.ambientPositionEquiv (4 : Fin 24)
  have hdegree :=
    alternatingSixAmbientPPrimeRowPermutation_dimension T 5
      (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
        (alternatingSixUniversalCoverSylow 5) :
        MulAut AlternatingSixUniversalCover)
      r
  have hrow :
      alternatingSixAmbientPPrimeRowPermutation T 5
          (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
            (alternatingSixUniversalCoverSylow 5) :
            MulAut AlternatingSixUniversalCover)
          r =
        (alternatingSixFiveCentralBlockCTblLibRowIdentification
          |>.ambientPositionEquiv
            (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo
              (4 : Fin 24))) := by
    exact h 4
  rw [hrow] at hdegree
  have hrDegree : r.1.dimension = 3 := by
    rfl
  have htargetDegree :
      ((alternatingSixFiveCentralBlockCTblLibRowIdentification
        |>.ambientPositionEquiv
          (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo
            (4 : Fin 24))).1.dimension) = 4 := by
    rfl
  omega

end InductiveMcKay
end McKayConjecture
