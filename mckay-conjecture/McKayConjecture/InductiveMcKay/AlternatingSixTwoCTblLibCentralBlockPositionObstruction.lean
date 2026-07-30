/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoAmbientCharacterBridge
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibParameterizedRowBridge

/-!
# Degree obstructions to the engineered two-local CTblLib position data

The central-block CTblLib row identification was deliberately engineered so
that transport of the audited finite candidate recovers the existing
central-block matching.  Its ambient position equivalence is the arithmetic
ordering of the project's odd-dimensional rows, not a semantic
identification with CTblLib positions.

This distinction is forced, rather than merely cautionary.  In the engineered
ordering the first audited ambient permutation sends the degree-three
`row05` position to the degree-nine `row20` position, and the second sends
it to the degree-five `row08` position.  Genuine character actions preserve
degree, so neither ambient semantic bridge can hold for this engineered
identification.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoCTblLibCentralBlockPositionObstructionFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The first audited ambient permutation is incompatible with the
engineered arithmetic position ordering: at position four it would have to
send a degree-three character to a degree-nine character. -/
theorem
    alternatingSixTwoCentralBlockCTblLibRowIdentification_not_ambientAlphaOneBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    ¬ (alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.AmbientCorrectedAlphaOneBridge T) := by
  intro h
  let r :=
    alternatingSixTwoCentralBlockCTblLibRowIdentification
      |>.ambientPositionEquiv (4 : Fin 12)
  have hdegree :=
    alternatingSixAmbientTwoPPrimeRowIndexAction_dimension T
      (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 2)) r
  have hrow :
      alternatingSixAmbientTwoPPrimeRowIndexAction T
          (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
            (alternatingSixUniversalCoverSylow 2)) r =
        (alternatingSixTwoCentralBlockCTblLibRowIdentification
          |>.ambientPositionEquiv
              (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaOne
                (4 : Fin 12))) := by
    exact h 4
  rw [hrow] at hdegree
  have hrDegree : r.1.dimension = 3 := by
    rfl
  have htargetDegree :
      ((alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.ambientPositionEquiv
            (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaOne
              (4 : Fin 12))).1.dimension) = 9 := by
    rfl
  omega

/-- The second audited ambient permutation is incompatible with the
engineered arithmetic position ordering: at position four it would have to
send a degree-three character to a degree-five character. -/
theorem
    alternatingSixTwoCentralBlockCTblLibRowIdentification_not_ambientAlphaTwoBridge
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) :
    ¬ (alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.AmbientCorrectedAlphaTwoBridge T) := by
  intro h
  let r :=
    alternatingSixTwoCentralBlockCTblLibRowIdentification
      |>.ambientPositionEquiv (4 : Fin 12)
  have hdegree :=
    alternatingSixAmbientTwoPPrimeRowIndexAction_dimension T
      (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
        (alternatingSixUniversalCoverSylow 2)) r
  have hrow :
      alternatingSixAmbientTwoPPrimeRowIndexAction T
          (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
            (alternatingSixUniversalCoverSylow 2)) r =
        (alternatingSixTwoCentralBlockCTblLibRowIdentification
          |>.ambientPositionEquiv
              (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaTwo
                (4 : Fin 12))) := by
    exact h 4
  rw [hrow] at hdegree
  have hrDegree : r.1.dimension = 3 := by
    rfl
  have htargetDegree :
      ((alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.ambientPositionEquiv
            (alternatingSixCTblLibTwoPPrimeActionData.ambientAlphaTwo
              (4 : Fin 12))).1.dimension) = 5 := by
    rfl
  omega

end InductiveMcKay
end McKayConjecture
