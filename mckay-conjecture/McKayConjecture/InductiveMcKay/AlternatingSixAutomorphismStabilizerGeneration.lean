/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixAutomorphismLowerBound
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibParameterizedFullEquivariance
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibFullEquivarianceReduction
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibParameterizedFullEquivariance
import McKayConjecture.InductiveMcKay.AutomorphismStabilizerGeneration

/-!
# Sylow-automorphism stabilizer generation for the canonical `A₆` cover

The certified four-coset normal form proves that inner automorphisms and the
two audited outer automorphisms generate the full automorphism group of the
canonical universal cover.  The generic correction theorem then replaces
arbitrary inner automorphisms by the inner image of the Sylow normalizer.

This closes, uniformly in the prime and chosen Sylow subgroup, the exact
generation proposition used by all three ordering-safe `A₆` ordinary
equivariance reductions.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixAutGenerationFactPrimeTwo :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

local instance alternatingSixAutGenerationFactPrimeThree :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance alternatingSixAutGenerationFactPrimeFive :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

@[simp]
theorem alternatingSixUniversalCoverOuterRepresentative_one :
    alternatingSixUniversalCoverOuterRepresentative 1 =
      alternatingSixUniversalCoverTransportedAlphaOne := by
  rfl

@[simp]
theorem alternatingSixUniversalCoverOuterRepresentative_two :
    alternatingSixUniversalCoverOuterRepresentative 2 =
      alternatingSixUniversalCoverTransportedAlphaTwo := by
  rfl

/-- Inner normalizer automorphisms and the two corrected audited outer
automorphisms generate the stabilizer of any chosen Sylow subgroup. -/
theorem alternatingSixUniversalCoverSylowAutStabilizer_generation
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    (SylowAutStabilizer.normalizerInnerHom P).range ⊔
        Subgroup.closure
          {alternatingSixUniversalCoverCorrectedAlphaOneStabilizer P,
            alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer P} =
      ⊤ := by
  simpa [
    alternatingSixUniversalCoverCorrectedAlphaOneStabilizer,
    alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
  ] using
    (SylowAutStabilizer.normalizerInner_sup_corrected_pair_eq_top_of_global
      P
      (alternatingSixUniversalCoverOuterRepresentative 1)
      (alternatingSixUniversalCoverOuterRepresentative 2)
      alternatingSixUniversalCover_inner_sup_outer_closure_eq_top)

/-- The exact two-local generation hypothesis is unconditional. -/
theorem alternatingSixTwoSylowAutStabilizerGeneration :
    AlternatingSixTwoSylowAutStabilizerGenerationHypothesis :=
  alternatingSixUniversalCoverSylowAutStabilizer_generation
    (alternatingSixUniversalCoverSylow 2)

/-- The exact three-local generation hypothesis is unconditional. -/
theorem alternatingSixThreeSylowAutStabilizerGeneration :
    AlternatingSixThreeSylowAutStabilizerGenerationHypothesis :=
  alternatingSixUniversalCoverSylowAutStabilizer_generation
    (alternatingSixUniversalCoverSylow 3)

/-- The exact five-local generation hypothesis is unconditional. -/
theorem alternatingSixFiveSylowAutStabilizerGeneration :
    AlternatingSixFiveSylowAutStabilizerGenerationHypothesis :=
  alternatingSixUniversalCoverSylowAutStabilizer_generation
    (alternatingSixUniversalCoverSylow 5)

end InductiveMcKay
end McKayConjecture
