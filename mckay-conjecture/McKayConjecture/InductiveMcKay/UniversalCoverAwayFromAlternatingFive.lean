/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingBeyondFiveUniversalCover

/-!
# Removing the verified `A₅` target from the universal-cover hypothesis

The projective tables for the binary icosahedral group prove the complete
universal-cover input for every simple target isomorphic to `A₅`, at every
prime.  Together with the automatic target-prime-absent case, the exact
remaining global obligation is therefore:

* the target is a nonabelian finite simple group;
* `p` divides its order; and
* it is not isomorphic to `A₅`.

This file proves that residual equivalent to the original universal-cover
hypothesis in universe zero.  It is a genuine removal of a completed
simple-group case, rather than a renamed copy of the hypothesis.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- One-cover/one-Sylow verification for precisely the prime-supported
non-`A₅` simple targets. -/
def SimpleTargetPrimeSupportedAwayFromAlternatingFiveVerification
    (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    IsSimpleGroup S →
      ¬IsMulCommutative S →
        p ∣ Nat.card S →
          ¬Nonempty (S ≃* alternatingGroup (Fin 5)) →
            ∃ (U : Type) (_ : Group U) (_ : Finite U)
                (_E : UniversalCentralExtension U S)
                (P : Sylow p U),
              Nonempty (LocalInductiveMcKayData P)

namespace SimpleTargetPrimeSupportedAwayFromAlternatingFiveVerification

/-- The residual verification plus the completed binary-icosahedral
tables recovers prime-supported verification for every simple target. -/
theorem toSimpleTargetPrimeSupported
    {p : ℕ} [Fact p.Prime]
    (h :
      SimpleTargetPrimeSupportedAwayFromAlternatingFiveVerification p) :
    SimpleTargetPrimeSupportedUniversalCoverVerification.{0} p := by
  intro S _ _ hsimple hnoncomm hpS
  by_cases hfive :
      Nonempty (S ≃* alternatingGroup (Fin 5))
  · exact
      alternatingFiveFamilyVerification p S
        ((alternatingFiveSimpleGroupFamily_contains_iff S).2 hfive)
        hsimple hnoncomm
  · exact h S hsimple hnoncomm hpS hfive

/-- Hence the non-`A₅`, prime-supported residual implies the complete
universal-cover hypothesis. -/
theorem toUniversalCover
    {p : ℕ} [Fact p.Prime]
    (h :
      SimpleTargetPrimeSupportedAwayFromAlternatingFiveVerification p) :
    UniversalCoverInductiveMcKayHypothesis.{0} p :=
  h.toSimpleTargetPrimeSupported.toUniversalCover

/-- The same exact residual also supplies the quasisimple hypothesis via
the already formalized descent from universal covers. -/
theorem toQuasisimple
    {p : ℕ} [Fact p.Prime]
    (h :
      SimpleTargetPrimeSupportedAwayFromAlternatingFiveVerification p) :
    QuasisimpleInductiveMcKayHypothesis.{0} p :=
  h.toUniversalCover.toQuasisimple

end SimpleTargetPrimeSupportedAwayFromAlternatingFiveVerification

namespace UniversalCoverInductiveMcKayHypothesis

/-- The full universal-cover hypothesis restricts to the non-`A₅`,
prime-supported residual. -/
theorem toSimpleTargetPrimeSupportedAwayFromAlternatingFive
    {p : ℕ}
    (h : UniversalCoverInductiveMcKayHypothesis.{0} p) :
    SimpleTargetPrimeSupportedAwayFromAlternatingFiveVerification p := by
  intro S _ _ hsimple hnoncomm hpS _
  exact
    h.toSimpleTargetPrimeSupportedVerification
      S hsimple hnoncomm hpS

/-- Exact global decomposition: the complete `A₅` tables and the automatic
prime-absent construction remove exactly those targets, leaving only
prime-supported non-`A₅` simple groups. -/
theorem iff_simpleTargetPrimeSupportedAwayFromAlternatingFive
    {p : ℕ} [Fact p.Prime] :
    UniversalCoverInductiveMcKayHypothesis.{0} p ↔
      SimpleTargetPrimeSupportedAwayFromAlternatingFiveVerification p :=
  ⟨toSimpleTargetPrimeSupportedAwayFromAlternatingFive,
    SimpleTargetPrimeSupportedAwayFromAlternatingFiveVerification.toUniversalCover⟩

end UniversalCoverInductiveMcKayHypothesis

end InductiveMcKay
end McKayConjecture
