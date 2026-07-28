/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurFiveNormalizerSemidirect
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverFiveLocalStructure
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverSylowTwoQuaternion
import McKayConjecture.Proof.Isomorphism

/-!
# A semidirect-product model of the fixed five-normalizer in `6.A₆`

The explicit presentation calculation identifies the normalizer of its
chosen Sylow-five subgroup with `C₃ × (C₅ ⋊ C₄)`, where a generator of
`C₄` acts on `C₅` by inversion.  This file transports that identification
first across the canonical equivalence of universal central extensions and
then across Sylow conjugacy.  The result concerns the fixed Sylow subgroup
used by the inductive-McKay reduction, rather than merely an unspecified
conjugate.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

open MulAction

local instance alternatingSixUniversalCoverFiveNormalizerSemidirectFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The concrete order-sixty model of the five-normalizer. -/
abbrev AlternatingSixFiveNormalizerSemidirect :=
  Multiplicative (ZMod 3) × CyclicFiveInversionSemidirect

/-- The explicit Sylow-five subgroup of the presented cover, transported
to the canonical universal cover. -/
def alternatingSixSchurFiveSylowInUniversalCover :
    Sylow 5 AlternatingSixUniversalCover :=
  McKayConjecture.Sylow.transport
    alternatingSixSchurEquivUniversalCover
    alternatingSixSchurFiveSylow

/-- A conjugating element carrying the transported explicit Sylow subgroup
to the fixed Sylow subgroup used throughout the reduction. -/
def alternatingSixSchurFiveSylowConjugator :
    AlternatingSixUniversalCover :=
  Classical.choose
    (exists_smul_eq
      AlternatingSixUniversalCover
      alternatingSixSchurFiveSylowInUniversalCover
      (alternatingSixUniversalCoverSylow 5))

theorem alternatingSixSchurFiveSylowConjugator_spec :
    alternatingSixSchurFiveSylowConjugator •
        alternatingSixSchurFiveSylowInUniversalCover =
      alternatingSixUniversalCoverSylow 5 :=
  Classical.choose_spec
    (exists_smul_eq
      AlternatingSixUniversalCover
      alternatingSixSchurFiveSylowInUniversalCover
      (alternatingSixUniversalCoverSylow 5))

/-- Conjugation carrying the transported explicit Sylow subgroup to the
fixed canonical Sylow subgroup. -/
def alternatingSixSchurFiveSylowConjugation :
    MulAut AlternatingSixUniversalCover :=
  MulAut.conj alternatingSixSchurFiveSylowConjugator

@[simp]
theorem alternatingSixSchurFiveSylow_transport_conjugation :
    McKayConjecture.Sylow.transport
        alternatingSixSchurFiveSylowConjugation
        alternatingSixSchurFiveSylowInUniversalCover =
      alternatingSixUniversalCoverSylow 5 := by
  rw [alternatingSixSchurFiveSylowConjugation,
    McKayConjecture.Sylow.transport_conj,
    alternatingSixSchurFiveSylowConjugator_spec]

/-- The normalizer of the transported explicit Sylow subgroup is
isomorphic to the normalizer of the fixed canonical Sylow subgroup. -/
def alternatingSixTransportedFiveNormalizerEquivFixed :
    SylowNormalizer alternatingSixSchurFiveSylowInUniversalCover ≃*
      SylowNormalizer (alternatingSixUniversalCoverSylow 5) :=
  (McKayConjecture.Sylow.normalizerEquiv
      alternatingSixSchurFiveSylowConjugation
      alternatingSixSchurFiveSylowInUniversalCover).trans
    (MulEquiv.subgroupCongr (by
      rw [alternatingSixSchurFiveSylow_transport_conjugation]))

/-- The concrete semidirect-product model is isomorphic to the exact
normalizer of the fixed Sylow-five subgroup in the canonical cover. -/
def alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer :
    AlternatingSixFiveNormalizerSemidirect ≃*
      SylowNormalizer (alternatingSixUniversalCoverSylow 5) :=
  cyclicThreeTimesCyclicFiveInversionSemidirectEquivSchurFiveNormalizer.trans
    ((McKayConjecture.Sylow.normalizerEquiv
      alternatingSixSchurEquivUniversalCover
      alternatingSixSchurFiveSylow).trans
        alternatingSixTransportedFiveNormalizerEquivFixed)

/-- The concrete semidirect-product normalizer model has order sixty. -/
@[simp]
theorem natCard_alternatingSixFiveNormalizerSemidirect :
    Nat.card AlternatingSixFiveNormalizerSemidirect = 60 := by
  calc
    Nat.card AlternatingSixFiveNormalizerSemidirect =
        Nat.card
          (SylowNormalizer
            (alternatingSixUniversalCoverSylow 5)) :=
      Nat.card_congr
        alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer.toEquiv
    _ = 60 :=
      natCard_normalizer_alternatingSixUniversalCoverSylowFive_exact

end GroupTheory
end McKayConjecture
