/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurThreeNormalizerSemidirect
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverThreeNormalizerQuotientModel

/-!
# A semidirect-product model of the fixed three-normalizer in `6.A₆`

The explicit presented-cover calculation gives the exact model
`3^{1+2} ⋊ C₈` for the normalizer of its Heisenberg Sylow subgroup.
This file transports that model across the canonical equivalence of
universal central extensions and then across Sylow conjugacy to the
fixed Sylow subgroup used by the inductive-McKay reduction.

The result upgrades the previous quotient model: the order-216 exact
normalizer itself, not merely its quotient by the center, is identified
with the concrete semidirect product.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

open MulAction

local instance alternatingSixUniversalCoverThreeSemidirectFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The explicit Schur-cover Sylow-three subgroup transported to the
canonical universal cover. -/
def alternatingSixSchurThreeSylowInUniversalCover :
    Sylow 3 AlternatingSixUniversalCover :=
  McKayConjecture.Sylow.transport
    alternatingSixSchurEquivUniversalCover
    alternatingSixSchurSylowThree

/-- A conjugating element carrying the transported explicit subgroup to
the fixed canonical Sylow subgroup. -/
def alternatingSixSchurThreeSylowConjugator :
    AlternatingSixUniversalCover :=
  Classical.choose
    (exists_smul_eq
      AlternatingSixUniversalCover
      alternatingSixSchurThreeSylowInUniversalCover
      (alternatingSixUniversalCoverSylow 3))

theorem alternatingSixSchurThreeSylowConjugator_spec :
    alternatingSixSchurThreeSylowConjugator •
        alternatingSixSchurThreeSylowInUniversalCover =
      alternatingSixUniversalCoverSylow 3 :=
  Classical.choose_spec
    (exists_smul_eq
      AlternatingSixUniversalCover
      alternatingSixSchurThreeSylowInUniversalCover
      (alternatingSixUniversalCoverSylow 3))

/-- Conjugation carrying the transported explicit Sylow subgroup to the
fixed canonical Sylow subgroup. -/
def alternatingSixSchurThreeSylowConjugation :
    MulAut AlternatingSixUniversalCover :=
  MulAut.conj alternatingSixSchurThreeSylowConjugator

@[simp]
theorem alternatingSixSchurThreeSylow_transport_conjugation :
    McKayConjecture.Sylow.transport
        alternatingSixSchurThreeSylowConjugation
        alternatingSixSchurThreeSylowInUniversalCover =
      alternatingSixUniversalCoverSylow 3 := by
  rw [alternatingSixSchurThreeSylowConjugation,
    McKayConjecture.Sylow.transport_conj,
    alternatingSixSchurThreeSylowConjugator_spec]

/-- The normalizer of the transported explicit Sylow subgroup is
isomorphic to the normalizer of the fixed canonical Sylow subgroup. -/
def alternatingSixTransportedThreeNormalizerEquivFixed :
    SylowNormalizer alternatingSixSchurThreeSylowInUniversalCover ≃*
      AlternatingSixUniversalCoverThreeNormalizer :=
  (McKayConjecture.Sylow.normalizerEquiv
      alternatingSixSchurThreeSylowConjugation
      alternatingSixSchurThreeSylowInUniversalCover).trans
    (MulEquiv.subgroupCongr (by
      rw [alternatingSixSchurThreeSylow_transport_conjugation]))

/-- The exact internal `3^{1+2} ⋊ C₈` model is isomorphic to the fixed
Sylow-three normalizer in the canonical universal cover. -/
def alternatingSixThreeNormalizerSemidirectEquivUniversalCoverNormalizer :
    AlternatingSixSchurThreeNormalizerSemidirect ≃*
      AlternatingSixUniversalCoverThreeNormalizer :=
  alternatingSixSchurThreeNormalizerSemidirectEquiv.trans
    ((McKayConjecture.Sylow.normalizerEquiv
      alternatingSixSchurEquivUniversalCover
      alternatingSixSchurSylowThree).trans
        alternatingSixTransportedThreeNormalizerEquivFixed)

/-- The concrete-factor `3^{1+2} ⋊ C₈` model is isomorphic to the fixed
Sylow-three normalizer in the canonical universal cover. -/
def alternatingSixThreeHeisenbergCyclicEightEquivUniversalCoverNormalizer :
    AlternatingSixThreeHeisenbergCyclicEightSemidirect ≃*
      AlternatingSixUniversalCoverThreeNormalizer :=
  alternatingSixThreeHeisenbergCyclicEightEquivSchurNormalizer.trans
    ((McKayConjecture.Sylow.normalizerEquiv
      alternatingSixSchurEquivUniversalCover
      alternatingSixSchurSylowThree).trans
        alternatingSixTransportedThreeNormalizerEquivFixed)

/-- The semidirect-product model has order 216. -/
@[simp]
theorem natCard_alternatingSixThreeNormalizerSemidirect :
    Nat.card AlternatingSixSchurThreeNormalizerSemidirect = 216 := by
  calc
    Nat.card AlternatingSixSchurThreeNormalizerSemidirect =
        Nat.card AlternatingSixUniversalCoverThreeNormalizer :=
      Nat.card_congr
        alternatingSixThreeNormalizerSemidirectEquivUniversalCoverNormalizer.toEquiv
    _ = 216 :=
      natCard_normalizer_alternatingSixUniversalCoverSylowThree

/-- The concrete-factor semidirect-product model also has order 216. -/
@[simp]
theorem natCard_alternatingSixThreeHeisenbergCyclicEightSemidirect_canonical :
    Nat.card AlternatingSixThreeHeisenbergCyclicEightSemidirect = 216 := by
  calc
    Nat.card AlternatingSixThreeHeisenbergCyclicEightSemidirect =
        Nat.card AlternatingSixUniversalCoverThreeNormalizer :=
      Nat.card_congr
        alternatingSixThreeHeisenbergCyclicEightEquivUniversalCoverNormalizer.toEquiv
    _ = 216 :=
      natCard_normalizer_alternatingSixUniversalCoverSylowThree

end GroupTheory
end McKayConjecture
