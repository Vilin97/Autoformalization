/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverFiveNormalizerCentralGenerator

/-!
# A generator for the center of the five-normalizer of `6.A₆`

The concrete five-normalizer is a finite product model.  An executable
calculation shows that its distinguished order-six element generates its
entire center.  Transporting this statement to the fixed Sylow
five-normalizer proves two facts needed by rowwise projective compatibility:

* every central normalizer element is a natural power of the distinguished
  generator; and
* every such element is already central in the ambient universal cover.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixFiveNormalizerCenterGenerationFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The center of the inversion semidirect factor consists of the identity
and the square of its cyclic-four generator. -/
theorem cyclicFiveInversionSemidirect_mem_center_eq_one_or_generator_sq
    (z : CyclicFiveInversionSemidirect)
    (hz : z ∈ Subgroup.center CyclicFiveInversionSemidirect) :
    z = 1 ∨ z = cyclicFourSemidirectGenerator ^ 2 := by
  obtain ⟨q, rfl⟩ :=
    quaternionFiveEquivCyclicFiveInversionSemidirect.surjective z
  have hqcenter :
      q ∈ Subgroup.center (QuaternionGroup 5) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro x
    apply quaternionFiveEquivCyclicFiveInversionSemidirect.injective
    simpa only [map_mul] using
      hz (quaternionFiveEquivCyclicFiveInversionSemidirect x)
  have quaternion_center :
      ∀ q : QuaternionGroup 5,
        q ∈ Subgroup.center (QuaternionGroup 5) →
          q = QuaternionGroup.a 0 ∨
            q = QuaternionGroup.a 5 := by
    decide
  rcases quaternion_center q hqcenter with hq | hq
  · subst q
    left
    simp
  · subst q
    right
    apply quaternionFiveEquivCyclicFiveInversionSemidirect.symm.injective
    rw [
      quaternionFiveEquivCyclicFiveInversionSemidirect_symm_generator_sq,
      quaternionFiveEquivCyclicFiveInversionSemidirect.symm_apply_apply
    ]

/-- The distinguished concrete element lies in the center of the product
model for the five-normalizer. -/
theorem alternatingSixFiveNormalizerSemidirectCentralGenerator_mem_center :
    alternatingSixFiveNormalizerSemidirectCentralGenerator ∈
      Subgroup.center
        (Multiplicative (ZMod 3) × CyclicFiveInversionSemidirect) := by
  rw [Subgroup.mem_center_iff]
  intro z
  apply Prod.ext
  · exact mul_comm _ _
  · exact
      Subgroup.mem_center_iff.mp
        cyclicFourSemidirectGenerator_sq_mem_center z.2

/-- Every central element of the concrete five-normalizer is one of the
first six powers of the distinguished generator. -/
theorem alternatingSixFiveNormalizerSemidirect_center_generated
    (z : Multiplicative (ZMod 3) × CyclicFiveInversionSemidirect)
    (hz :
      z ∈ Subgroup.center
        (Multiplicative (ZMod 3) × CyclicFiveInversionSemidirect)) :
    ∃ n : Fin 6,
      z = alternatingSixFiveNormalizerSemidirectCentralGenerator ^ n.1 := by
  rcases z with ⟨j, z⟩
  have hzSecond :
      z ∈ Subgroup.center CyclicFiveInversionSemidirect := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro x
    exact congrArg Prod.snd (hz (1, x))
  rcases
      cyclicFiveInversionSemidirect_mem_center_eq_one_or_generator_sq
        z hzSecond with rfl | rfl
  · clear hz hzSecond
    revert j
    decide
  · clear hz hzSecond
    revert j
    decide

/-- The transported distinguished generator is central in the actual fixed
Sylow five-normalizer. -/
theorem alternatingSixFiveActualNormalizerCentralGenerator_mem_center :
    alternatingSixFiveActualNormalizerCentralGenerator ∈
      Subgroup.center
        (SylowNormalizer (alternatingSixUniversalCoverSylow 5)) := by
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp
      alternatingSixUniversalCoverCentralGenerator_mem_center z.1

/-- Every central element of the actual fixed normalizer is a natural power
of the transported distinguished generator. -/
theorem alternatingSixFiveActualNormalizer_center_generated
    (z : SylowNormalizer (alternatingSixUniversalCoverSylow 5))
    (hz :
      z ∈ Subgroup.center
        (SylowNormalizer (alternatingSixUniversalCoverSylow 5))) :
    ∃ n : ℕ,
      z = alternatingSixFiveActualNormalizerCentralGenerator ^ n := by
  let e :=
    alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer
  have hz' :
      e.symm z ∈
        Subgroup.center
          (Multiplicative (ZMod 3) ×
            CyclicFiveInversionSemidirect) :=
    MulEquivClass.apply_mem_center e.symm hz
  obtain ⟨n, hn⟩ :=
    alternatingSixFiveNormalizerSemidirect_center_generated
      (e.symm z) hz'
  refine ⟨n.1, ?_⟩
  calc
    z = e (e.symm z) := (e.apply_symm_apply z).symm
    _ =
        e
          (alternatingSixFiveNormalizerSemidirectCentralGenerator ^
            n.1) := by rw [hn]
    _ =
        e alternatingSixFiveNormalizerSemidirectCentralGenerator ^
          n.1 := map_pow e _ _
    _ =
        alternatingSixFiveActualNormalizerCentralGenerator ^ n.1 := by
      rw [
        alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer_centralGenerator
      ]

/-- The center of the actual fixed normalizer embeds into the ambient
center. -/
theorem alternatingSixFiveActualNormalizer_center_le_ambientCenter
    (z : SylowNormalizer (alternatingSixUniversalCoverSylow 5))
    (hz :
      z ∈ Subgroup.center
        (SylowNormalizer (alternatingSixUniversalCoverSylow 5))) :
    z.1 ∈ Subgroup.center AlternatingSixUniversalCover := by
  obtain ⟨n, rfl⟩ :=
    alternatingSixFiveActualNormalizer_center_generated z hz
  change
    alternatingSixUniversalCoverCentralGenerator ^ n ∈
      Subgroup.center AlternatingSixUniversalCover
  exact
    pow_mem
      alternatingSixUniversalCoverCentralGenerator_mem_center n

end GroupTheory
end McKayConjecture
