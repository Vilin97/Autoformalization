/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteFactorCrossCharacteristicReduction

/-!
# Finite factors through a compatible coefficient reduction

The cross-characteristic argument does not require a prescribed embedding
between two finite fields.  It only needs a multiplicative reduction of the
finite complex roots together with a complex-valued character which recovers
their prime-to-`q` projection.  This file isolates that choice-free interface.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

open Representation

variable {G K : Type} [Group G] [CommGroup K]
variable (q n : ℕ) [Fact q.Prime] [NeZero n]

/-- Reconstruct a finite complex factor from its `q`-primary remainder and
any retained complex factor which is pointwise the prime-to-`q` projection. -/
theorem map_subtype_eq_primePrimaryRemainder_mul_retainedFactor
    (α : FactorSet G (rootsOfUnity n ℂ))
    (β : FactorSet G ℂˣ)
    (hretained :
      ∀ g h,
        β g h =
          ((primeToRootsProjection q n (α g h) :
            rootsOfUnity n ℂ) : ℂˣ)) :
    α.map (rootsOfUnity n ℂ).subtype =
      (α.primePrimaryRemainder q n).map
          ((rootsOfUnity n ℂ).subtype.comp
            ((primeToRootsProjection q n).ker.subtype)) *
        β := by
  apply FactorSet.ext
  intro g h
  change
    ((α g h : rootsOfUnity n ℂ) : ℂˣ) =
      (((α.primePrimaryRemainder q n g h :
            (primeToRootsProjection q n).ker) :
          rootsOfUnity n ℂ) : ℂˣ) *
        β g h
  rw [hretained]
  change
    (α g h : ℂˣ) =
      ((α g h *
          (primeToRootsProjection q n (α g h))⁻¹ :
        rootsOfUnity n ℂ) : ℂˣ) *
          (primeToRootsProjection q n (α g h) : ℂˣ)
  simp

/-- Reconstruct a finite complex factor from its `q`-primary remainder and
any coefficient reduction whose chosen complex character recovers the
prime-to-`q` projection. -/
theorem map_subtype_eq_primePrimaryRemainder_mul_compatibleReduction
    (α : FactorSet G (rootsOfUnity n ℂ))
    (r : rootsOfUnity n ℂ →* K)
    (κ : K →* ℂˣ)
    (hcompat :
      ∀ z : rootsOfUnity n ℂ,
        κ (r z) =
          ((primeToRootsProjection q n z :
            rootsOfUnity n ℂ) : ℂˣ)) :
    α.map (rootsOfUnity n ℂ).subtype =
      (α.primePrimaryRemainder q n).map
          ((rootsOfUnity n ℂ).subtype.comp
            ((primeToRootsProjection q n).ker.subtype)) *
        (α.map r).map κ := by
  apply
    map_subtype_eq_primePrimaryRemainder_mul_retainedFactor
      q n α ((α.map r).map κ)
  intro g h
  exact hcompat (α g h)

/-- If a retained complex factor is pointwise the prime-to-`q` projection
and is split, then the original finite complex factor class is
`q`-primary. -/
theorem exists_pow_nsmul_map_subtype_h2Class_eq_zero_of_retainedFactor
    (α : FactorSet G (rootsOfUnity n ℂ))
    (β : FactorSet G ℂˣ)
    (hretained :
      ∀ g h,
        β g h =
          ((primeToRootsProjection q n (α g h) :
            rootsOfUnity n ℂ) : ℂˣ))
    (hreduced :
      letI := trivialMulDistribMulAction G ℂˣ
      β.h2Class = 0) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G ℂˣ
      q ^ k •
          (α.map (rootsOfUnity n ℂ).subtype).h2Class =
        0 := by
  obtain ⟨k, hk⟩ :=
    exists_pow_nsmul_primePrimaryRemainder_h2Class_eq_zero
      q n α
  refine ⟨k, ?_⟩
  rw [map_subtype_eq_primePrimaryRemainder_mul_retainedFactor
      q n α β hretained,
    h2Class_mul, hreduced, add_zero]
  exact hk

/-- Splitting a compatible retained factor makes the original complex
factor class `q`-primary. -/
theorem exists_pow_nsmul_map_subtype_h2Class_eq_zero_of_compatibleReduction
    (α : FactorSet G (rootsOfUnity n ℂ))
    (r : rootsOfUnity n ℂ →* K)
    (κ : K →* ℂˣ)
    (hcompat :
      ∀ z : rootsOfUnity n ℂ,
        κ (r z) =
          ((primeToRootsProjection q n z :
            rootsOfUnity n ℂ) : ℂˣ))
    (hreduced :
      letI := trivialMulDistribMulAction G ℂˣ
      ((α.map r).map κ).h2Class = 0) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G ℂˣ
      q ^ k •
          (α.map (rootsOfUnity n ℂ).subtype).h2Class =
        0 := by
  apply
    exists_pow_nsmul_map_subtype_h2Class_eq_zero_of_retainedFactor
      q n α ((α.map r).map κ)
  · intro g h
    exact hcompat (α g h)
  · exact hreduced

end FactorSet
end CharacterTriple
end McKayConjecture
