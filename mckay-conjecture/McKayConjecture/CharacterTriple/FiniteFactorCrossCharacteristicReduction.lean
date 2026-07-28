/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CrossCharacteristicCoefficientReduction
import McKayConjecture.CharacterTriple.FactorSetCohomologyGroup
import McKayConjecture.CharacterTriple.FactorSetPPrimaryValues

/-!
# Cross-characteristic reduction of finite factor sets

A factor set valued in complex `n`th roots of unity admits a canonical
coefficient-level reduction to a concrete finite field of
characteristic `q`.  Pointwise, the original factor is the product of

* a factor valued in a finite `q`-group, and
* the chosen complex lift of the reduced finite-field factor.

Thus this construction completely resolves the scalar part of
cross-characteristic reduction.  It deliberately does not claim to
reduce the projective operators themselves; that further step requires
a stable integral lattice.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

open Representation

universe u

section CoefficientReduction

variable {G : Type u} [Group G]
variable (q n : ℕ) [Fact q.Prime] [NeZero n]

/-- The finite-field factor set obtained by applying the canonical
prime-to-`q` coefficient reduction pointwise. -/
def crossCharacteristicReduction
    (α : FactorSet G (rootsOfUnity n ℂ)) :
    FactorSet G (PrimeToCoefficientField q n)ˣ :=
  α.map (crossCharacteristicCoefficientReduction q n)

@[simp]
theorem crossCharacteristicReduction_apply
    (α : FactorSet G (rootsOfUnity n ℂ))
    (g h : G) :
    α.crossCharacteristicReduction q n g h =
      crossCharacteristicCoefficientReduction q n (α g h) :=
  rfl

/-- The factor set containing precisely the discarded `q`-primary
coefficient component. -/
def primePrimaryRemainder
    (α : FactorSet G (rootsOfUnity n ℂ)) :
    FactorSet G (primeToRootsProjection q n).ker :=
  α.map (primePrimaryRootsRemainderToKernel q n)

@[simp]
theorem primePrimaryRemainder_apply
    (α : FactorSet G (rootsOfUnity n ℂ))
    (g h : G) :
    α.primePrimaryRemainder q n g h =
      primePrimaryRootsRemainderToKernel q n (α g h) :=
  rfl

/-- The remainder coefficient group is a finite `q`-group. -/
theorem primePrimaryRemainder_coefficient_isPGroup :
    IsPGroup q (primeToRootsProjection q n).ker :=
  primeToRootsProjection_ker_isPGroup q n

/-- Exact pointwise reconstruction of the original complex factor from
its `q`-primary remainder and its reduced finite-field value. -/
theorem primePrimaryRemainder_mul_lifted_crossCharacteristicReduction
    (α : FactorSet G (rootsOfUnity n ℂ))
    (g h : G) :
    (((α.primePrimaryRemainder q n g h :
          (primeToRootsProjection q n).ker) :
        rootsOfUnity n ℂ) : ℂˣ) *
      finiteFieldUnitsToComplexUnits
        (PrimeToCoefficientField q n)
        (α.crossCharacteristicReduction q n g h) =
      ((α g h : rootsOfUnity n ℂ) : ℂˣ) :=
  primePrimaryRemainder_mul_lifted_reduction q n (α g h)

/-- Bundled form of the exact coefficient decomposition. -/
theorem map_subtype_eq_primePrimaryRemainder_mul_liftedReduction
    (α : FactorSet G (rootsOfUnity n ℂ)) :
    α.map (rootsOfUnity n ℂ).subtype =
      (α.primePrimaryRemainder q n).map
          ((rootsOfUnity n ℂ).subtype.comp
            ((primeToRootsProjection q n).ker.subtype)) *
        (α.crossCharacteristicReduction q n).map
          (finiteFieldUnitsToComplexUnits
            (PrimeToCoefficientField q n)) := by
  apply FactorSet.ext
  intro g h
  change
    ((α g h : rootsOfUnity n ℂ) : ℂˣ) =
      (((α.primePrimaryRemainder q n g h :
            (primeToRootsProjection q n).ker) :
          rootsOfUnity n ℂ) : ℂˣ) *
        finiteFieldUnitsToComplexUnits
          (PrimeToCoefficientField q n)
          (α.crossCharacteristicReduction q n g h)
  exact
    (primePrimaryRemainder_mul_lifted_crossCharacteristicReduction
      q n α g h).symm

end CoefficientReduction

variable {G : Type} [Group G]
variable (q n : ℕ) [Fact q.Prime] [NeZero n]

/-- After inclusion in complex units, the discarded remainder
represents a `q`-primary cohomology class. -/
theorem exists_pow_nsmul_primePrimaryRemainder_h2Class_eq_zero
    (α : FactorSet G (rootsOfUnity n ℂ)) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G ℂˣ
      q ^ k •
          ((α.primePrimaryRemainder q n).map
            ((rootsOfUnity n ℂ).subtype.comp
              ((primeToRootsProjection q n).ker.subtype))).h2Class =
        0 := by
  exact
    exists_pow_nsmul_map_h2Class_eq_zero_of_isPGroup
      q
      (primePrimaryRemainder_coefficient_isPGroup q n)
      (α.primePrimaryRemainder q n)
      ((rootsOfUnity n ℂ).subtype.comp
        ((primeToRootsProjection q n).ker.subtype))

/-- If the retained finite-field factor becomes cohomologically
trivial after the chosen complex embedding, then the original complex
factor class is `q`-primary.  This is the coefficient-level conclusion
needed after a modular normalizer argument. -/
theorem exists_pow_nsmul_map_subtype_h2Class_eq_zero_of_reduction
    (α : FactorSet G (rootsOfUnity n ℂ))
    (hreduced :
      letI := trivialMulDistribMulAction G ℂˣ
      ((α.crossCharacteristicReduction q n).map
        (finiteFieldUnitsToComplexUnits
          (PrimeToCoefficientField q n))).h2Class =
        0) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G ℂˣ
      q ^ k •
          (α.map (rootsOfUnity n ℂ).subtype).h2Class =
        0 := by
  obtain ⟨k, hk⟩ :=
    exists_pow_nsmul_primePrimaryRemainder_h2Class_eq_zero
      q n α
  refine ⟨k, ?_⟩
  rw [map_subtype_eq_primePrimaryRemainder_mul_liftedReduction
      q n α,
    h2Class_mul, hreduced, add_zero]
  exact hk

end FactorSet
end CharacterTriple
end McKayConjecture
