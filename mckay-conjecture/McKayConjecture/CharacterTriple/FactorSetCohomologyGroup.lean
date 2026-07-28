/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCohomology
import McKayConjecture.CharacterTriple.FactorSetGroup

/-!
# Group operations on factor-set cohomology classes

Pointwise multiplication and inversion of multiplicative factor sets become
addition and negation in the additive second cohomology group.  These lemmas
make factor quotients usable as explicit representatives of differences of
projective obstruction classes.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {G A : Type} [Group G] [CommGroup A]

/-- The mathlib cocycle associated with a pointwise product is the sum of
the two associated additive cocycles. -/
theorem toMathlibCocycle_mul (α β : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    (α * β).toMathlibCocycle =
      α.toMathlibCocycle + β.toMathlibCocycle := by
  letI := trivialMulDistribMulAction G A
  ext x
  rfl

/-- The mathlib cocycle associated with a pointwise inverse is the negative
of the associated additive cocycle. -/
theorem toMathlibCocycle_inv (α : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    α⁻¹.toMathlibCocycle = -α.toMathlibCocycle := by
  letI := trivialMulDistribMulAction G A
  ext x
  rfl

/-- Pointwise multiplication of factor sets becomes addition in `H²`. -/
theorem h2Class_mul (α β : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    (α * β).h2Class = α.h2Class + β.h2Class := by
  letI := trivialMulDistribMulAction G A
  change
    groupCohomology.H2π
        (Rep.ofMulDistribMulAction G A)
        (α * β).toMathlibCocycle =
      groupCohomology.H2π
          (Rep.ofMulDistribMulAction G A)
          α.toMathlibCocycle +
        groupCohomology.H2π
          (Rep.ofMulDistribMulAction G A)
          β.toMathlibCocycle
  rw [toMathlibCocycle_mul, map_add]

/-- Pointwise inversion of a factor set becomes negation in `H²`. -/
theorem h2Class_inv (α : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    α⁻¹.h2Class = -α.h2Class := by
  letI := trivialMulDistribMulAction G A
  change
    groupCohomology.H2π
        (Rep.ofMulDistribMulAction G A)
        α⁻¹.toMathlibCocycle =
      -groupCohomology.H2π
        (Rep.ofMulDistribMulAction G A)
        α.toMathlibCocycle
  rw [toMathlibCocycle_inv, map_neg]

/-- The class of the pointwise quotient `α * β⁻¹` is the difference of the
two factor-set classes. -/
theorem h2Class_mul_inv (α β : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    (α * β⁻¹).h2Class = α.h2Class - β.h2Class := by
  letI := trivialMulDistribMulAction G A
  rw [h2Class_mul, h2Class_inv, sub_eq_add_neg]

/-- The pointwise quotient has zero class exactly when the original two
factor sets have equal `H²` classes. -/
theorem h2Class_mul_inv_eq_zero_iff (α β : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    (α * β⁻¹).h2Class = 0 ↔ α.h2Class = β.h2Class := by
  letI := trivialMulDistribMulAction G A
  rw [h2Class_mul_inv, sub_eq_zero]

end FactorSet
end CharacterTriple
end McKayConjecture
