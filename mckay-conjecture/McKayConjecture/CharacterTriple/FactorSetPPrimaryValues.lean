/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveFactorDeterminantCoboundary
import Mathlib.GroupTheory.PGroup

/-!
# Factor sets with `p`-primary values

A factor set whose values are uniformly killed by a power of `p`
represents a `p`-primary class in `H²`.  In particular this applies when
the factor set is obtained by mapping a factor set valued in a finite
commutative `p`-group into the desired scalar group.

This is the coefficient-side alternative to factoring the base group
through a `p`-group.  It is the natural target when finite-order
projective operators show that their scalar mismatch consists of
`p`-power roots of unity.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {G A B : Type}
variable [Group G] [CommGroup A] [CommGroup B]

/-- Map the coefficients of a factor set along a commutative-group
homomorphism. -/
def map (α : FactorSet G A) (f : A →* B) :
    FactorSet G B where
  toFun x y := f (α x y)
  cocycle' x y z := by
    simpa only [map_mul] using congrArg f (α.cocycle x y z)

@[simp]
theorem map_apply
    (α : FactorSet G A) (f : A →* B)
    (x y : G) :
    α.map f x y = f (α x y) :=
  rfl

/-- A uniform exponent for all factor-set values gives the same
annihilator for the represented `H²` class. -/
theorem nsmul_h2Class_eq_zero_of_forall_pow_eq_one
    (α : FactorSet G A) (n : ℕ)
    (hvalues : ∀ x y : G, α x y ^ n = 1) :
    letI := trivialMulDistribMulAction G A
    n • α.h2Class = 0 := by
  apply α.nsmul_h2Class_eq_zero_of_pow_isMulCoboundary₂ n
  letI := trivialMulDistribMulAction G A
  refine ⟨fun _ ↦ 1, ?_⟩
  intro x y
  simpa using (hvalues x y).symm

/-- Mapping a factor set out of a finite commutative `p`-group produces
a `p`-primary scalar factor class. -/
theorem exists_pow_nsmul_map_h2Class_eq_zero_of_isPGroup
    [Finite A]
    (p : ℕ)
    (hA : IsPGroup p A)
    (α : FactorSet G A)
    (f : A →* B) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G B
      p ^ k • (α.map f).h2Class = 0 := by
  obtain ⟨k, hk⟩ :=
    isPGroup_iff_exists_pow_pow_eq_one.mp hA
  refine ⟨k,
    (α.map f).nsmul_h2Class_eq_zero_of_forall_pow_eq_one
      (p ^ k) ?_⟩
  intro x y
  rw [map_apply, ← map_pow, hk, map_one]

end FactorSet
end CharacterTriple
end McKayConjecture
