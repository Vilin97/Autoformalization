/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetFiniteGroupAnnihilation
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionNormalizer
import Mathlib.GroupTheory.PGroup

/-!
# Pulling factor sets back from finite `p`-groups

The order of a finite group annihilates every factor-set class with
trivial coefficients.  This file records the functorial form needed for
projective Glauberman multiplicity arguments: if a factor set on an
arbitrary group is pulled back from a finite `p`-group, then a power of
`p` annihilates its cohomology class.

The proof is cochain-level.  The row-product coboundary on the finite
source group is simply precomposed with the given homomorphism, so no
restriction--corestriction API is required.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {G H A : Type}
variable [Group G] [Finite G] [Group H] [CommGroup A]

omit [Finite G] in
/-- A power coboundary remains a power coboundary after pulling the
factor set back along a group homomorphism. -/
theorem pow_comap_isMulCoboundary₂
    (α : FactorSet G A) (f : H →* G) (n : ℕ)
    (h :
      letI := trivialMulDistribMulAction G A
      groupCohomology.IsMulCoboundary₂
        (fun x : G × G ↦ α x.1 x.2 ^ n)) :
    letI := trivialMulDistribMulAction H A
    groupCohomology.IsMulCoboundary₂
      (fun x : H × H ↦ (α.comap f) x.1 x.2 ^ n) := by
  letI := trivialMulDistribMulAction G A
  obtain ⟨c, hc⟩ := h
  letI := trivialMulDistribMulAction H A
  refine ⟨fun x ↦ c (f x), ?_⟩
  intro x y
  change
    c (f y) / c (f (x * y)) * c (f x) =
      α (f x) (f y) ^ n
  have hxy := hc (f x) (f y)
  change
    c (f y) / c (f x * f y) * c (f x) =
      α (f x) (f y) ^ n at hxy
  simpa only [map_mul] using hxy

/-- The order of the finite source group annihilates the class of every
factor set pulled back from it, even when the target group is infinite. -/
theorem natCard_nsmul_comap_h2Class_eq_zero
    (α : FactorSet G A) (f : H →* G) :
    letI := trivialMulDistribMulAction H A
    Nat.card G • (α.comap f).h2Class = 0 := by
  apply
    (α.comap f).nsmul_h2Class_eq_zero_of_pow_isMulCoboundary₂
      (Nat.card G)
  exact
    pow_comap_isMulCoboundary₂
      α f (Nat.card G) α.pow_natCard_isMulCoboundary₂

/-- Pullback from a finite `p`-group gives an explicit `p`-power
annihilator for the pulled-back factor-set class. -/
theorem exists_pow_nsmul_comap_h2Class_eq_zero_of_isPGroup
    (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p G)
    (α : FactorSet G A) (f : H →* G) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction H A
      p ^ k • (α.comap f).h2Class = 0 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
  refine ⟨k, ?_⟩
  rw [← hk]
  exact α.natCard_nsmul_comap_h2Class_eq_zero f

/-- In particular, every factor-set class on a finite `p`-group is
`p`-primary. -/
theorem exists_pow_nsmul_h2Class_eq_zero_of_isPGroup
    (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p G)
    (α : FactorSet G A) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G A
      p ^ k • α.h2Class = 0 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
  refine ⟨k, ?_⟩
  rw [← hk]
  exact α.natCard_nsmul_h2Class_eq_zero

end FactorSet
end CharacterTriple
end McKayConjecture
