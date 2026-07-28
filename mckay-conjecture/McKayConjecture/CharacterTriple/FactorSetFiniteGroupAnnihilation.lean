/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveFactorDeterminantCoboundary

/-!
# Finite-group annihilation of factor-set cohomology

For a factor set on a finite group, multiplying the cocycle identity over the
last variable gives an explicit coboundary for the pointwise `|G|`th power.
Thus the group order annihilates every `H²` class represented by a factor
set with trivial coefficient action.

This supplies the low-degree finite-group annihilation result directly,
without requiring a restriction-corestriction API in group cohomology.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {G A : Type} [Group G] [CommGroup A]

/-- The product of one row of a factor set. -/
def rowProduct [Fintype G] (α : FactorSet G A) (g : G) : A :=
  ∏ k : G, α g k

/-- Multiplication by a fixed group element permutes a factor-set row
product. -/
theorem prod_mul_left_row [Fintype G]
    (α : FactorSet G A) (g h : G) :
    (∏ k : G, α g (h * k)) =
      ∏ k : G, α g k := by
  exact
    Fintype.prod_bijective
      (h * ·) (Group.mulLeft_bijective h)
      (fun k ↦ α g (h * k)) (fun k ↦ α g k)
      (fun _ ↦ rfl)

/-- The factor set raised pointwise to the group order is the coboundary of
the row-product cochain. -/
theorem pow_card_isMulCoboundary₂ [Fintype G]
    (α : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    groupCohomology.IsMulCoboundary₂
      (fun x : G × G ↦ α x.1 x.2 ^ Fintype.card G) := by
  letI := trivialMulDistribMulAction G A
  refine ⟨α.rowProduct, ?_⟩
  intro g h
  have hcocycleProduct :
      (∏ k : G, α (g * h) k * α g h) =
        ∏ k : G, α h k * α g (h * k) := by
    apply Finset.prod_congr rfl
    intro k _
    exact α.cocycle g h k
  rw [Finset.prod_mul_distrib,
    Finset.prod_mul_distrib] at hcocycleProduct
  simp only [Finset.prod_const, Finset.card_univ] at hcocycleProduct
  rw [α.prod_mul_left_row g h] at hcocycleProduct
  change
    α.rowProduct (g * h) *
        α g h ^ Fintype.card G =
      α.rowProduct h * α.rowProduct g at hcocycleProduct
  change
    α.rowProduct h / α.rowProduct (g * h) *
        α.rowProduct g =
      α g h ^ Fintype.card G
  calc
    α.rowProduct h / α.rowProduct (g * h) *
          α.rowProduct g =
        (α.rowProduct h * α.rowProduct g) /
          α.rowProduct (g * h) := by
            simp only [div_eq_mul_inv]
            ac_rfl
    _ =
        (α.rowProduct (g * h) *
            α g h ^ Fintype.card G) /
          α.rowProduct (g * h) := by
            rw [← hcocycleProduct]
    _ = α g h ^ Fintype.card G := by
          simp

/-- For a finite group, the pointwise `Nat.card G`th power of every factor
set is a multiplicative two-coboundary. -/
theorem pow_natCard_isMulCoboundary₂ [Finite G]
    (α : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    groupCohomology.IsMulCoboundary₂
      (fun x : G × G ↦ α x.1 x.2 ^ Nat.card G) := by
  letI := Fintype.ofFinite G
  simpa only [Nat.card_eq_fintype_card] using
    α.pow_card_isMulCoboundary₂

/-- The order of a finite group annihilates every factor-set class in
`H²` with trivial coefficient action. -/
theorem natCard_nsmul_h2Class_eq_zero [Finite G]
    (α : FactorSet G A) :
    letI := trivialMulDistribMulAction G A
    Nat.card G • α.h2Class = 0 := by
  exact
    α.nsmul_h2Class_eq_zero_of_pow_isMulCoboundary₂
      (Nat.card G)
      α.pow_natCard_isMulCoboundary₂

end FactorSet
end CharacterTriple
end McKayConjecture
