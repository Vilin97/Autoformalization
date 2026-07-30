/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Index

/-!
# Subgroup indices from a set-product decomposition

Let `H` and `K` be subgroups of `G`.  If every element of `G` can be
written as `k h` with `k ∈ K` and `h ∈ H`, then inclusion of `K` in
`G` induces a bijection

`K / (H ∩ K) ≃ G / H`.

No normality assumption is needed.  This is the exact coset calculation
used in the proper branch of the Okuyama--Wajima induction, where the
intermediate subgroup is not asserted to be normal.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

open scoped Pointwise

variable {G : Type u} [Group G]

/-- Inclusion of `K` induces the canonical map from its quotient by the
internal copy of `H ∩ K` to the ambient quotient by `H`. -/
def subgroupQuotientToAmbientQuotient
    (H K : Subgroup G) :
    K ⧸ H.subgroupOf K → G ⧸ H :=
  Quotient.map' K.subtype fun a b ↦ by
    simp_rw [QuotientGroup.leftRel_eq]
    exact id

@[simp]
theorem subgroupQuotientToAmbientQuotient_mk
    (H K : Subgroup G) (k : K) :
    subgroupQuotientToAmbientQuotient H K
        (QuotientGroup.mk k) =
      QuotientGroup.mk (k : G) :=
  rfl

/-- The quotient map induced by subgroup inclusion is always injective. -/
theorem subgroupQuotientToAmbientQuotient_injective
    (H K : Subgroup G) :
    Function.Injective
      (subgroupQuotientToAmbientQuotient H K) := by
  refine Quotient.ind₂' ?_
  intro a b hab
  simpa only [subgroupQuotientToAmbientQuotient,
    Quotient.map'_mk'', QuotientGroup.eq] using! hab

/-- A set-product decomposition `G = K H` makes the quotient map induced
by `K ↪ G` surjective. -/
theorem subgroupQuotientToAmbientQuotient_surjective
    (H K : Subgroup G)
    (hproduct :
      (K : Set G) * (H : Set G) =
        (⊤ : Subgroup G)) :
    Function.Surjective
      (subgroupQuotientToAmbientQuotient H K) := by
  refine Quotient.ind' ?_
  intro g
  have hg :
      g ∈ (K : Set G) * (H : Set G) := by
    rw [hproduct]
    trivial
  obtain ⟨k, hk, h, hh, hkh⟩ := hg
  let kK : K := ⟨k, hk⟩
  refine ⟨QuotientGroup.mk kK, ?_⟩
  rw [subgroupQuotientToAmbientQuotient_mk]
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  rw [← hkh]
  change k⁻¹ * (k * h) ∈ H
  simpa [mul_assoc] using hh

/-- If `G = K H` as a set product, then left cosets of `H ∩ K` in `K`
are canonically equivalent to left cosets of `H` in `G`. -/
def subgroupQuotientEquivAmbientQuotient
    (H K : Subgroup G)
    (hproduct :
      (K : Set G) * (H : Set G) =
        (⊤ : Subgroup G)) :
    K ⧸ H.subgroupOf K ≃ G ⧸ H :=
  Equiv.ofBijective
    (subgroupQuotientToAmbientQuotient H K)
    ⟨subgroupQuotientToAmbientQuotient_injective H K,
      subgroupQuotientToAmbientQuotient_surjective
        H K hproduct⟩

@[simp]
theorem subgroupQuotientEquivAmbientQuotient_mk
    (H K : Subgroup G)
    (hproduct :
      (K : Set G) * (H : Set G) =
        (⊤ : Subgroup G))
    (k : K) :
    subgroupQuotientEquivAmbientQuotient H K hproduct
        (QuotientGroup.mk k) =
      QuotientGroup.mk (k : G) :=
  rfl

/-- Index form of a set-product decomposition:
`G = K H` implies `[G : H] = [K : H ∩ K]`. -/
theorem index_eq_relIndex_of_mul_eq_top
    (H K : Subgroup G)
    (hproduct :
      (K : Set G) * (H : Set G) =
        (⊤ : Subgroup G)) :
    H.index = H.relIndex K := by
  rw [Subgroup.index_eq_card, Subgroup.relIndex]
  exact
    (Nat.card_congr
      (subgroupQuotientEquivAmbientQuotient
        H K hproduct)).symm

end GroupTheory
end McKayConjecture
