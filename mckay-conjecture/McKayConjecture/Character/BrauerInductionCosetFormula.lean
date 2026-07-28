/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Coset.Card
import McKayConjecture.Character.Induction

/-!
# The coset formula for induced class functions

The definition of class-function induction is normalized as a sum over all
ambient group elements.  Brauer's fixed-point argument is naturally a sum
over cosets.  This file proves the bridge between those two forms.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G : Type*} [Group G]

/-- An induction summand is unchanged when its indexing element is
multiplied on the right by an element of the inducing subgroup. -/
theorem inductionTerm_mul_subgroup
    (S : Subgroup G) (θ : ClassFunction S)
    (x g : G) (s : S) :
    inductionTerm S θ (x * s) g =
      inductionTerm S θ x g := by
  let y : G := x⁻¹ * g * x
  have heq :
      (x * (s : G))⁻¹ * g * (x * (s : G)) =
        (s : G)⁻¹ * y * s := by
    dsimp only [y]
    group
  have hmem :
      (x * (s : G))⁻¹ * g * (x * (s : G)) ∈ S ↔
        y ∈ S := by
    rw [heq]
    constructor
    · intro hs
      have hrestore :=
        S.mul_mem
          (S.mul_mem s.property hs)
          (S.inv_mem s.property)
      simpa [mul_assoc] using hrestore
    · intro hy
      exact
        S.mul_mem
          (S.mul_mem (S.inv_mem s.property) hy)
          s.property
  by_cases hy : y ∈ S
  · have hxy :
        (x * (s : G))⁻¹ * g * (x * (s : G)) ∈ S :=
      hmem.mpr hy
    have hx : x⁻¹ * g * x ∈ S := by
      simpa only [y] using hy
    rw [inductionTerm_of_mem S θ hxy,
      inductionTerm_of_mem S θ hx]
    have hconj :=
      ClassFunction.conj_apply θ
        (⟨y, hy⟩ : S) s⁻¹
    calc
      θ ⟨(x * (s : G))⁻¹ * g * (x * (s : G)), hxy⟩ =
          θ (s⁻¹ * (⟨y, hy⟩ : S) * (s⁻¹)⁻¹) := by
        apply congrArg θ
        apply Subtype.ext
        exact heq.trans (by simp)
      _ = θ ⟨y, hy⟩ := hconj
      _ = θ ⟨x⁻¹ * g * x, hx⟩ := by
        apply congrArg θ
        apply Subtype.ext
        rfl
  · have hxy :
        (x * (s : G))⁻¹ * g * (x * (s : G)) ∉ S :=
      fun h => hy (hmem.mp h)
    have hx : x⁻¹ * g * x ∉ S := by
      simpa only [y] using hy
    rw [inductionTerm_of_not_mem S θ hxy,
      inductionTerm_of_not_mem S θ hx]

noncomputable local instance brauerCosetQuotientFintype
    [Fintype G] (S : Subgroup G) :
    Fintype (G ⧸ S) :=
  Fintype.ofFinite _

/-- A concrete choice of coset representatives identifies the product of
the coset space and the subgroup with the ambient group. -/
noncomputable def quotientProdSubgroupEquiv
    (S : Subgroup G) :
    (G ⧸ S) × S ≃ G where
  toFun z := z.1.out * (z.2 : G)
  invFun x :=
    ⟨(x : G ⧸ S),
      ⟨(Quotient.out (x : G ⧸ S))⁻¹ * x,
        QuotientGroup.eq.mp
          (Quotient.out_eq' (x : G ⧸ S))⟩⟩
  left_inv z := by
    rcases z with ⟨q, s⟩
    have hq :
        ((q.out * (s : G) : G) : G ⧸ S) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ s.property,
        QuotientGroup.out_eq']
    apply Prod.ext
    · exact hq
    · apply Subtype.ext
      change
        (Quotient.out
            ((q.out * (s : G) : G) : G ⧸ S))⁻¹ *
            (q.out * (s : G)) =
          (s : G)
      rw [hq]
      simp
  right_inv x := by
    dsimp
    simp

/-- The induced value is the sum of its induction summand over right
cosets of the inducing subgroup. -/
theorem induce_apply_eq_sum_quotient
    [Fintype G]
    (S : Subgroup G) (θ : ClassFunction S)
    (g : G) :
    induce S θ g =
      ∑ q : G ⧸ S,
        inductionTerm S θ q.out g := by
  classical
  rw [induce_apply]
  let e : (G ⧸ S) × S ≃ G :=
    quotientProdSubgroupEquiv S
  have hsum :
      (∑ x : G, inductionTerm S θ x g) =
        (Nat.card S : ℂ) *
          ∑ q : G ⧸ S,
            inductionTerm S θ q.out g := by
    calc
      (∑ x : G, inductionTerm S θ x g) =
          ∑ z : (G ⧸ S) × S,
            inductionTerm S θ (e z) g := by
        exact
          (e.sum_comp
            (fun x : G =>
              inductionTerm S θ x g)).symm
      _ =
          ∑ q : G ⧸ S, ∑ s : S,
            inductionTerm S θ (q.out * (s : G)) g := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro q _hq
        apply Finset.sum_congr rfl
        intro s _hs
        rfl
      _ =
          ∑ q : G ⧸ S, ∑ _s : S,
            inductionTerm S θ q.out g := by
        apply Finset.sum_congr rfl
        intro q _hq
        apply Finset.sum_congr rfl
        intro s _hs
        exact inductionTerm_mul_subgroup S θ q.out g s
      _ =
          (Nat.card S : ℂ) *
            ∑ q : G ⧸ S,
              inductionTerm S θ q.out g := by
        simp only [Finset.sum_const, Finset.card_univ,
          ← Nat.card_eq_fintype_card, nsmul_eq_mul]
        rw [Finset.mul_sum]
  rw [hsum]
  have hcard :
      (Nat.card S : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

end ClassFunction
end McKayConjecture
