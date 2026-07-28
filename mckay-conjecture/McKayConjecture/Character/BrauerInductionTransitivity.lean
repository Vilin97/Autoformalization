/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionInductionPairing
import McKayConjecture.Character.InductionEquivalenceTransport

/-!
# Transitivity of class-function induction

For subgroups `K ≤ H ≤ G`, a class function on `K` can be transported to
the image of `K` in `G`.  Inducing first to `H` and then to `G` agrees with
inducing once from that image.  The statement is formulated for arbitrary
complex class functions, rather than only representation characters.

This is the transport step needed to turn the elementary formulas
constructed inside a centralizer into elementary induction terms for the
ambient group.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G : Type*} [Group G]

/-- Transport a class function on a subgroup of `H` to the image subgroup
inside the ambient group. -/
def mapSubtypeClassFunction
    (H : Subgroup G) (K : Subgroup H)
    (θ : ClassFunction K) :
    ClassFunction (K.map H.subtype) :=
  comapLinearEquiv
    (K.equivMapOfInjective
      H.subtype H.subtype_injective).symm θ

@[simp]
theorem mapSubtypeClassFunction_equivMapOfInjective
    (H : Subgroup G) (K : Subgroup H)
    (θ : ClassFunction K) (k : K) :
    mapSubtypeClassFunction H K θ
        (K.equivMapOfInjective
          H.subtype H.subtype_injective k) =
      θ k := by
  simp [mapSubtypeClassFunction]

/-- The inner induction summand, after multiplying the ambient summation
variable on the right by an element of `H`, is the corresponding summand
for the image of `K` in `G`. -/
private theorem inductionTerm_mapSubtype_mul
    (H : Subgroup G) (K : Subgroup H)
    (θ : ClassFunction K)
    (x g : G) (h : H)
    (hx : x⁻¹ * g * x ∈ H) :
    inductionTerm
        (K.map H.subtype)
        (mapSubtypeClassFunction H K θ)
        (x * (h : G)) g =
      inductionTerm K θ h
        ⟨x⁻¹ * g * x, hx⟩ := by
  let y : H := ⟨x⁻¹ * g * x, hx⟩
  have hconj :
      (x * (h : G))⁻¹ * g * (x * (h : G)) =
        H.subtype (h⁻¹ * y * h) := by
    change
      (x * (h : G))⁻¹ * g * (x * (h : G)) =
        ((h : G)⁻¹ * (x⁻¹ * g * x) * (h : G))
    group
  have hmem :
      (x * (h : G))⁻¹ * g * (x * (h : G)) ∈
          K.map H.subtype ↔
        h⁻¹ * y * h ∈ K := by
    rw [hconj]
    exact
      Subgroup.mem_map_iff_mem
        H.subtype_injective
  by_cases hk : h⁻¹ * y * h ∈ K
  · have hk' :
        (x * (h : G))⁻¹ * g * (x * (h : G)) ∈
          K.map H.subtype :=
      hmem.mpr hk
    rw [inductionTerm_of_mem _ _ hk',
      inductionTerm_of_mem _ _ hk]
    let k : K := ⟨h⁻¹ * y * h, hk⟩
    have himage :
        (⟨(x * (h : G))⁻¹ * g * (x * (h : G)),
            hk'⟩ : K.map H.subtype) =
          K.equivMapOfInjective
            H.subtype H.subtype_injective k := by
      apply Subtype.ext
      exact hconj
    rw [himage,
      mapSubtypeClassFunction_equivMapOfInjective]
  · have hk' :
        (x * (h : G))⁻¹ * g * (x * (h : G)) ∉
          K.map H.subtype :=
      fun hk' => hk (hmem.mp hk')
    rw [inductionTerm_of_not_mem _ _ hk',
      inductionTerm_of_not_mem _ _ hk]

/-- If the outer conjugate misses `H`, every corresponding summand for
the image of `K` also vanishes. -/
private theorem inductionTerm_mapSubtype_mul_eq_zero
    (H : Subgroup G) (K : Subgroup H)
    (θ : ClassFunction K)
    (x g : G) (h : H)
    (hx : x⁻¹ * g * x ∉ H) :
    inductionTerm
        (K.map H.subtype)
        (mapSubtypeClassFunction H K θ)
        (x * (h : G)) g =
      0 := by
  apply inductionTerm_of_not_mem
  intro hk
  have hkH :
      (x * (h : G))⁻¹ * g * (x * (h : G)) ∈ H :=
    Subgroup.map_subtype_le K hk
  have hrestore :=
    H.mul_mem
      (H.mul_mem h.property hkH)
      (H.inv_mem h.property)
  have hrestore_eq :
      (h : G) *
          ((x * (h : G))⁻¹ * g * (x * (h : G))) *
          (h : G)⁻¹ =
        x⁻¹ * g * x := by
    group
  apply hx
  rw [← hrestore_eq]
  exact hrestore

/-- One outer induction summand is the normalized sum of the ambient
summands obtained from the intermediate subgroup. -/
theorem inductionTerm_induce_eq_sum_mapSubtype
    (H : Subgroup G) (K : Subgroup H)
    [Fintype H]
    (θ : ClassFunction K)
    (x g : G) :
    inductionTerm H (induce K θ) x g =
      (Nat.card K : ℂ)⁻¹ *
        ∑ h : H,
          inductionTerm
            (K.map H.subtype)
            (mapSubtypeClassFunction H K θ)
            (x * (h : G)) g := by
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [inductionTerm_of_mem H _ hx,
      induce_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro h _hh
    exact
      (inductionTerm_mapSubtype_mul
        H K θ x g h hx).symm
  · rw [inductionTerm_of_not_mem H _ hx]
    have hzero :
        ∀ h : H,
          inductionTerm
              (K.map H.subtype)
              (mapSubtypeClassFunction H K θ)
              (x * (h : G)) g =
            0 :=
      fun h =>
        inductionTerm_mapSubtype_mul_eq_zero
          H K θ x g h hx
    simp_rw [hzero]
    simp

/-- **Transitivity of class-function induction.**  For `K ≤ H ≤ G`,
induction through `H` equals induction from the image of `K` in `G`, after
the canonical transport of the inducing class function. -/
theorem induce_induce_subgroup
    [Fintype G]
    (H : Subgroup G) (K : Subgroup H)
    [Fintype H]
    (θ : ClassFunction K) :
    induce H (induce K θ) =
      induce (K.map H.subtype)
        (mapSubtypeClassFunction H K θ) := by
  ext g
  rw [induce_apply, induce_apply]
  simp_rw [inductionTerm_induce_eq_sum_mapSubtype
    H K θ]
  rw [Finset.mul_sum]
  have hdouble :
      (∑ x : G,
          ∑ h : H,
            inductionTerm
              (K.map H.subtype)
              (mapSubtypeClassFunction H K θ)
              (x * (h : G)) g) =
        (Nat.card H : ℂ) *
          ∑ x : G,
            inductionTerm
              (K.map H.subtype)
              (mapSubtypeClassFunction H K θ)
              x g := by
    calc
      (∑ x : G,
          ∑ h : H,
            inductionTerm
              (K.map H.subtype)
              (mapSubtypeClassFunction H K θ)
              (x * (h : G)) g) =
          ∑ h : H,
            ∑ x : G,
              inductionTerm
                (K.map H.subtype)
                (mapSubtypeClassFunction H K θ)
                (x * (h : G)) g := by
        rw [Finset.sum_comm]
      _ =
          ∑ h : H,
            ∑ x : G,
              inductionTerm
                (K.map H.subtype)
                (mapSubtypeClassFunction H K θ)
                x g := by
        apply Finset.sum_congr rfl
        intro h _hh
        exact
          Equiv.sum_comp
            (Equiv.mulRight (h : G))
            (fun x : G =>
              inductionTerm
                (K.map H.subtype)
                (mapSubtypeClassFunction H K θ)
                x g)
      _ =
          (Nat.card H : ℂ) *
            ∑ x : G,
              inductionTerm
                (K.map H.subtype)
                (mapSubtypeClassFunction H K θ)
                x g := by
        simp only [Finset.sum_const, Finset.card_univ,
          ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  let F : G → ℂ :=
    fun x =>
      inductionTerm
        (K.map H.subtype)
        (mapSubtypeClassFunction H K θ)
        x g
  change
    (∑ x : G,
        (Nat.card H : ℂ)⁻¹ *
          ((Nat.card K : ℂ)⁻¹ *
            ∑ h : H, F (x * (h : G)))) =
      (Nat.card (K.map H.subtype) : ℂ)⁻¹ *
        ∑ x : G, F x
  calc
    _ =
        (Nat.card H : ℂ)⁻¹ *
          ((Nat.card K : ℂ)⁻¹ *
            ∑ x : G, ∑ h : H, F (x * (h : G))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ =
        (Nat.card H : ℂ)⁻¹ *
          ((Nat.card K : ℂ)⁻¹ *
            ((Nat.card H : ℂ) *
              ∑ x : G, F x)) := by
      rw [hdouble]
    _ =
        (Nat.card (K.map H.subtype) : ℂ)⁻¹ *
          ∑ x : G, F x := by
      rw [Nat.card_congr
        (K.equivMapOfInjective
          H.subtype H.subtype_injective).toEquiv]
      have hH : (Nat.card H : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      have hK : (Nat.card K : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      field_simp

end ClassFunction
end McKayConjecture
