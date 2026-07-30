/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GoodElement

/-!
# Gallagher commutator fibres and quotient centralizers

Let `N ◁ A`.  For fixed `x : A`, the Gallagher commutator condition

`x⁻¹ * y⁻¹ * x * y ∈ N`

says exactly that the image of `y` centralizes the image of `x` in `A / N`.
Consequently its fibre in `A` is canonically equivalent to
`goodElementCentralizer N (QuotientGroup.mk' N x)`.

This file records the membership equivalence, its identity-on-elements
subtype equivalence, and reindexing lemmas for both a single filtered sum
and the corresponding filtered double sum.
-/

noncomputable section

open scoped BigOperators

local instance goodElementCommutatorFiberPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

variable {A : Type u} [Group A]
variable (N : Subgroup A) [N.Normal]

/-- The Gallagher commutator lies in `N` exactly when the right variable
lies in the preimage of the quotient centralizer of the left variable. -/
theorem gallagherCommutator_mem_iff_mem_goodElementCentralizer
    (x y : A) :
    x⁻¹ * y⁻¹ * x * y ∈ N ↔
      y ∈
        goodElementCentralizer N
          (QuotientGroup.mk' N x) := by
  rw [← QuotientGroup.eq_one_iff
    (x⁻¹ * y⁻¹ * x * y)]
  change
    QuotientGroup.mk' N (x⁻¹ * y⁻¹ * x * y) = 1 ↔
      QuotientGroup.mk' N y ∈
        Subgroup.centralizer
          ({QuotientGroup.mk' N x} : Set (A ⧸ N))
  rw [Subgroup.mem_centralizer_singleton_iff]
  simpa only [map_mul, map_inv, mul_inv_rev, mul_assoc] using
    (inv_mul_eq_one
      (a :=
        QuotientGroup.mk' N y *
          QuotientGroup.mk' N x)
      (b :=
        QuotientGroup.mk' N x *
          QuotientGroup.mk' N y))

/-- The fibre cut out by the Gallagher commutator condition is the
quotient-centralizer preimage. -/
def gallagherCommutatorFiberEquiv
    (x : A) :
    {y : A // x⁻¹ * y⁻¹ * x * y ∈ N} ≃
      goodElementCentralizer N
        (QuotientGroup.mk' N x) where
  toFun y :=
    ⟨y,
      (gallagherCommutator_mem_iff_mem_goodElementCentralizer
        N x y).mp y.property⟩
  invFun y :=
    ⟨y,
      (gallagherCommutator_mem_iff_mem_goodElementCentralizer
        N x y).mpr y.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp]
theorem gallagherCommutatorFiberEquiv_apply_coe
    (x : A)
    (y : {y : A // x⁻¹ * y⁻¹ * x * y ∈ N}) :
    ((gallagherCommutatorFiberEquiv N x y :
      goodElementCentralizer N
        (QuotientGroup.mk' N x)) : A) =
      y :=
  rfl

@[simp]
theorem gallagherCommutatorFiberEquiv_symm_apply_coe
    (x : A)
    (y :
      goodElementCentralizer N
        (QuotientGroup.mk' N x)) :
    (((gallagherCommutatorFiberEquiv N x).symm y :
      {y : A // x⁻¹ * y⁻¹ * x * y ∈ N}) : A) =
      y :=
  rfl

/-- Reindex a finite sum over the Gallagher commutator fibre by the
quotient-centralizer preimage. -/
theorem
    sum_gallagherCommutatorFiber_eq_sum_goodElementCentralizer
    [Fintype A]
    {M : Type v} [AddCommMonoid M]
    (x : A) (f : A → M) :
    (∑ y :
        {y : A // x⁻¹ * y⁻¹ * x * y ∈ N},
      f y) =
      ∑ y :
          goodElementCentralizer N
            (QuotientGroup.mk' N x),
        f y := by
  simpa only [
    gallagherCommutatorFiberEquiv_apply_coe
  ] using
    Equiv.sum_comp
      (gallagherCommutatorFiberEquiv N x)
      (fun y :
        goodElementCentralizer N
          (QuotientGroup.mk' N x) =>
        f y)

/-- Reindex a filtered sum over the right variable by the preimage of the
quotient centralizer. -/
theorem
    sum_ite_gallagherCommutator_mem_eq_sum_goodElementCentralizer
    [Fintype A]
    {M : Type v} [AddCommMonoid M]
    (x : A) (f : A → M) :
    (∑ y : A,
      if x⁻¹ * y⁻¹ * x * y ∈ N then f y else 0) =
      ∑ y :
          goodElementCentralizer N
            (QuotientGroup.mk' N x),
        f y := by
  calc
    (∑ y : A,
      if x⁻¹ * y⁻¹ * x * y ∈ N then f y else 0) =
        ∑ y ∈
          Finset.univ.filter
            (fun y : A =>
              x⁻¹ * y⁻¹ * x * y ∈ N),
          f y := by
      symm
      exact Finset.sum_filter _ _
    _ =
        ∑ y :
          {y : A // x⁻¹ * y⁻¹ * x * y ∈ N},
          f y := by
      exact Finset.sum_subtype _ (by simp) f
    _ = _ :=
      sum_gallagherCommutatorFiber_eq_sum_goodElementCentralizer
        N x f

/-- Reindex the filtered double Gallagher commutator sum one left variable
at a time by its quotient-centralizer preimage. -/
theorem
    sum_sum_ite_gallagherCommutator_mem_eq_sum_goodElementCentralizer
    [Fintype A]
    {M : Type v} [AddCommMonoid M]
    (f : A → A → M) :
    (∑ x : A, ∑ y : A,
      if x⁻¹ * y⁻¹ * x * y ∈ N
        then f x y
        else 0) =
      ∑ x : A,
        ∑ y :
            goodElementCentralizer N
              (QuotientGroup.mk' N x),
          f x y := by
  apply Finset.sum_congr rfl
  intro x _
  exact
    sum_ite_gallagherCommutator_mem_eq_sum_goodElementCentralizer
      N x (f x)

end IrreducibleCharacter
end McKayConjecture
