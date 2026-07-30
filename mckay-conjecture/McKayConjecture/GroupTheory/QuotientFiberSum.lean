/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Finite sums over quotient fibres

Let `H` be normal in `G`.  For `q : G ⧸ H`, right multiplication by
elements of `H` parametrizes the fibre of the quotient map over `q`:

`h ↦ Quotient.out q * h`.

Using these fibre equivalences together with `Equiv.sigmaFiberEquiv`
decomposes any finite sum over `G` into an outer sum over `G ⧸ H` and an
inner sum over `H`.
-/

noncomputable section

open scoped BigOperators

noncomputable local instance quotientFiberSumFintype
    (X : Type*) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace McKayConjecture
namespace GroupTheory

universe u v

variable {G : Type u} [Group G]
variable (H : Subgroup G) [H.Normal]

/-- Multiplying the chosen representative of `q` on the right by `H`
parametrizes the fibre of the quotient map over `q`. -/
def quotientFiberEquiv
    (q : G ⧸ H) :
    H ≃ {x : G // QuotientGroup.mk' H x = q} where
  toFun h := by
    refine ⟨Quotient.out q * (h : G), ?_⟩
    rw [map_mul]
    have hq :
        QuotientGroup.mk' H (Quotient.out q) = q :=
      Quotient.out_eq q
    have hh :
        QuotientGroup.mk' H (h : G) = 1 :=
      (QuotientGroup.eq_one_iff (h : G)).mpr
        h.property
    rw [hq, hh, mul_one]
  invFun x := by
    refine ⟨(Quotient.out q)⁻¹ * (x : G), ?_⟩
    apply
      (QuotientGroup.eq_one_iff
        ((Quotient.out q)⁻¹ * (x : G))).mp
    change
      QuotientGroup.mk' H
          ((Quotient.out q)⁻¹ * (x : G)) =
        1
    rw [map_mul, map_inv, x.property]
    have hq :
        QuotientGroup.mk' H (Quotient.out q) = q :=
      Quotient.out_eq q
    rw [hq]
    simp
  left_inv h := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

@[simp]
theorem quotientFiberEquiv_apply_coe
    (q : G ⧸ H) (h : H) :
    ((quotientFiberEquiv H q h :
      {x : G // QuotientGroup.mk' H x = q}) : G) =
      Quotient.out q * (h : G) :=
  rfl

@[simp]
theorem quotientFiberEquiv_symm_apply_coe
    (q : G ⧸ H)
    (x : {x : G // QuotientGroup.mk' H x = q}) :
    (((quotientFiberEquiv H q).symm x : H) : G) =
      (Quotient.out q)⁻¹ * (x : G) :=
  rfl

/-- Reindex a finite sum over a group by its quotient fibres and the
normal subgroup. -/
theorem sum_eq_sum_quotient_mul_subgroup
    [Finite G]
    {M : Type v} [AddCommMonoid M]
    (f : G → M) :
    (∑ x : G, f x) =
      ∑ q : G ⧸ H, ∑ h : H,
        f (Quotient.out q * (h : G)) := by
  calc
    (∑ x : G, f x) =
        ∑ z :
          Σ q : G ⧸ H,
            {x : G // QuotientGroup.mk' H x = q},
          f z.2 := by
      exact
        (Equiv.sum_comp
          (Equiv.sigmaFiberEquiv
            (QuotientGroup.mk' H))
          f).symm
    _ =
        ∑ q : G ⧸ H,
          ∑ x :
              {x : G //
                QuotientGroup.mk' H x = q},
            f x := by
      exact
        Fintype.sum_sigma
          (fun z :
            Σ q : G ⧸ H,
              {x : G //
                QuotientGroup.mk' H x = q} =>
            f z.2)
    _ =
        ∑ q : G ⧸ H, ∑ h : H,
          f (Quotient.out q * (h : G)) := by
      apply Finset.sum_congr rfl
      intro q _
      simpa only [quotientFiberEquiv_apply_coe] using
        (Equiv.sum_comp
          (quotientFiberEquiv H q)
          (fun x :
            {x : G //
              QuotientGroup.mk' H x = q} =>
            f x)).symm

end GroupTheory
end McKayConjecture
