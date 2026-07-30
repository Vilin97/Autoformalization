/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Sylow
import McKayConjecture.Character.FiniteFiberSum
import McKayConjecture.Character.GoodElement
import McKayConjecture.GroupTheory.ConjugacyClassCard

/-!
# The class sum for good quotient elements

For a predicate on the conjugacy classes of a finite group, summing the
centralizer order over the elements in the selected classes gives one copy
of the group order per selected class.  This follows by grouping the sum
through `ConjClasses.mk` and applying orbit--stabilizer on each fibre.

For a normal subgroup `N ◁ A`, `goodElementCentralizer N q` is the preimage
in `A` of the centralizer of `q ∈ A / N`.  Its order is therefore
`|N| * |C_{A/N}(q)|`.  Applying the generic class sum to Gallagher-good
classes gives

`∑ q, if q is good then |goodElementCentralizer N q| else 0
  = |A| * |GoodQuotientConjugacyClasses N θ|`.
-/

noncomputable section

open scoped BigOperators

local instance goodElementClassSumPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

namespace McKayConjecture

/-- The fibre of `ConjClasses.mk` over `c` is the carrier of `c`. -/
private def conjugacyClassFiberEquiv
    {H : Type} [Group H] (c : ConjClasses H) :
    {x : H // ConjClasses.mk x = c} ≃ c.carrier where
  toFun x :=
    ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mpr x.property⟩
  invFun x :=
    ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Centralizers of conjugate elements have the same finite cardinality. -/
theorem natCard_centralizer_eq_of_isConj
    {H : Type} [Group H] [Finite H]
    {x y : H} (hxy : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set H)) =
      Nat.card (Subgroup.centralizer ({y} : Set H)) := by
  have hclass : ConjClasses.mk x = ConjClasses.mk y :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr hxy
  have hx := card_conjClass_mul_card_centralizer x
  have hy := card_conjClass_mul_card_centralizer y
  rw [hclass] at hx
  letI : Nonempty (ConjClasses.mk y).carrier :=
    ⟨⟨y, ConjClasses.mem_carrier_mk⟩⟩
  exact
    Nat.eq_of_mul_eq_mul_left Nat.card_pos
      (hx.trans hy.symm)

/-- A centralizer-weighted sum over any collection of conjugacy classes
equals the group order times the number of selected classes. -/
theorem sum_natCard_centralizer_over_classPredicate
    {H : Type} [Group H] [Fintype H]
    (P : ConjClasses H → Prop) :
    (∑ x : H,
      if P (ConjClasses.mk x) then
        Nat.card (Subgroup.centralizer ({x} : Set H))
      else 0) =
      Nat.card H * Nat.card {c : ConjClasses H // P c} := by
  classical
  let representative : ConjClasses H → H :=
    Quotient.out
  let f : H → ℕ := fun x =>
    if P (ConjClasses.mk x) then
      Nat.card (Subgroup.centralizer ({x} : Set H))
    else 0
  have hrepresentative (c : ConjClasses H) :
      ConjClasses.mk (representative c) = c :=
    Quotient.out_eq c
  have hf (x : H) :
      f x = f (representative (ConjClasses.mk x)) := by
    have hclass :=
      hrepresentative (ConjClasses.mk x)
    have hconj :
        IsConj x (representative (ConjClasses.mk x)) :=
      ConjClasses.mk_eq_mk_iff_isConj.mp hclass.symm
    simp only [f]
    rw [hclass, natCard_centralizer_eq_of_isConj hconj]
  calc
    (∑ x : H,
      if P (ConjClasses.mk x) then
        Nat.card (Subgroup.centralizer ({x} : Set H))
      else 0) =
        ∑ x : H, f x :=
      rfl
    _ =
        ∑ c : ConjClasses H,
          Fintype.card {x : H // ConjClasses.mk x = c} •
            f (representative c) :=
      sum_eq_sum_card_fiber_nsmul
        ConjClasses.mk representative f hf
    _ =
        ∑ c : ConjClasses H,
          if P c then Nat.card H else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [show
        Fintype.card {x : H // ConjClasses.mk x = c} =
          Nat.card {x : H // ConjClasses.mk x = c} by
        exact (Nat.card_eq_fintype_card).symm]
      rw [Nat.card_congr (conjugacyClassFiberEquiv c)]
      simp only [f, hrepresentative]
      split_ifs
      · have hcard :=
          card_conjClass_mul_card_centralizer
            (representative c)
        rw [hrepresentative c] at hcard
        simpa only [nsmul_eq_mul, Nat.cast_id] using hcard
      · simp
    _ =
        Nat.card H *
          Nat.card {c : ConjClasses H // P c} := by
      simp_rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul]
      rw [← Fintype.card_subtype P]
      simpa only [Nat.card_eq_fintype_card, Nat.cast_id] using
        Nat.mul_comm
          (Fintype.card {c : ConjClasses H // P c})
          (Fintype.card H)

namespace IrreducibleCharacter

variable {A : Type} [Group A]
variable (N : Subgroup A) [N.Normal]

/-- The order of the preimage centralizer is the kernel order times the
order of the quotient centralizer. -/
theorem natCard_goodElementCentralizer
    (q : A ⧸ N) :
    Nat.card (goodElementCentralizer N q) =
      Nat.card N *
        Nat.card
          (Subgroup.centralizer ({q} : Set (A ⧸ N))) := by
  change
    Nat.card
        ((QuotientGroup.mk : A → A ⧸ N) ⁻¹'
          (Subgroup.centralizer
            ({q} : Set (A ⧸ N)) : Set (A ⧸ N))) =
      _
  exact QuotientGroup.card_preimage_mk N _

/-- Good quotient elements, weighted by the orders of their preimage
centralizers, contribute one copy of the ambient group order per good
quotient conjugacy class. -/
theorem
    sum_natCard_goodElementCentralizer_eq_card_mul_natCard_goodQuotientConjugacyClasses
    [Fintype A]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ) :
    (∑ q : A ⧸ N,
      if IsGoodQuotientElement N θ q then
        Nat.card (goodElementCentralizer N q)
      else 0) =
      Nat.card A *
        Nat.card (GoodQuotientConjugacyClasses N θ) := by
  classical
  have hclassSum :
      (∑ q : A ⧸ N,
        if IsGoodQuotientElement N θ q then
          Nat.card
            (Subgroup.centralizer
              ({q} : Set (A ⧸ N)))
        else 0) =
        Nat.card (A ⧸ N) *
          Nat.card
            (GoodQuotientConjugacyClasses N θ) := by
    simpa only [
      isGoodQuotientConjugacyClass_mk_iff
        N θ hinvariant,
      GoodQuotientConjugacyClasses
    ] using
      sum_natCard_centralizer_over_classPredicate
        (H := A ⧸ N)
        (IsGoodQuotientConjugacyClass N θ)
  calc
    (∑ q : A ⧸ N,
      if IsGoodQuotientElement N θ q then
        Nat.card (goodElementCentralizer N q)
      else 0) =
        ∑ q : A ⧸ N,
          if IsGoodQuotientElement N θ q then
            Nat.card N *
              Nat.card
                (Subgroup.centralizer
                  ({q} : Set (A ⧸ N)))
          else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      rw [natCard_goodElementCentralizer N q]
    _ =
        Nat.card N *
          (∑ q : A ⧸ N,
            if IsGoodQuotientElement N θ q then
              Nat.card
                (Subgroup.centralizer
                  ({q} : Set (A ⧸ N)))
            else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq :
          IsGoodQuotientElement N θ q <;>
        simp [hq]
    _ =
        Nat.card N *
          (Nat.card (A ⧸ N) *
            Nat.card
              (GoodQuotientConjugacyClasses N θ)) := by
      rw [hclassSum]
    _ =
        Nat.card A *
          Nat.card
            (GoodQuotientConjugacyClasses N θ) := by
      rw [← mul_assoc]
      congr 1
      rw [Nat.mul_comm]
      exact
        (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm

end IrreducibleCharacter
end McKayConjecture
