/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.OfQuotient
import Mathlib.GroupTheory.SemidirectProduct
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Semidirect coordinates for a group action

An action of a group `P` on a group `A` is represented by the canonical
semidirect product `A ⋊ P`.  This file records the subgroup coordinates
needed to apply ambient-subgroup versions of coprime-action theorems:

* the canonical kernel is normal and isomorphic to `A`;
* the canonical acting subgroup is isomorphic to `P`;
* the two subgroups generate the semidirect product; and
* the centralizer of the acting subgroup inside the kernel is canonically
  the fixed-point subgroup `A^P`.

No coprimality assumption is needed for these structural facts.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

variable (P A : Type*) [Group P] [Group A]
variable [MulDistribMulAction P A]

/-- The automorphism homomorphism associated to the action. -/
abbrev actionHom : P →* MulAut A :=
  MulDistribMulAction.toMulAut P A

/-- The semidirect product associated to the action. -/
abbrev actionSemidirectProduct : Type _ :=
  A ⋊[actionHom P A] P

/-- The canonical copy of the acted-on group in its action semidirect
product. -/
abbrev actionKernel :
    Subgroup (actionSemidirectProduct P A) :=
  MonoidHom.range
    (SemidirectProduct.inl :
      A →* actionSemidirectProduct P A)

/-- The canonical copy of the acting group in the action semidirect
product. -/
abbrev actionActingSubgroup :
    Subgroup (actionSemidirectProduct P A) :=
  MonoidHom.range
    (SemidirectProduct.inr :
      P →* actionSemidirectProduct P A)

/-- Finiteness of both factors gives finiteness of the action semidirect
product. -/
instance actionSemidirectProductFinite
    [Finite P] [Finite A] :
    Finite (actionSemidirectProduct P A) :=
  Finite.of_equiv (A × P)
    SemidirectProduct.equivProd.symm

/-- The canonical action kernel is normal. -/
instance actionKernelNormal :
    (actionKernel P A).Normal := by
  rw [actionKernel,
    SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

/-- The canonical action kernel is isomorphic to the acted-on group. -/
def actionKernelEquiv :
    actionKernel P A ≃* A where
  toFun x := x.1.left
  invFun a :=
    ⟨SemidirectProduct.inl a, ⟨a, rfl⟩⟩
  left_inv x := by
    obtain ⟨a, ha⟩ := x.2
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · simpa using congrArg SemidirectProduct.right ha
  right_inv _ := rfl
  map_mul' x y := by
    have hx :
        x.1.right = 1 := by
      have hx' :
          SemidirectProduct.rightHom
              (x : actionSemidirectProduct P A) =
            1 := by
        rw [← MonoidHom.mem_ker,
          ← SemidirectProduct.range_inl_eq_ker_rightHom]
        exact x.2
      simpa only [
        SemidirectProduct.rightHom_eq_right] using hx'
    change
      (x.1 * y.1).left =
        x.1.left * y.1.left
    simp only [SemidirectProduct.mul_left, hx,
      map_one, MulAut.one_apply]

@[simp]
theorem actionKernelEquiv_apply
    (x : actionKernel P A) :
    actionKernelEquiv P A x = x.1.left :=
  rfl

/-- The canonical acting subgroup is isomorphic to the acting group. -/
def actionActingSubgroupEquiv :
    actionActingSubgroup P A ≃* P where
  toFun x := x.1.right
  invFun p :=
    ⟨SemidirectProduct.inr p, ⟨p, rfl⟩⟩
  left_inv x := by
    obtain ⟨p, hp⟩ := x.2
    apply Subtype.ext
    apply SemidirectProduct.ext
    · simpa using congrArg SemidirectProduct.left hp
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem actionActingSubgroupEquiv_apply
    (x : actionActingSubgroup P A) :
    actionActingSubgroupEquiv P A x = x.1.right :=
  rfl

/-- A prime-to-`p` acted-on group gives a prime-to-`p` canonical kernel. -/
theorem actionKernel_isPPrimeGroup
    {p : ℕ}
    (hA : IsPPrimeGroup p A) :
    IsPPrimeGroup p (actionKernel P A) :=
  hA.of_equiv (actionKernelEquiv P A).symm

/-- A `p`-group action gives a canonical acting `p`-subgroup. -/
theorem actionActingSubgroup_isPGroup
    {p : ℕ}
    (hP : IsPGroup p P) :
    IsPGroup p (actionActingSubgroup P A) :=
  hP.of_equiv (actionActingSubgroupEquiv P A).symm

/-- The canonical kernel and acting subgroup generate the whole action
semidirect product. -/
theorem actionKernel_sup_actionActingSubgroup :
    actionKernel P A ⊔
        actionActingSubgroup P A =
      ⊤ := by
  apply top_unique
  intro x _hx
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact
    (actionKernel P A ⊔
      actionActingSubgroup P A).mul_mem
      ((show actionKernel P A ≤
          actionKernel P A ⊔
            actionActingSubgroup P A from
        le_sup_left)
        (show SemidirectProduct.inl x.left ∈
            actionKernel P A from
          ⟨x.left, rfl⟩))
      ((show actionActingSubgroup P A ≤
          actionKernel P A ⊔
            actionActingSubgroup P A from
        le_sup_right)
        (show SemidirectProduct.inr x.right ∈
            actionActingSubgroup P A from
          ⟨x.right, rfl⟩))

/-- The fixed kernel inside the semidirect product. -/
abbrev actionFixedKernel :
    Subgroup (actionSemidirectProduct P A) :=
  actionKernel P A ⊓
    Subgroup.centralizer
      (actionActingSubgroup P A :
        Set (actionSemidirectProduct P A))

/-- Centralizing the canonical acting subgroup inside the canonical
kernel is equivalent to being fixed by the original action. -/
def actionFixedKernelEquiv :
    actionFixedKernel P A ≃*
      FixedPoints.subgroup P A where
  toFun x :=
    ⟨x.1.left, fun p ↦ by
      have hcomm :
          (x.1 :
              actionSemidirectProduct P A) *
                SemidirectProduct.inr p =
            SemidirectProduct.inr p * x.1 :=
        (Subgroup.mem_centralizer_iff.mp x.2.2
          (SemidirectProduct.inr p)
          ⟨p, rfl⟩).symm
      have hleft :=
        congrArg SemidirectProduct.left hcomm
      simpa using hleft.symm⟩
  invFun a :=
    ⟨SemidirectProduct.inl a.1,
      ⟨⟨a.1, rfl⟩, by
        apply Subgroup.mem_centralizer_iff.mpr
        intro y hy
        obtain ⟨p, rfl⟩ := hy
        apply SemidirectProduct.ext
        · simpa using a.2 p
        · simp⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.2.1
    apply SemidirectProduct.ext
    · rfl
    · simpa using congrArg SemidirectProduct.right ha
  right_inv _ := rfl
  map_mul' x y := by
    apply Subtype.ext
    change (x.1 * y.1).left =
      x.1.left * y.1.left
    have hxright :
        x.1.right = 1 := by
      obtain ⟨a, ha⟩ := x.2.1
      rw [← ha]
      rfl
    simp only [SemidirectProduct.mul_left,
      hxright, map_one, MulAut.one_apply]

@[simp]
theorem actionFixedKernelEquiv_apply_coe
    (x : actionFixedKernel P A) :
    ((actionFixedKernelEquiv P A x :
        FixedPoints.subgroup P A) : A) =
      x.1.left :=
  rfl

end GroupTheory
end McKayConjecture
