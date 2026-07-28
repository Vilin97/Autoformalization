/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Internal central products

Two normal subgroups which centralize one another multiply through a
homomorphism from their direct product.  Its image is their join and its
kernel is central.  Thus the join is canonically the quotient of the direct
product by this central kernel.
-/

noncomputable section

universe u

namespace McKayConjecture

/-- Data for an internal central product of two normal subgroups. -/
structure InternalCentralProduct (G : Type u) [Group G] where
  /-- The first central factor. -/
  left : Subgroup G
  /-- The second central factor. -/
  right : Subgroup G
  /-- Normality of the first factor. -/
  left_normal : left.Normal
  /-- Normality of the second factor. -/
  right_normal : right.Normal
  /-- The second factor centralizes the first factor. -/
  commute : right ≤ Subgroup.centralizer (left : Set G)

namespace InternalCentralProduct

variable {G : Type u} [Group G] (P : InternalCentralProduct G)

instance : P.left.Normal := P.left_normal
instance : P.right.Normal := P.right_normal

/-- Multiplication from the external direct product of the two factors. -/
def multiplication : P.left × P.right →* G where
  toFun z := (z.1 : G) * (z.2 : G)
  map_one' := by simp
  map_mul' x y := by
    change
      ((x.1 : G) * (y.1 : G)) *
          ((x.2 : G) * (y.2 : G)) =
        ((x.1 : G) * (x.2 : G)) *
          ((y.1 : G) * (y.2 : G))
    symm
    have hcomm :
        (y.1 : G) * (x.2 : G) =
          (x.2 : G) * (y.1 : G) :=
      P.commute x.2.property y.1 y.1.property
    calc
      ((x.1 : G) * (x.2 : G)) *
          ((y.1 : G) * (y.2 : G)) =
          (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
            simp only [mul_assoc]
      _ = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by
            rw [hcomm.symm]
      _ = ((x.1 : G) * (y.1 : G)) *
          ((x.2 : G) * (y.2 : G)) := by
            simp only [mul_assoc]

@[simp]
theorem multiplication_apply (z : P.left × P.right) :
    P.multiplication z = (z.1 : G) * (z.2 : G) :=
  rfl

/-- The internal central-product subgroup. -/
abbrev subgroup : Subgroup G :=
  MonoidHom.range P.multiplication

/-- The multiplication image is exactly the join of the two factors. -/
theorem subgroup_eq_sup :
    P.subgroup = P.left ⊔ P.right := by
  apply le_antisymm
  · rintro g ⟨z, rfl⟩
    exact (P.left ⊔ P.right).mul_mem
      (Subgroup.mem_sup_left z.1.property)
      (Subgroup.mem_sup_right z.2.property)
  · apply sup_le
    · intro h hh
      exact ⟨(⟨h, hh⟩, 1), by simp [multiplication]⟩
    · intro k hk
      exact ⟨(1, ⟨k, hk⟩), by simp [multiplication]⟩

instance subgroup_normal : P.subgroup.Normal := by
  rw [P.subgroup_eq_sup]
  infer_instance

/-- The central kernel identifying the overlap of the two factors. -/
abbrev kernel : Subgroup (P.left × P.right) :=
  MonoidHom.ker P.multiplication

@[simp]
theorem mem_kernel_iff (z : P.left × P.right) :
    z ∈ P.kernel ↔ (z.1 : G) * (z.2 : G) = 1 :=
  MonoidHom.mem_ker

/-- In a kernel pair, the second coordinate is the inverse of the first. -/
theorem kernel_snd_eq_inv_fst (z : P.kernel) :
    (z.1.2 : G) = (z.1.1 : G)⁻¹ := by
  have hz :
      (z.1.1 : G) * (z.1.2 : G) = 1 :=
    (P.mem_kernel_iff z.1).mp z.2
  exact eq_inv_of_mul_eq_one_right hz

/-- The overlap is canonically the anti-diagonal multiplication kernel. -/
def overlapEquivKernel :
    (P.left ⊓ P.right : Subgroup G) ≃* P.kernel where
  toFun z :=
    ⟨(⟨(z : G), z.property.1⟩,
      ⟨(z : G)⁻¹, P.right.inv_mem z.property.2⟩),
      by
        rw [P.mem_kernel_iff]
        simp⟩
  invFun n :=
    ⟨(n.1.1 : G),
      ⟨n.1.1.property, by
        rw [← inv_inv (n.1.1 : G),
          ← P.kernel_snd_eq_inv_fst n]
        exact P.right.inv_mem n.1.2.property⟩⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv n := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      exact (P.kernel_snd_eq_inv_fst n).symm
  map_mul' z w := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change
        ((z : G) * (w : G))⁻¹ =
          (z : G)⁻¹ * (w : G)⁻¹
      rw [mul_inv_rev]
      have hc : Commute (z : G) (w : G) :=
        P.commute w.property.2 z z.property.1
      exact hc.inv_left.inv_right.eq.symm

/-- The multiplication kernel is central in the external direct product. -/
theorem kernel_le_center :
    P.kernel ≤ Subgroup.center (P.left × P.right) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro y
  have hzprod :
      (z.1 : G) * (z.2 : G) = 1 :=
    (P.mem_kernel_iff z).mp hz
  have hz₂ : (z.2 : G) = (z.1 : G)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hzprod
  apply Prod.ext
  · apply Subtype.ext
    change
      (y.1 : G) * (z.1 : G) =
        (z.1 : G) * (y.1 : G)
    have hc :
        Commute (y.1 : G) (z.2 : G) :=
      P.commute z.2.property y.1 y.1.property
    rw [hz₂] at hc
    exact Commute.inv_right_iff.mp hc
  · apply Subtype.ext
    change
      (y.2 : G) * (z.2 : G) =
        (z.2 : G) * (y.2 : G)
    have hc :
        Commute (y.2 : G) (z.1 : G) :=
      (show Commute (z.1 : G) (y.2 : G) from
        P.commute y.2.property z.1 z.1.property).symm
    rw [hz₂]
    exact hc.inv_right

/-- The canonical quotient description of the internal central product. -/
def quotientEquiv :
    (P.left × P.right) ⧸ P.kernel ≃* P.subgroup :=
  QuotientGroup.quotientKerEquivRange P.multiplication

@[simp]
theorem quotientEquiv_mk (z : P.left × P.right) :
    P.quotientEquiv (QuotientGroup.mk' P.kernel z) =
      ⟨P.multiplication z, ⟨z, rfl⟩⟩ :=
  rfl

end InternalCentralProduct
end McKayConjecture
