/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.IsPerfect
import McKayConjecture.GroupTheory.UniversalCentralExtension

/-!
# Centers of perfect central extensions

For a central extension with perfect source, no new central elements appear
in the target: the source center maps onto the target center.

The proof uses Grün's lemma.  If the image of `a` is central, every
commutator of `a` lies in the extension kernel and hence in the source
center.  Thus the image of `a` is central in the quotient by the source
center.  Grün's lemma says that this latter center is trivial for a perfect
group, so `a` was central already.
-/

noncomputable section

universe u v

open scoped commutatorElement

namespace McKayConjecture
namespace GroupTheory
namespace CentralExtension

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q]

/-- In a central extension with perfect source, every lift of a central
target element is central. -/
theorem mem_center_of_projection_mem_center
    (E : CentralExtension A Q)
    (hperfect : Group.IsPerfect A)
    {a : A}
    (ha : E.projection a ∈ Subgroup.center Q) :
    a ∈ Subgroup.center A := by
  letI : Group.IsPerfect A := hperfect
  have haQuotient :
      QuotientGroup.mk' (Subgroup.center A) a ∈
        Subgroup.center (A ⧸ Subgroup.center A) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
        rw [← commutatorElement_eq_one_iff_mul_comm]
        change
          ⁅QuotientGroup.mk' (Subgroup.center A) x,
            QuotientGroup.mk' (Subgroup.center A) a⁆ = 1
        rw [← map_commutatorElement]
        apply (QuotientGroup.eq_one_iff _).2
        apply E.ker_le_center
        apply MonoidHom.mem_ker.mpr
        rw [map_commutatorElement]
        exact
          commutatorElement_eq_one_iff_mul_comm.mpr
            (Subgroup.mem_center_iff.mp ha
              (E.projection x))
  have haOne :
      QuotientGroup.mk' (Subgroup.center A) a = 1 := by
    have hcenter :
        Subgroup.center (A ⧸ Subgroup.center A) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot A
    rw [hcenter, Subgroup.mem_bot] at haQuotient
    exact haQuotient
  exact (QuotientGroup.eq_one_iff a).1 haOne

/-- A perfect central extension maps its source center onto the entire
target center. -/
theorem center_le_map_center_of_source_perfect
    (E : CentralExtension A Q)
    (hperfect : Group.IsPerfect A) :
    Subgroup.center Q ≤
      (Subgroup.center A).map E.projection := by
  intro q hq
  obtain ⟨a, rfl⟩ := E.surjective q
  exact
    ⟨a, E.mem_center_of_projection_mem_center hperfect hq, rfl⟩

/-- Exact center preservation for a perfect central extension. -/
theorem map_center_eq_center_of_source_perfect
    (E : CentralExtension A Q)
    (hperfect : Group.IsPerfect A) :
    (Subgroup.center A).map E.projection =
      Subgroup.center Q :=
  le_antisymm
    (map_center_le_center_of_surjective E.surjective)
    (E.center_le_map_center_of_source_perfect hperfect)

/-- Two homomorphisms from a perfect group to the source of a central
extension are equal when their composites with the projection agree. -/
theorem hom_ext_of_domain_perfect
    {P : Type*}
    [Group P]
    (E : CentralExtension A Q)
    (hperfect : Group.IsPerfect P)
    (f g : P →* A)
    (hprojection :
      E.projection.comp f =
        E.projection.comp g) :
    f = g := by
  letI : Group.IsPerfect P := hperfect
  apply MonoidHom.ext
  intro a
  have hcommutator :
      _root_.commutator P ≤ f.eqLocus g := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    change f ⁅x, y⁆ = g ⁅x, y⁆
    rw [map_commutatorElement, map_commutatorElement]
    let kx : A := f x * (g x)⁻¹
    let ky : A := f y * (g y)⁻¹
    have hkxKer : kx ∈ E.projection.ker := by
      apply MonoidHom.mem_ker.mpr
      have hx :=
        DFunLike.congr_fun hprojection x
      change
        E.projection (f x) =
          E.projection (g x) at hx
      simp [kx, hx]
    have hkyKer : ky ∈ E.projection.ker := by
      apply MonoidHom.mem_ker.mpr
      have hy :=
        DFunLike.congr_fun hprojection y
      change
        E.projection (f y) =
          E.projection (g y) at hy
      simp [ky, hy]
    have hkxCenter : kx ∈ Subgroup.center A :=
      E.ker_le_center hkxKer
    have hkyCenter : ky ∈ Subgroup.center A :=
      E.ker_le_center hkyKer
    have hfx : f x = kx * g x := by
      simp [kx]
    have hfy : f y = ky * g y := by
      simp [ky]
    have hkxComm (z : A) : kx * z = z * kx :=
      (Subgroup.mem_center_iff.mp hkxCenter z).symm
    have hkyComm (z : A) : ky * z = z * ky :=
      (Subgroup.mem_center_iff.mp hkyCenter z).symm
    have hkxCommutator (z : A) : ⁅kx, z⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hkxComm z)
    have hkyCommutator (z : A) : ⁅z, ky⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hkyComm z).symm
    rw [hfx, hfy,
      commutatorElement_mul_left_eq_conj_mul,
      hkxCommutator, mul_one]
    rw [hkxComm ⁅g x, ky * g y⁆, mul_assoc,
      mul_inv_cancel, mul_one]
    rw [commutatorElement_mul_right_eq_mul_conj,
      hkyCommutator, one_mul]
    rw [hkyComm ⁅g x, g y⁆, mul_assoc,
      mul_inv_cancel, mul_one]
  exact hcommutator Group.IsPerfect.mem_commutator

/-- Two endomorphisms of a perfect central extension which induce the same
map on the target are equal.  Their pointwise discrepancies are central,
so the two maps agree on every commutator and hence on the perfect source. -/
theorem hom_ext_of_source_perfect
    (E : CentralExtension A Q)
    (hperfect : Group.IsPerfect A)
    (f g : A →* A)
    (hprojection :
      E.projection.comp f =
        E.projection.comp g) :
    f = g := by
  letI : Group.IsPerfect A := hperfect
  apply MonoidHom.ext
  intro a
  have hcommutator :
      _root_.commutator A ≤ f.eqLocus g := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    change f ⁅x, y⁆ = g ⁅x, y⁆
    rw [map_commutatorElement, map_commutatorElement]
    let kx : A := f x * (g x)⁻¹
    let ky : A := f y * (g y)⁻¹
    have hkxKer : kx ∈ E.projection.ker := by
      apply MonoidHom.mem_ker.mpr
      have hx :=
        DFunLike.congr_fun hprojection x
      change
        E.projection (f x) =
          E.projection (g x) at hx
      simp [kx, hx]
    have hkyKer : ky ∈ E.projection.ker := by
      apply MonoidHom.mem_ker.mpr
      have hy :=
        DFunLike.congr_fun hprojection y
      change
        E.projection (f y) =
          E.projection (g y) at hy
      simp [ky, hy]
    have hkxCenter : kx ∈ Subgroup.center A :=
      E.ker_le_center hkxKer
    have hkyCenter : ky ∈ Subgroup.center A :=
      E.ker_le_center hkyKer
    have hfx : f x = kx * g x := by
      simp [kx]
    have hfy : f y = ky * g y := by
      simp [ky]
    have hkxComm (z : A) : kx * z = z * kx :=
      (Subgroup.mem_center_iff.mp hkxCenter z).symm
    have hkyComm (z : A) : ky * z = z * ky :=
      (Subgroup.mem_center_iff.mp hkyCenter z).symm
    have hkxCommutator (z : A) : ⁅kx, z⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hkxComm z)
    have hkyCommutator (z : A) : ⁅z, ky⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hkyComm z).symm
    rw [hfx, hfy,
      commutatorElement_mul_left_eq_conj_mul,
      hkxCommutator, mul_one]
    rw [hkxComm ⁅g x, ky * g y⁆, mul_assoc,
      mul_inv_cancel, mul_one]
    rw [commutatorElement_mul_right_eq_mul_conj,
      hkyCommutator, one_mul]
    rw [hkyComm ⁅g x, g y⁆, mul_assoc,
      mul_inv_cancel, mul_one]
  exact hcommutator Group.IsPerfect.mem_commutator

end CentralExtension
end GroupTheory
end McKayConjecture
