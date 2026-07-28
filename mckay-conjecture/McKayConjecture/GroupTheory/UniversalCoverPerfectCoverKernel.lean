/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Index
import McKayConjecture.GroupTheory.UniversalCoverDominatesPerfectCover

/-!
# Kernels of perfect quotients of a universal central extension

Let `E : U → S` be a universal central extension and let `F : A → S`
be a perfect central cover.  The canonical surjection `U → A` restricts
to a surjection

`ker(E) → ker(F)`.

This file records that restriction, checks its kernel, and derives the
finite cardinality and divisibility consequences.  In particular, the
kernel order of every concrete perfect central cover divides the kernel
order of the universal cover.  This is the precise comparison needed when
a Schur-multiplier computation is assembled from explicit central covers.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory
namespace UniversalCentralExtension

variable {U S A : Type u}
variable [Group U] [Group S] [Group A]

/-- The restriction to extension kernels of the canonical map from a
universal central extension to a perfect central cover. -/
def kernelMapToPerfectCover
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S) :
    E.toCentralExtension.projection.ker →*
      F.projection.ker :=
  ((E.mapToCentralExtension F).domRestrict
      E.toCentralExtension.projection.ker).codRestrict
    F.projection.ker (by
      intro u
      apply MonoidHom.mem_ker.mpr
      have h :=
        DFunLike.congr_fun
          (E.mapToCentralExtension_commutes F) (u : U)
      change
        F.projection (E.mapToCentralExtension F (u : U)) =
          E.toCentralExtension.projection (u : U) at h
      exact h.trans (MonoidHom.mem_ker.mp u.2))

@[simp]
theorem kernelMapToPerfectCover_apply
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (u : E.toCentralExtension.projection.ker) :
    (E.kernelMapToPerfectCover F u : A) =
      E.mapToCentralExtension F u :=
  rfl

/-- The restricted kernel map is onto whenever the comparison cover is
perfect. -/
theorem kernelMapToPerfectCover_surjective
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A) :
    Function.Surjective (E.kernelMapToPerfectCover F) := by
  intro a
  obtain ⟨u, hu⟩ :=
    E.mapToCentralExtension_surjective F hperfect a
  have huKer :
      u ∈ E.toCentralExtension.projection.ker := by
    apply MonoidHom.mem_ker.mpr
    have h :=
      DFunLike.congr_fun
        (E.mapToCentralExtension_commutes F) u
    change
      F.projection (E.mapToCentralExtension F u) =
        E.toCentralExtension.projection u at h
    rw [hu] at h
    exact h.symm.trans (MonoidHom.mem_ker.mp a.2)
  exact ⟨⟨u, huKer⟩, Subtype.ext hu⟩

/-- The kernel of the ambient comparison map already lies in the kernel
of the universal projection. -/
theorem mapToCentralExtension_ker_le_universalKernel
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S) :
    (E.mapToCentralExtension F).ker ≤
      E.toCentralExtension.projection.ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have h :=
    DFunLike.congr_fun
      (E.mapToCentralExtension_commutes F) u
  change
    F.projection (E.mapToCentralExtension F u) =
      E.toCentralExtension.projection u at h
  rw [hu, map_one] at h
  exact h.symm

/-- Kernel check for the restriction to extension kernels: no additional
elements are killed beyond the kernel of the ambient comparison map. -/
@[simp]
theorem kernelMapToPerfectCover_ker
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S) :
    (E.kernelMapToPerfectCover F).ker =
      (E.mapToCentralExtension F).ker.subgroupOf
        E.toCentralExtension.projection.ker := by
  rw [kernelMapToPerfectCover, MonoidHom.ker_codRestrict,
    MonoidHom.ker_domRestrict]

/-- The short exact sequence on extension kernels, expressed as a quotient
equivalence. -/
def universalKernelQuotientEquivPerfectCoverKernel
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A) :
    E.toCentralExtension.projection.ker ⧸
        (E.kernelMapToPerfectCover F).ker ≃*
      F.projection.ker :=
  QuotientGroup.quotientKerEquivOfSurjective
    (E.kernelMapToPerfectCover F)
    (E.kernelMapToPerfectCover_surjective F hperfect)

/-- The universal kernel is an extension of the kernel of any perfect
central cover by the kernel of the canonical comparison map. -/
theorem natCard_universalKernel_eq_mul_natCard_perfectCoverKernel
    [Finite U] [Finite A]
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A) :
    Nat.card E.toCentralExtension.projection.ker =
      Nat.card (E.kernelMapToPerfectCover F).ker *
        Nat.card F.projection.ker := by
  let f := E.kernelMapToPerfectCover F
  calc
    Nat.card E.toCentralExtension.projection.ker =
        Nat.card f.ker * f.ker.index :=
      f.ker.card_mul_index.symm
    _ = Nat.card f.ker * Nat.card f.range := by
      rw [Subgroup.index_ker]
    _ = Nat.card f.ker * Nat.card F.projection.ker := by
      rw [MonoidHom.range_eq_top.mpr
        (E.kernelMapToPerfectCover_surjective F hperfect)]
      simp

/-- Cardinality form of the kernel exact sequence using the ambient
comparison-map kernel itself. -/
theorem natCard_universalKernel_eq_natCard_comparisonKernel_mul_perfectCoverKernel
    [Finite U] [Finite A]
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A) :
    Nat.card E.toCentralExtension.projection.ker =
      Nat.card (E.mapToCentralExtension F).ker *
        Nat.card F.projection.ker := by
  rw [E.natCard_universalKernel_eq_mul_natCard_perfectCoverKernel
    F hperfect]
  congr 1
  rw [E.kernelMapToPerfectCover_ker F]
  exact
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (E.mapToCentralExtension_ker_le_universalKernel F)).toEquiv

/-- Consequently, the kernel order of every finite perfect central cover
divides the kernel order of the finite universal cover. -/
theorem natCard_perfectCoverKernel_dvd_natCard_universalKernel
    [Finite U] [Finite A]
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A) :
    Nat.card F.projection.ker ∣
      Nat.card E.toCentralExtension.projection.ker := by
  rw [E.natCard_universalKernel_eq_mul_natCard_perfectCoverKernel
    F hperfect]
  exact dvd_mul_left _ _

/-- Over a nonabelian simple target, extension kernels are source centers.
Thus the center order of every finite perfect central cover divides the
center order of the finite universal cover. -/
theorem natCard_center_perfectCover_dvd_natCard_center_universalCover
    [Finite U] [Finite A]
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A)
    (hsimple : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    Nat.card (Subgroup.center A) ∣
      Nat.card (Subgroup.center U) := by
  rw [← F.ker_eq_center hsimple hnoncomm,
    ← E.toCentralExtension.ker_eq_center hsimple hnoncomm]
  exact
    E.natCard_perfectCoverKernel_dvd_natCard_universalKernel
      F hperfect

end UniversalCentralExtension
end GroupTheory
end McKayConjecture
