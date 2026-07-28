/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.Quasisimple
import McKayConjecture.GroupTheory.UniversalCentralExtension

/-!
# Universal covers dominate perfect central covers

Let `U → S` be a universal central extension and let `A → S` be any
perfect central cover in the same universe.  The universal property gives a
canonical homomorphism `U → A`.  It is surjective: its range maps onto `S`,
so together with `Z(A)` it generates `A`; that range is consequently normal,
contains the commutator subgroup, and hence equals `A` because `A` is
perfect.

Thus every perfect central cover is genuinely a central quotient of the
universal cover.  This is the group-theoretic bridge needed before applying
central-quotient descent to the quasisimple input.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory
namespace UniversalCentralExtension

variable {U S A : Type u}
variable [Group U] [Group S] [Group A]

/-- The canonical map from a universal cover to another central extension
of the same target. -/
def mapToCentralExtension
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S) :
    U →* A :=
  Classical.choose (E.lift A F)

/-- The canonical map commutes with the two projections. -/
theorem mapToCentralExtension_commutes
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S) :
    F.projection.comp (E.mapToCentralExtension F) =
      E.toCentralExtension.projection :=
  (Classical.choose_spec (E.lift A F)).1

/-- Uniqueness of the canonical map among maps over the target. -/
theorem mapToCentralExtension_unique
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (f : U →* A)
    (hf :
      F.projection.comp f =
        E.toCentralExtension.projection) :
    f = E.mapToCentralExtension F :=
  (Classical.choose_spec (E.lift A F)).2 f hf

/-- The range of the universal map together with the center generates any
perfect central cover.  Perfectness is not needed for this intermediate
generation statement. -/
theorem mapToCentralExtension_range_sup_center_eq_top
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S) :
    (E.mapToCentralExtension F).range ⊔
        Subgroup.center A =
      ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨u, hu⟩ :=
    E.toCentralExtension.surjective (F.projection a)
  have hcommutes :=
    DFunLike.congr_fun
      (E.mapToCentralExtension_commutes F) u
  have hprojection :
      F.projection (E.mapToCentralExtension F u) =
        F.projection a := by
    exact hcommutes.trans hu
  have hzKer :
      a * (E.mapToCentralExtension F u)⁻¹ ∈
        F.projection.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      hprojection, mul_inv_cancel]
  have hzCenter :
      a * (E.mapToCentralExtension F u)⁻¹ ∈
        Subgroup.center A :=
    F.ker_le_center hzKer
  have hfactor :
      a =
        (a * (E.mapToCentralExtension F u)⁻¹) *
          E.mapToCentralExtension F u := by
    simp
  rw [hfactor]
  exact
    ((E.mapToCentralExtension F).range ⊔
      Subgroup.center A).mul_mem
      (Subgroup.mem_sup_right hzCenter)
      (Subgroup.mem_sup_left
        ⟨u, rfl⟩)

/-- The canonical map onto a perfect central cover is surjective. -/
theorem mapToCentralExtension_surjective
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A) :
    Function.Surjective (E.mapToCentralExtension F) := by
  let H : Subgroup A :=
    (E.mapToCentralExtension F).range
  have hsup :
      H ⊔ Subgroup.center A = ⊤ :=
    E.mapToCentralExtension_range_sup_center_eq_top F
  have hnormalizer :
      Subgroup.normalizer (H : Set A) = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer
      (Subgroup.center_le_normalizer (H : Set A))
  have hnormal : H.Normal :=
    Subgroup.normalizer_eq_top_iff.mp hnormalizer
  have hcommutator :
      _root_.commutator A ≤ H :=
    commutator_le_of_sup_center_eq_top hnormal hsup
  have htop : H = ⊤ := by
    apply top_unique
    rw [← hperfect.commutator_eq_top]
    exact hcommutator
  exact MonoidHom.range_eq_top.mp htop

/-- Every perfect central cover is a central quotient of the universal
cover via the canonical map. -/
def centralExtensionToPerfectCover
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A) :
    CentralExtension U A where
  projection := E.mapToCentralExtension F
  surjective :=
    E.mapToCentralExtension_surjective F hperfect
  ker_le_center := by
    intro u hu
    apply E.toCentralExtension.ker_le_center
    apply MonoidHom.mem_ker.mpr
    have hcommutes :=
      DFunLike.congr_fun
        (E.mapToCentralExtension_commutes F) u
    rw [MonoidHom.comp_apply] at hcommutes
    rw [MonoidHom.mem_ker] at hu
    rw [hu, map_one] at hcommutes
    exact hcommutes.symm

@[simp]
theorem centralExtensionToPerfectCover_projection
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A) :
    (E.centralExtensionToPerfectCover F hperfect).projection =
      E.mapToCentralExtension F :=
  rfl

end UniversalCentralExtension
end GroupTheory
end McKayConjecture
