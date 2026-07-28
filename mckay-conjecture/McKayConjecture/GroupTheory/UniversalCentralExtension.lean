/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.Quasisimple

/-!
# Universal central extensions

The reduction theorem for McKay is stated for universal covering groups of
nonabelian finite simple groups.  This file gives a kernel-checked interface
for those covers and proves that their source groups are quasisimple.
-/

noncomputable section

open Subgroup QuotientGroup
open scoped IsMulCommutative

universe u v

namespace McKayConjecture.GroupTheory

variable (U : Type u) (S : Type v) [Group U] [Group S]

/-- A central extension `U → S`: a surjective homomorphism whose kernel is
central. -/
structure CentralExtension where
  projection : U →* S
  surjective : Function.Surjective projection
  ker_le_center : projection.ker ≤ center U

namespace CentralExtension

variable {U S}

/-- A nonabelian simple target is centerless. -/
theorem center_target_eq_bot
    (_E : CentralExtension U S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    center S = ⊥ := by
  letI := hs
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with
    hbot | htop
  · exact hbot
  · exact (hnoncomm
      (Subgroup.center_eq_top_iff.mp htop)).elim

/-- For a central extension onto a nonabelian simple group, the kernel is
exactly the center of the covering group. -/
theorem ker_eq_center
    (E : CentralExtension U S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    E.projection.ker = center U := by
  apply le_antisymm E.ker_le_center
  intro z hz
  have hzmap :
      E.projection z ∈ center S := by
    have hmap :
        (center U).map E.projection ≤ center S :=
      map_center_le_center_of_surjective E.surjective
    exact hmap ⟨z, hz, rfl⟩
  rw [E.center_target_eq_bot hs hnoncomm,
    Subgroup.mem_bot] at hzmap
  exact MonoidHom.mem_ker.mpr hzmap

/-- The central quotient of the covering group is canonically isomorphic to
the nonabelian simple target. -/
def quotientCenterEquiv
    (E : CentralExtension U S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    (U ⧸ center U) ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq
      (E.ker_eq_center hs hnoncomm).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      E.projection E.surjective)

/-- A perfect central cover of a nonabelian simple group is quasisimple. -/
theorem source_isQuasisimple
    (E : CentralExtension U S)
    (hperfect : Group.IsPerfect U)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    IsQuasisimple U where
  isPerfect := hperfect
  isSimpleGroup_quotient := by
    letI := hs
    exact (E.quotientCenterEquiv hs hnoncomm).isSimpleGroup

end CentralExtension

/-- A universal central extension.  The universal property is expressed in
its usual initial form: it admits a unique map to every central extension of
the same target, commuting with the projections. -/
structure UniversalCentralExtension
    extends CentralExtension U S where
  sourcePerfect : Group.IsPerfect U
  lift :
    ∀ (V : Type (max u v)) [Group V]
      (E : CentralExtension V S),
      ∃! f : U →* V,
        E.projection.comp f = toCentralExtension.projection

namespace UniversalCentralExtension

variable {U S}

/-- The source of a universal central extension of a nonabelian simple group
is quasisimple. -/
theorem source_isQuasisimple
    (E : UniversalCentralExtension U S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    IsQuasisimple U :=
  E.toCentralExtension.source_isQuasisimple
    E.sourcePerfect hs hnoncomm

end UniversalCentralExtension
end McKayConjecture.GroupTheory
