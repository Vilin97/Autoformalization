/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import McKayConjecture.GroupTheory.ComponentCommutation
import McKayConjecture.GroupTheory.ComponentFreeFittingCentralizer
import McKayConjecture.GroupTheory.FittingProduct
import McKayConjecture.GroupTheory.GeneralizedFittingMinimalNormal

/-!
# The centralizer of the generalized Fitting subgroup

This file records the normal-subgroup functoriality needed in the standard
proof that the generalized Fitting subgroup of a finite group contains its
own centralizer.  It also isolates the structural reduction at the heart of
that proof: the generalized Fitting subgroup of its centralizer is central
in that centralizer.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

open scoped IsMulCommutative

variable {G : Type u} [Group G]

/-- A component of a normal subgroup maps to an ambient component under
the inclusion. -/
theorem IsComponent.map_normal_subtype
    {N : Subgroup G} [N.Normal] {K : Subgroup N}
    (hK : IsComponent K) :
    IsComponent (K.map N.subtype) :=
  hK.map_subtype
    (inferInstance : N.Normal).isSubnormal

/-- The inclusion of a normal subgroup maps its layer into the ambient
layer. -/
theorem map_layer_normal_subgroup_le
    (N : Subgroup G) [N.Normal] :
    (layer N).map N.subtype ≤ layer G := by
  rw [Subgroup.map_le_iff_le_comap]
  apply layer_le
  intro K hK
  rw [← Subgroup.map_le_iff_le_comap]
  exact hK.map_normal_subtype.le_layer

/-- The inclusion of a normal subgroup maps its Fitting subgroup into the
ambient Fitting subgroup. -/
theorem map_fitting_normal_subgroup_le
    (N : Subgroup G) [N.Normal] :
    (fittingSubgroup N).map N.subtype ≤
      fittingSubgroup G :=
  map_fittingSubgroup_subtype_le N

/-- The inclusion of a normal subgroup maps its generalized Fitting
subgroup into the ambient generalized Fitting subgroup. -/
theorem map_generalizedFitting_normal_subgroup_le
    (N : Subgroup G) [N.Normal] :
    (generalizedFittingSubgroup N).map N.subtype ≤
      generalizedFittingSubgroup G := by
  rw [generalizedFittingSubgroup, Subgroup.map_sup]
  exact sup_le
    ((map_fitting_normal_subgroup_le N).trans
      fittingSubgroup_le_generalizedFitting)
    ((map_layer_normal_subgroup_le N).trans
      layer_le_generalizedFitting)

/-- The centralizer of the generalized Fitting subgroup. -/
abbrev generalizedFittingCentralizer
    (G : Type u) [Group G] : Subgroup G :=
  Subgroup.centralizer
    (generalizedFittingSubgroup G : Set G)

/-- The generalized-Fitting centralizer is characteristic. -/
instance generalizedFittingCentralizer_characteristic :
    (generalizedFittingCentralizer G).Characteristic :=
  inferInstance

/-- The generalized-Fitting centralizer is normal. -/
instance generalizedFittingCentralizer_normal :
    (generalizedFittingCentralizer G).Normal :=
  inferInstance

/-- The generalized Fitting subgroup of its ambient centralizer maps into
the ambient generalized Fitting subgroup. -/
theorem map_generalizedFittingCentralizer_le :
    (generalizedFittingSubgroup
        (generalizedFittingCentralizer G)).map
          (generalizedFittingCentralizer G).subtype ≤
      generalizedFittingSubgroup G :=
  map_generalizedFitting_normal_subgroup_le
    (generalizedFittingCentralizer G)

/-- The generalized Fitting subgroup of the generalized-Fitting
centralizer is central in that centralizer. -/
theorem generalizedFittingCentralizer_generalizedFitting_le_center :
    generalizedFittingSubgroup
        (generalizedFittingCentralizer G) ≤
      Subgroup.center
        (generalizedFittingCentralizer G) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hxambient :
      (x : G) ∈ generalizedFittingSubgroup G :=
    map_generalizedFittingCentralizer_le
      ⟨x, hx, rfl⟩
  exact (y.property (x : G) hxambient).symm

/-- In a finite group, the center of the generalized-Fitting centralizer
lies in its Fitting subgroup. -/
theorem generalizedFittingCentralizer_center_le_fitting
    [Finite G] :
    Subgroup.center (generalizedFittingCentralizer G) ≤
      fittingSubgroup (generalizedFittingCentralizer G) := by
  exact normal_isNilpotent_le_fittingSubgroup
    (Subgroup.center (generalizedFittingCentralizer G))
    inferInstance inferInstance

/-- The generalized Fitting subgroup of its centralizer is exactly the
center of that centralizer. -/
theorem generalizedFittingCentralizer_generalizedFitting_eq_center
    [Finite G] :
    generalizedFittingSubgroup
        (generalizedFittingCentralizer G) =
      Subgroup.center
        (generalizedFittingCentralizer G) := by
  apply le_antisymm
  · exact
      generalizedFittingCentralizer_generalizedFitting_le_center
  · exact
      generalizedFittingCentralizer_center_le_fitting.trans
        fittingSubgroup_le_generalizedFitting

/-- The Fitting subgroup of the generalized-Fitting centralizer is exactly
its center. -/
theorem generalizedFittingCentralizer_fitting_eq_center
    [Finite G] :
    fittingSubgroup (generalizedFittingCentralizer G) =
      Subgroup.center
        (generalizedFittingCentralizer G) := by
  apply le_antisymm
  · exact
      fittingSubgroup_le_generalizedFitting.trans
        generalizedFittingCentralizer_generalizedFitting_le_center
  · exact generalizedFittingCentralizer_center_le_fitting

/-- The generalized-Fitting centralizer has no components. -/
theorem generalizedFittingCentralizer_layer_eq_bot
    [Finite G] :
    layer (generalizedFittingCentralizer G) = ⊥ := by
  by_contra hne
  letI : Nontrivial
      (layer (generalizedFittingCentralizer G)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hnil :
      Group.IsNilpotent
        (layer (generalizedFittingCentralizer G)) :=
    isNilpotent_of_le_fittingSubgroup
      (layer_le_generalizedFitting.trans
        (generalizedFittingCentralizer_generalizedFitting_eq_center.le.trans
          generalizedFittingCentralizer_center_le_fitting))
  exact
    Group.IsPerfect.not_isNilpotent
      (layer (generalizedFittingCentralizer G)) hnil

/-- The ambient center of the generalized Fitting subgroup lies in its
centralizer. -/
theorem map_center_generalizedFitting_le_centralizer :
    (Subgroup.center
        (generalizedFittingSubgroup G)).map
          (generalizedFittingSubgroup G).subtype ≤
      generalizedFittingCentralizer G := by
  rintro z ⟨zF, hz, rfl⟩
  intro x hx
  exact congrArg Subtype.val
    (Subgroup.mem_center_iff.mp hz
      ⟨x, hx⟩)

/-- Intersecting the generalized Fitting subgroup with its ambient
centralizer gives its center, embedded in the ambient group. -/
theorem generalizedFitting_inf_centralizer_eq_map_center :
    generalizedFittingSubgroup G ⊓
        generalizedFittingCentralizer G =
      (Subgroup.center
          (generalizedFittingSubgroup G)).map
        (generalizedFittingSubgroup G).subtype := by
  apply le_antisymm
  · rintro x ⟨hxF, hxC⟩
    let xF : generalizedFittingSubgroup G :=
      ⟨x, hxF⟩
    have hxcenter :
        xF ∈
          Subgroup.center
            (generalizedFittingSubgroup G) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact hxC (y : G) y.property
    exact ⟨xF, hxcenter, rfl⟩
  · exact le_inf
      (Subgroup.map_subtype_le _)
      map_center_generalizedFitting_le_centralizer

/-- Once the self-centralizing inclusion is known, the centralizer is
exactly the embedded center of the generalized Fitting subgroup. -/
theorem generalizedFittingCentralizer_eq_map_center_of_le
    (hle :
      generalizedFittingCentralizer G ≤
        generalizedFittingSubgroup G) :
    generalizedFittingCentralizer G =
      (Subgroup.center
          (generalizedFittingSubgroup G)).map
        (generalizedFittingSubgroup G).subtype := by
  rw [← generalizedFitting_inf_centralizer_eq_map_center]
  exact (inf_eq_right.mpr hle).symm

/-- **Bender's self-centralizing theorem.**  In a finite group, the
centralizer of the generalized Fitting subgroup lies in the generalized
Fitting subgroup. -/
theorem centralizer_generalizedFittingSubgroup_le_self
    [Finite G] :
    generalizedFittingCentralizer G ≤
      generalizedFittingSubgroup G := by
  let C : Subgroup G :=
    generalizedFittingCentralizer G
  have hClayer : layer C = ⊥ :=
    generalizedFittingCentralizer_layer_eq_bot
  have hcentralizerF :
      Subgroup.centralizer
          (fittingSubgroup C : Set C) ≤
        fittingSubgroup C :=
    centralizer_fittingSubgroup_le_of_layer_eq_bot
      hClayer
  have hcentralizerFTop :
      Subgroup.centralizer
          (fittingSubgroup C : Set C) =
        ⊤ := by
    rw [generalizedFittingCentralizer_fitting_eq_center,
      Subgroup.centralizer_center]
  have hFtop : fittingSubgroup C = ⊤ := by
    apply top_unique
    rw [← hcentralizerFTop]
    exact hcentralizerF
  have hmap :
      (fittingSubgroup C).map C.subtype ≤
        fittingSubgroup G :=
    map_fitting_normal_subgroup_le C
  intro c hc
  let cC : C := ⟨c, hc⟩
  have hcF : cC ∈ fittingSubgroup C := by
    rw [hFtop]
    exact Subgroup.mem_top cC
  exact fittingSubgroup_le_generalizedFitting
    (hmap ⟨cC, hcF, rfl⟩)

/-- In a finite group, the generalized-Fitting centralizer is exactly the
ambient image of the center of the generalized Fitting subgroup. -/
theorem centralizer_generalizedFittingSubgroup_eq_map_center
    [Finite G] :
    generalizedFittingCentralizer G =
      (Subgroup.center
          (generalizedFittingSubgroup G)).map
        (generalizedFittingSubgroup G).subtype :=
  generalizedFittingCentralizer_eq_map_center_of_le
    centralizer_generalizedFittingSubgroup_le_self

end McKayConjecture.GroupTheory
