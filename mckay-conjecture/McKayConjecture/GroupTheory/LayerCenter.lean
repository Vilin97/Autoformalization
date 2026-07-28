/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.Component
import McKayConjecture.GroupTheory.FittingProduct

/-!
# The center of the layer

The center of the layer is characteristic in the layer and the layer is
normal in the ambient group.  Its ambient image is therefore a normal
nilpotent subgroup, and hence lies in the Fitting subgroup.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

open scoped IsMulCommutative

variable {G : Type u} [Group G] [Finite G]

/-- The ambient image of the center of the layer is normal. -/
instance map_center_layer_normal :
    ((Subgroup.center (layer G)).map
      (layer G).subtype).Normal :=
  inferInstance

omit [Finite G] in
/-- The ambient image of `Z(E(G))` is nilpotent. -/
theorem map_center_layer_isNilpotent :
    Group.IsNilpotent
      ((Subgroup.center (layer G)).map
        (layer G).subtype) := by
  let e :
      Subgroup.center (layer G) ≃*
        (Subgroup.center (layer G)).map
          (layer G).subtype :=
    (Subgroup.center (layer G)).equivMapOfInjective
      (layer G).subtype Subtype.coe_injective
  exact Group.nilpotent_of_mulEquiv e

/-- The ambient image of the center of the layer lies in the Fitting
subgroup. -/
theorem map_center_layer_le_fittingSubgroup :
    (Subgroup.center (layer G)).map
        (layer G).subtype ≤
      fittingSubgroup G :=
  normal_isNilpotent_le_fittingSubgroup
    ((Subgroup.center (layer G)).map
      (layer G).subtype)
    inferInstance map_center_layer_isNilpotent

/-- Equivalently, the center of the layer lies in the pullback of the
ambient Fitting subgroup. -/
theorem center_layer_le_comap_fittingSubgroup :
    Subgroup.center (layer G) ≤
      (fittingSubgroup G).comap (layer G).subtype := by
  rw [← Subgroup.map_le_iff_le_comap]
  exact map_center_layer_le_fittingSubgroup

/-- If the Fitting subgroup is the ambient center, then the ambient image
of the center of the layer is central in the whole group. -/
theorem map_center_layer_le_center_of_fittingSubgroup_eq_center
    (hF : fittingSubgroup G = Subgroup.center G) :
    (Subgroup.center (layer G)).map
        (layer G).subtype ≤
      Subgroup.center G :=
  map_center_layer_le_fittingSubgroup.trans_eq hF

end McKayConjecture.GroupTheory
