/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralProductLocalSubgroup
import McKayConjecture.GroupTheory.FrattiniIntermediate
import McKayConjecture.GroupTheory.LayerCentralProduct

/-!
# Local subgroups assembled inside the layer

For every component `K` of a finite group, choose a subgroup `M K`.
Multiplying these coordinate subgroups through the canonical component
product homomorphism gives a subgroup of the layer.  If every `M K`
contains `Z(K)` and at least one is proper, the resulting subgroup is
proper in the layer.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable (G : Type u) [Group G] [Finite G]

/-- The subgroup of the layer obtained by multiplying a chosen subgroup
inside every component. -/
def layerLocalSubgroup
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    Subgroup (layer G) :=
  (piLocalSubgroup M).map (layerProductHom G)

/-- Coordinate center containment and one proper coordinate make the
assembled subgroup proper in the layer. -/
theorem layerLocalSubgroup_lt_top
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hcenter :
      ∀ K, Subgroup.center K.1 ≤ M K)
    (hproper :
      ∃ K, M K < ⊤) :
    layerLocalSubgroup G M < ⊤ := by
  classical
  letI := Fintype.ofFinite (ComponentIndex G)
  exact
    map_piLocalSubgroup_lt_top_of_centralKernel
      (layerProductHom G)
      (layerProductHom_surjective G)
      (layerProductHom_ker_le_center G)
      M hcenter hproper

/-- The same assembled local subgroup, viewed in the ambient group. -/
def ambientLayerLocalSubgroup
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    Subgroup G :=
  (layerLocalSubgroup G M).map (layer G).subtype

/-- The ambient image lies in the layer. -/
theorem ambientLayerLocalSubgroup_le_layer
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    ambientLayerLocalSubgroup G M ≤
      layer G := by
  exact
    (Subgroup.map_le_range
      (layer G).subtype
      (layerLocalSubgroup G M)).trans_eq
        (layer G).range_subtype

/-- Under the coordinate hypotheses, the ambient image is properly
contained in the layer. -/
theorem ambientLayerLocalSubgroup_lt_layer
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hcenter :
      ∀ K, Subgroup.center K.1 ≤ M K)
    (hproper :
      ∃ K, M K < ⊤) :
    ambientLayerLocalSubgroup G M <
      layer G := by
  exact
    map_subtype_lt_ambient_of_lt_top
      (layer G) (layerLocalSubgroup G M)
      (layerLocalSubgroup_lt_top G M
        hcenter hproper)

end GroupTheory
end McKayConjecture
