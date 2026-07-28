/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.LayerLocalNormalizerAction
import McKayConjecture.GroupTheory.SylowNormalIntersection

/-!
# The layer-local intermediate subgroup

Let `Q` be a Sylow `p`-subgroup of the layer `E(G)` and let `M K` be a
component-local family invariant under the ambient normalizer `N_G(Q)`.
This file packages the subgroup

`L = componentLocalSubgroup G M ⊔ N_G(Q)`

used in the layer step of the McKay reduction.

The component-local subgroup is normal in `L`, its copy inside `L` is
canonically isomorphic both to the ambient component-local subgroup and to
its pullback to `E(G)`, and `E(G) L = G`.  For the canonical choice
`Q = P ∩ E(G)`, the Sylow normalizer `N_G(P)` is contained in `L`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable (G : Type u) [Group G] [Finite G]

/-- The intermediate subgroup obtained by adjoining the ambient layer-Sylow
normalizer to a component-local subgroup. -/
def layerIntermediate
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    Subgroup G :=
  componentLocalSubgroup G M ⊔
    LayerSylowAmbientNormalizer G Q

omit [Finite G] in
/-- The component-local subgroup is contained in its layer intermediate. -/
theorem componentLocalSubgroup_le_layerIntermediate
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    componentLocalSubgroup G M ≤
      layerIntermediate G Q M :=
  le_sup_left

omit [Finite G] in
/-- The ambient layer-Sylow normalizer is contained in the layer
intermediate. -/
theorem layerSylowAmbientNormalizer_le_layerIntermediate
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    LayerSylowAmbientNormalizer G Q ≤
      layerIntermediate G Q M :=
  le_sup_right

omit [Finite G] in
/-- Normalizer invariance makes the component-local subgroup normal inside
the layer intermediate. -/
theorem componentLocalSubgroup_normal_in_layerIntermediate
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M) :
    ((componentLocalSubgroup G M).subgroupOf
      (layerIntermediate G Q M)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (componentLocalSubgroup_le_layerIntermediate G Q M)]
  exact
    sup_le Subgroup.le_normalizer
      (layerSylowAmbientNormalizer_le_normalizer_componentLocal
        G M Q hM)

/-- The ambient layer-Sylow normalizer, viewed internally as a subgroup of
the layer intermediate. -/
def layerIntermediateAmbientNormalizer
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    Subgroup (layerIntermediate G Q M) :=
  (LayerSylowAmbientNormalizer G Q).subgroupOf
    (layerIntermediate G Q M)

/-- The internal copy of the ambient layer-Sylow normalizer is canonically
isomorphic to that ambient normalizer. -/
def layerIntermediateAmbientNormalizerEquiv
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    layerIntermediateAmbientNormalizer G Q M ≃*
      LayerSylowAmbientNormalizer G Q :=
  Subgroup.subgroupOfEquivOfLe
    (layerSylowAmbientNormalizer_le_layerIntermediate
      G Q M)

omit [Finite G] in
@[simp]
theorem layerIntermediateAmbientNormalizerEquiv_apply_coe
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (a : layerIntermediateAmbientNormalizer G Q M) :
    ((layerIntermediateAmbientNormalizerEquiv
      G Q M a :
        LayerSylowAmbientNormalizer G Q) : G) =
      (((a : layerIntermediate G Q M) : G)) :=
  rfl

omit [Finite G] in
/-- Internally to the layer intermediate, the component-local subgroup and
the ambient layer-Sylow normalizer generate the whole group. -/
theorem layerIntermediateComponentLocal_sup_ambientNormalizer_eq_top
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    (componentLocalSubgroup G M).subgroupOf
          (layerIntermediate G Q M) ⊔
        layerIntermediateAmbientNormalizer G Q M =
      ⊤ := by
  change
    (componentLocalSubgroup G M).subgroupOf
          (layerIntermediate G Q M) ⊔
        (LayerSylowAmbientNormalizer G Q).subgroupOf
          (layerIntermediate G Q M) =
      ⊤
  rw [← Subgroup.subgroupOf_sup
    (componentLocalSubgroup_le_layerIntermediate G Q M)
    (layerSylowAmbientNormalizer_le_layerIntermediate G Q M)]
  change
    (layerIntermediate G Q M).subgroupOf
        (layerIntermediate G Q M) =
      ⊤
  exact Subgroup.subgroupOf_self _

omit [Finite G] in
/-- Mapping the internal component-local subgroup back into the ambient
group recovers the original component-local subgroup. -/
theorem map_layerIntermediateComponentLocal
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    ((componentLocalSubgroup G M).subgroupOf
      (layerIntermediate G Q M)).map
        (layerIntermediate G Q M).subtype =
      componentLocalSubgroup G M :=
  Subgroup.map_subgroupOf_eq_of_le
    (componentLocalSubgroup_le_layerIntermediate G Q M)

/-- The internal component-local normal subgroup maps into the layer. -/
theorem map_layerIntermediateComponentLocal_le_layer
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    ((componentLocalSubgroup G M).subgroupOf
      (layerIntermediate G Q M)).map
        (layerIntermediate G Q M).subtype ≤
      layer G := by
  rw [map_layerIntermediateComponentLocal]
  exact componentLocalSubgroup_le_layer G M

/-- The internal copy of the component-local subgroup in the layer
intermediate is canonically isomorphic to the ambient copy. -/
def layerIntermediateComponentLocalEquiv
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    (componentLocalSubgroup G M).subgroupOf
        (layerIntermediate G Q M) ≃*
      componentLocalSubgroup G M :=
  Subgroup.subgroupOfEquivOfLe
    (componentLocalSubgroup_le_layerIntermediate G Q M)

omit [Finite G] in
@[simp]
theorem layerIntermediateComponentLocalEquiv_apply_coe
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (x :
      (componentLocalSubgroup G M).subgroupOf
        (layerIntermediate G Q M)) :
    ((layerIntermediateComponentLocalEquiv G Q M x :
      componentLocalSubgroup G M) : G) =
        ((x : layerIntermediate G Q M) : G) :=
  rfl

/-- The internal component-local normal subgroup is also canonically
isomorphic to the pullback of the component-local subgroup to the layer. -/
def layerIntermediateComponentLocalEquivInLayer
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    (componentLocalSubgroup G M).subgroupOf
        (layerIntermediate G Q M) ≃*
      componentLocalSubgroupInLayer G M :=
  (layerIntermediateComponentLocalEquiv G Q M).trans
    (componentLocalSubgroupInLayerEquivComponentLocalSubgroup
      G M).symm

@[simp]
theorem layerIntermediateComponentLocalEquivInLayer_apply_coe
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (x :
      (componentLocalSubgroup G M).subgroupOf
        (layerIntermediate G Q M)) :
    ((((layerIntermediateComponentLocalEquivInLayer
      G Q M x :
        componentLocalSubgroupInLayer G M) :
          layer G) : G)) =
      ((x : layerIntermediate G Q M) : G) := by
  change
    ((((componentLocalSubgroupInLayerEquivComponentLocalSubgroup
      G M).symm
        (layerIntermediateComponentLocalEquiv G Q M x) :
          componentLocalSubgroupInLayer G M) :
            layer G) : G) =
      ((x : layerIntermediate G Q M) : G)
  rw [
    componentLocalSubgroupInLayerEquivComponentLocalSubgroup_symm_apply_coe,
    layerIntermediateComponentLocalEquiv_apply_coe]

/-- Frattini generation for a Sylow subgroup of the layer. -/
theorem layer_sup_layerSylowAmbientNormalizer_eq_top
    {p : ℕ} [Fact p.Prime]
    (Q : Sylow p (layer G)) :
    layer G ⊔ LayerSylowAmbientNormalizer G Q =
      ⊤ :=
  Sylow.frattiniArgument Q

/-- Adjoining the layer to the layer intermediate generates the whole
ambient group. -/
theorem layer_sup_layerIntermediate_eq_top
    {p : ℕ} [Fact p.Prime]
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    layer G ⊔ layerIntermediate G Q M = ⊤ := by
  apply top_unique
  rw [← layer_sup_layerSylowAmbientNormalizer_eq_top G Q]
  exact
    sup_le le_sup_left
      ((layerSylowAmbientNormalizer_le_layerIntermediate
        G Q M).trans le_sup_right)

/-- The normalizer of an ambient Sylow subgroup normalizes its intersection
with the layer. -/
theorem normalizer_le_layerSylowAmbientNormalizer_intersectionNormal
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    Subgroup.normalizer (P : Set G) ≤
      LayerSylowAmbientNormalizer G
        (Sylow.intersectionNormal P (layer G)) := by
  change
    Subgroup.normalizer
        (((P : Subgroup G) : Set G)) ≤
      Subgroup.normalizer
        ((Sylow.ambientSubgroup
          (Sylow.intersectionNormal P (layer G)) :
            Subgroup G) : Set G)
  simpa only [LayerSylowAmbientNormalizer,
    Sylow.ambientSubgroup,
    Sylow.map_intersectionNormal_subtype] using
      (normalizer_le_normalizer_inf
        (layer G) (P : Subgroup G))

/-- For `Q = P ∩ E(G)`, the Sylow normalizer is contained in the
layer-local intermediate. -/
theorem normalizer_le_layerIntermediate_intersectionNormal
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    Subgroup.normalizer (P : Set G) ≤
      layerIntermediate G
        (Sylow.intersectionNormal P (layer G)) M :=
  (normalizer_le_layerSylowAmbientNormalizer_intersectionNormal
    G P).trans
      (layerSylowAmbientNormalizer_le_layerIntermediate
        G (Sylow.intersectionNormal P (layer G)) M)

end GroupTheory
end McKayConjecture
