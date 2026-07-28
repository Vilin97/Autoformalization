/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.LayerIntermediateNormalizerInvariant
import McKayConjecture.GroupTheory.LayerLocalSubgroupIdentification
import McKayConjecture.GroupTheory.LayerSylowNormalizerAction

/-!
# The ambient layer-Sylow normalizer action on local subgroups

Let `Q` be a Sylow subgroup of the layer and let
`A = N_G(Q)` denote the normalizer of its ambient image.  Ambient
conjugation gives explicit actions of `A` on the layer and on the
external product of the components.  If a component-local family is
equivariant under `A`, it also gives an action on the generated ambient
component-local subgroup.

The pullback of that subgroup to the layer is canonically isomorphic to
the ambient subgroup.  Transporting the ambient action across this
isomorphism gives an action on `componentLocalSubgroupInLayer`.  The
inclusions into the layer and ambient group, as well as component
multiplication, are equivariant for these actions.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

section General

variable (G : Type u) [Group G] [Finite G]
variable {p : ℕ} (Q : Sylow p (layer G))

/-- Conjugation by the ambient layer-Sylow normalizer on the layer. -/
def layerSylowAmbientNormalizerLayerAction :
    LayerSylowAmbientNormalizer G Q →*
      MulAut (layer G) :=
  (MulAut.conjNormal (H := layer G)).comp
    (LayerSylowAmbientNormalizer G Q).subtype

omit [Finite G] in
@[simp]
theorem layerSylowAmbientNormalizerLayerAction_apply
    (a : LayerSylowAmbientNormalizer G Q)
    (x : layer G) :
    layerSylowAmbientNormalizerLayerAction G Q a x =
      (MulAut.conjNormal (a : G) :
        MulAut (layer G)) x :=
  rfl

omit [Finite G] in
/-- The layer action is ambient conjugation on underlying elements. -/
@[simp]
theorem layerSylowAmbientNormalizerLayerAction_apply_coe
    (a : LayerSylowAmbientNormalizer G Q)
    (x : layer G) :
    ((layerSylowAmbientNormalizerLayerAction
        G Q a x : layer G) : G) =
      (a : G) * (x : G) * (a : G)⁻¹ :=
  rfl

omit [Finite G] in
/-- Inclusion of the layer into the ambient group intertwines the
normalizer action with ambient conjugation. -/
theorem layer_subtype_comp_layerSylowAmbientNormalizerLayerAction
    (a : LayerSylowAmbientNormalizer G Q) :
    (layer G).subtype.comp
        (layerSylowAmbientNormalizerLayerAction
          G Q a).toMonoidHom =
      (MulAut.conj (a : G)).toMonoidHom.comp
        (layer G).subtype := by
  ext x
  rfl

omit [Finite G] in
/-- Every element of the ambient normalizer fixes `Q` under its action
on Sylow subgroups of the layer. -/
theorem layerSylowAmbientNormalizerLayerAction_smul_Q
    (a : LayerSylowAmbientNormalizer G Q) :
    (layerSylowAmbientNormalizerLayerAction
        G Q a : MulAut (layer G)) • Q =
      Q := by
  change Sylow.ambientConj (a : G) Q = Q
  exact
    (Sylow.ambientConj_eq_iff_mem_ambientNormalizer
      (a : G) Q).mpr a.property

/-- The canonical inclusion of the ambient layer-Sylow normalizer into
the normalizer of an invariant component-local subgroup. -/
def layerSylowAmbientNormalizerToComponentLocalNormalizer
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M) :
    LayerSylowAmbientNormalizer G Q →*
      Subgroup.normalizer
        (componentLocalSubgroup G M : Set G) :=
  Subgroup.inclusion
    (layerSylowAmbientNormalizer_le_normalizer_componentLocal
      G M Q hM)

omit [Finite G] in
@[simp]
theorem layerSylowAmbientNormalizerToComponentLocalNormalizer_apply_coe
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M)
    (a : LayerSylowAmbientNormalizer G Q) :
    ((layerSylowAmbientNormalizerToComponentLocalNormalizer
        G Q M hM a :
      Subgroup.normalizer
        (componentLocalSubgroup G M : Set G)) : G) =
      (a : G) :=
  rfl

/-- Conjugation by the ambient layer-Sylow normalizer on an invariant
ambient component-local subgroup. -/
def layerSylowAmbientNormalizerComponentLocalAction
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M) :
    LayerSylowAmbientNormalizer G Q →*
      MulAut (componentLocalSubgroup G M) :=
  (componentLocalSubgroup G M).normalizerMonoidHom.comp
    (layerSylowAmbientNormalizerToComponentLocalNormalizer
      G Q M hM)

omit [Finite G] in
/-- The action on the ambient component-local subgroup is ambient
conjugation on underlying elements. -/
@[simp]
theorem layerSylowAmbientNormalizerComponentLocalAction_apply_coe
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M)
    (a : LayerSylowAmbientNormalizer G Q)
    (x : componentLocalSubgroup G M) :
    ((layerSylowAmbientNormalizerComponentLocalAction
        G Q M hM a x :
      componentLocalSubgroup G M) : G) =
      (a : G) * (x : G) * (a : G)⁻¹ :=
  rfl

omit [Finite G] in
/-- Inclusion of the ambient component-local subgroup into `G`
intertwines its normalizer action with ambient conjugation. -/
theorem componentLocal_subtype_comp_layerSylowAmbientNormalizerAction
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M)
    (a : LayerSylowAmbientNormalizer G Q) :
    (componentLocalSubgroup G M).subtype.comp
        (layerSylowAmbientNormalizerComponentLocalAction
          G Q M hM a).toMonoidHom =
      (MulAut.conj (a : G)).toMonoidHom.comp
        (componentLocalSubgroup G M).subtype := by
  ext x
  rfl

/-- The pullback of a component-local subgroup to the layer is
canonically isomorphic to the ambient component-local subgroup. -/
def componentLocalSubgroupInLayerEquivComponentLocalSubgroup
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    componentLocalSubgroupInLayer G M ≃*
      componentLocalSubgroup G M :=
  ((componentLocalSubgroupInLayer G M).equivMapOfInjective
      (layer G).subtype
      (layer G).subtype_injective).trans
    (MulEquiv.subgroupCongr
      (map_componentLocalSubgroupInLayer G M))

/-- The canonical pullback equivalence is inclusion on underlying
ambient elements. -/
@[simp]
theorem componentLocalSubgroupInLayerEquivComponentLocalSubgroup_apply_coe
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (x : componentLocalSubgroupInLayer G M) :
    ((componentLocalSubgroupInLayerEquivComponentLocalSubgroup
        G M x : componentLocalSubgroup G M) : G) =
      ((x : layer G) : G) :=
  rfl

/-- The inverse canonical pullback equivalence is also inclusion on
underlying ambient elements. -/
@[simp]
theorem componentLocalSubgroupInLayerEquivComponentLocalSubgroup_symm_apply_coe
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (x : componentLocalSubgroup G M) :
    ((((componentLocalSubgroupInLayerEquivComponentLocalSubgroup
        G M).symm x :
      componentLocalSubgroupInLayer G M) : layer G) : G) =
      (x : G) := by
  let e :=
    componentLocalSubgroupInLayerEquivComponentLocalSubgroup
      G M
  have h := e.apply_symm_apply x
  exact congrArg (fun y : componentLocalSubgroup G M => (y : G)) h

/-- The normalizer action on the component-local subgroup, transported
to its pullback inside the layer. -/
def layerSylowAmbientNormalizerComponentLocalInLayerAction
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M) :
    LayerSylowAmbientNormalizer G Q →*
      MulAut (componentLocalSubgroupInLayer G M) :=
  (MulAut.congr
      (componentLocalSubgroupInLayerEquivComponentLocalSubgroup
        G M).symm).toMonoidHom.comp
    (layerSylowAmbientNormalizerComponentLocalAction
      G Q M hM)

/-- The canonical pullback equivalence intertwines the two
component-local actions. -/
theorem componentLocalSubgroupInLayerEquiv_intertwines_action
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M)
    (a : LayerSylowAmbientNormalizer G Q) :
    (componentLocalSubgroupInLayerEquivComponentLocalSubgroup
        G M).toMonoidHom.comp
        (layerSylowAmbientNormalizerComponentLocalInLayerAction
          G Q M hM a).toMonoidHom =
      (layerSylowAmbientNormalizerComponentLocalAction
        G Q M hM a).toMonoidHom.comp
        (componentLocalSubgroupInLayerEquivComponentLocalSubgroup
          G M).toMonoidHom := by
  ext x
  simp [layerSylowAmbientNormalizerComponentLocalInLayerAction,
    MulAut.congr]

/-- The action on the pullback inside the layer is ambient conjugation
on underlying elements. -/
@[simp]
theorem layerSylowAmbientNormalizerComponentLocalInLayerAction_apply_coe
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M)
    (a : LayerSylowAmbientNormalizer G Q)
    (x : componentLocalSubgroupInLayer G M) :
    (((layerSylowAmbientNormalizerComponentLocalInLayerAction
        G Q M hM a x :
      componentLocalSubgroupInLayer G M) : layer G) : G) =
      (a : G) * ((x : layer G) : G) * (a : G)⁻¹ := by
  have h :=
    DFunLike.congr_fun
      (componentLocalSubgroupInLayerEquiv_intertwines_action
        G Q M hM a) x
  exact congrArg
    (fun y : componentLocalSubgroup G M => (y : G)) h

/-- Inclusion of the component-local pullback into the layer
intertwines its action with conjugation on the layer. -/
theorem componentLocalInLayer_subtype_comp_layerSylowAmbientNormalizerAction
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M)
    (a : LayerSylowAmbientNormalizer G Q) :
    (componentLocalSubgroupInLayer G M).subtype.comp
        (layerSylowAmbientNormalizerComponentLocalInLayerAction
          G Q M hM a).toMonoidHom =
      (layerSylowAmbientNormalizerLayerAction
        G Q a).toMonoidHom.comp
        (componentLocalSubgroupInLayer G M).subtype := by
  ext x
  change
    (((layerSylowAmbientNormalizerComponentLocalInLayerAction
        G Q M hM a x :
      componentLocalSubgroupInLayer G M) : layer G) : G) =
      ((layerSylowAmbientNormalizerLayerAction
        G Q a (x : layer G) : layer G) : G)
  rw [layerSylowAmbientNormalizerComponentLocalInLayerAction_apply_coe,
    layerSylowAmbientNormalizerLayerAction_apply_coe]

end General

section ComponentProduct

variable (G : Type) [Group G] [Finite G]
variable {p : ℕ} (Q : Sylow p (layer G))

/-- The ambient layer-Sylow normalizer action on the external product
of the components. -/
def layerSylowAmbientNormalizerComponentProductAction :
    LayerSylowAmbientNormalizer G Q →*
      MulAut (∀ K : ComponentIndex G, K.1) :=
  (layerComponentProductConjugationHom G).comp
    (LayerSylowAmbientNormalizer G Q).subtype

omit [Finite G] in
@[simp]
theorem layerSylowAmbientNormalizerComponentProductAction_apply
    (a : LayerSylowAmbientNormalizer G Q)
    (x : ∀ K : ComponentIndex G, K.1) :
    layerSylowAmbientNormalizerComponentProductAction
        G Q a x =
      layerComponentProductConjugation G (a : G) x :=
  rfl

omit [Finite G] in
/-- The component-product action has the expected coordinate formula
on underlying ambient elements. -/
@[simp]
theorem layerSylowAmbientNormalizerComponentProductAction_apply_coe
    (a : LayerSylowAmbientNormalizer G Q)
    (x : ∀ K : ComponentIndex G, K.1)
    (L : ComponentIndex G) :
    ((layerSylowAmbientNormalizerComponentProductAction
        G Q a x L : L.1) : G) =
      (a : G) *
        (x ((a : G)⁻¹ • L) : G) *
        (a : G)⁻¹ :=
  rfl

/-- Component multiplication intertwines the component-product action
with the action on the layer. -/
theorem layerProductHom_comp_layerSylowAmbientNormalizerAction
    (a : LayerSylowAmbientNormalizer G Q) :
    (layerProductHom G).comp
        (layerSylowAmbientNormalizerComponentProductAction
          G Q a).toMonoidHom =
      (layerSylowAmbientNormalizerLayerAction
        G Q a).toMonoidHom.comp
        (layerProductHom G) := by
  exact layerProductHom_comp_conjugation G (a : G)

end ComponentProduct

end GroupTheory
end McKayConjecture
