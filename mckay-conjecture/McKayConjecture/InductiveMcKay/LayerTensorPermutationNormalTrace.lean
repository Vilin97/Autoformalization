/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteTensorPermutationTrace
import McKayConjecture.GroupTheory.LayerProductCoordinateResidual
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCanonicalAssembly

/-!
# Normal-element traces in the canonical layer tensor construction

Elements of the component-local normal subgroup lie in the layer and
therefore normalize every component.  Thus they fix every canonical
tensor-permutation coordinate.  Their full tensor traces reduce to products
of the traces of the selected local transports.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace McKayConjecture
namespace InductiveMcKay
namespace LayerProjectiveRestrictionAssembly

open CharacterTriple
open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}
variable
  {d : ComponentOrbitLocalData D}
  {hcoordinate :
    d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
      d.isConjugationEquivariantUnder}
  {θ : PPrimeIrreducibleCharacter (layer G) p}

noncomputable local instance layerNormalTraceComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite _

/-- A target-triple normal element transported back to the original
component-local subgroup inside the layer intermediate. -/
def targetNormalOriginal
    (x : (targetTriple d θ).normalSubgroup) :
    d.intermediateComponentLocal :=
  CliffordEquivalence.inertiaNormalCopyEquiv
    d.intermediateComponentLocal
    (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1 x

/-- The same normal element in the component-local subgroup inside the
layer. -/
def targetNormalComponentLocalInLayer
    (x : (targetTriple d θ).normalSubgroup) :
    componentLocalSubgroupInLayer G d.intermediate :=
  d.intermediateComponentLocalEquivInLayer
    (targetNormalOriginal x)

/-- The same normal element in the canonically isomorphic layer-local
subgroup. -/
def targetNormalLayerLocal
    (x : (targetTriple d θ).normalSubgroup) :
    layerLocalSubgroup G d.intermediate :=
  d.toLayerComponentLocalData.componentLocalInLayerEquivLayerLocal
    (targetNormalComponentLocalInLayer x)

/-- A coordinate family whose central-product image is the selected target
normal element. -/
def targetNormalCoordinateFamily
    (x : (targetTriple d θ).normalSubgroup) :
    ∀ K : ComponentIndex G, d.intermediate K :=
  Function.surjInv
    (layerLocalProductHom_surjective G d.intermediate)
    (targetNormalLayerLocal x)

@[simp]
theorem targetNormalCoordinateFamily_product
    (x : (targetTriple d θ).normalSubgroup) :
    layerLocalProductHom G d.intermediate
        (targetNormalCoordinateFamily x) =
      targetNormalLayerLocal x :=
  Function.rightInverse_surjInv
    (layerLocalProductHom_surjective G d.intermediate)
    (targetNormalLayerLocal x)

/-- The source-triple normal copy of the same underlying layer-local
element. -/
def targetNormalSourceCopy
    (x : (targetTriple d θ).normalSubgroup) :
    (sourceTriple θ).normalSubgroup :=
  (CliffordEquivalence.inertiaNormalCopyEquiv
    (layer G) θ.1).symm
      ((targetNormalLayerLocal x :
        layerLocalSubgroup G d.intermediate) : layer G)

/-- The source normal character is the product of the original coordinate
characters on the same chosen central-product preimage used for the target
normal character. -/
theorem sourceTriple_character_values_targetNormalSourceCopy_eq_coordinateProduct
    (x : (targetTriple d θ).normalSubgroup) :
    (sourceTriple θ).character.values (targetNormalSourceCopy x) =
      ∏ K : ComponentIndex G,
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K).1.values
          (targetNormalCoordinateFamily x K) := by
  change
    θ.1.values
        ((targetNormalLayerLocal x :
          layerLocalSubgroup G d.intermediate) : layer G) =
      _
  rw [← targetNormalCoordinateFamily_product x]
  change
    θ.1.values
        (layerProductHom G
          (fun K : ComponentIndex G ↦
            (targetNormalCoordinateFamily x K : K.1))) =
      _
  have h :=
    GroupTheory.layerPPrimeCharacterEquiv_values_componentProduct
      G p
      ((GroupTheory.layerPPrimeCharacterEquiv G p).symm θ)
      (fun K : ComponentIndex G ↦
        (targetNormalCoordinateFamily x K : K.1))
  rw [GroupTheory.layerPPrimeCharacterEquiv_apply_symm_apply] at h
  exact h

/-- The target normal character is the product of the corresponding local
coordinate-character values on a chosen central-product preimage. -/
theorem targetTriple_character_values_normal_eq_coordinateProduct
    (x : (targetTriple d θ).normalSubgroup) :
    (targetTriple d θ).character.values x =
      ∏ K : ComponentIndex G,
        (d.correspondence K
          (ComponentOrbitLocalData.coordinateLayerCharacter θ K)).1.values
            (targetNormalCoordinateFamily x K) := by
  let y := targetNormalCoordinateFamily x
  change
    (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1.values
        (targetNormalOriginal x) =
      _
  change
    (d.toLayerComponentLocalData
      |>.componentLocalPPrimeCharacterEquiv θ).1.values
        (targetNormalComponentLocalInLayer x) =
      _
  change
    (d.toLayerComponentLocalData
      |>.layerPPrimeCharacterEquiv θ).1.values
        (targetNormalLayerLocal x) =
      _
  rw [← targetNormalCoordinateFamily_product x]
  exact
    d.toLayerComponentLocalData
      |>.layerPPrimeCharacterEquiv_values_layerLocalProduct θ y

/-- The same target-character formula, reindexed by the canonical
target-inertia orbits used by the tensor-permutation construction. -/
theorem targetTriple_character_values_normal_eq_orbitCoordinateProduct
    (x : (targetTriple d θ).normalSubgroup) :
    (targetTriple d θ).character.values x =
      ∏ o, ∏ K : LayerTargetOrbitCoordinate d θ o,
        (d.correspondence K.1
          (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.values
            (targetNormalCoordinateFamily x K.1) := by
  rw [targetTriple_character_values_normal_eq_coordinateProduct]
  calc
    (∏ K : ComponentIndex G,
        (d.correspondence K
          (ComponentOrbitLocalData.coordinateLayerCharacter θ K)).1.values
            (targetNormalCoordinateFamily x K)) =
        ∏ z :
          Σ o : LayerTargetComponentOrbit d θ,
            LayerTargetOrbitCoordinate d θ o,
          (d.correspondence z.2.1
            (ComponentOrbitLocalData.coordinateLayerCharacter
              θ z.2.1)).1.values
              (targetNormalCoordinateFamily x z.2.1) := by
      exact
        (Equiv.prod_comp
          (layerTargetOrbitCoordinateSigmaEquiv d θ)
          (fun K : ComponentIndex G ↦
            (d.correspondence K
              (ComponentOrbitLocalData.coordinateLayerCharacter
                θ K)).1.values
                  (targetNormalCoordinateFamily x K))).symm
    _ =
        ∏ o, ∏ K : LayerTargetOrbitCoordinate d θ o,
          (d.correspondence K.1
            (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.values
              (targetNormalCoordinateFamily x K.1) := by
      rw [Fintype.prod_sigma]

/-- The orbit-coordinate reindexing of the source normal-character
formula. -/
theorem sourceTriple_character_values_targetNormalSourceCopy_eq_orbitCoordinateProduct
    (x : (targetTriple d θ).normalSubgroup) :
    (sourceTriple θ).character.values (targetNormalSourceCopy x) =
      ∏ o, ∏ K : LayerTargetOrbitCoordinate d θ o,
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.values
          (targetNormalCoordinateFamily x K.1) := by
  rw [
    sourceTriple_character_values_targetNormalSourceCopy_eq_coordinateProduct]
  calc
    (∏ K : ComponentIndex G,
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K).1.values
          (targetNormalCoordinateFamily x K)) =
        ∏ z :
          Σ o : LayerTargetComponentOrbit d θ,
            LayerTargetOrbitCoordinate d θ o,
          (ComponentOrbitLocalData.coordinateLayerCharacter
            θ z.2.1).1.values
              (targetNormalCoordinateFamily x z.2.1) := by
      exact
        (Equiv.prod_comp
          (layerTargetOrbitCoordinateSigmaEquiv d θ)
          (fun K : ComponentIndex G ↦
            (ComponentOrbitLocalData.coordinateLayerCharacter θ K).1.values
              (targetNormalCoordinateFamily x K))).symm
    _ =
        ∏ o, ∏ K : LayerTargetOrbitCoordinate d θ o,
          (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.values
            (targetNormalCoordinateFamily x K.1) := by
      rw [Fintype.prod_sigma]

/-- A normal element of the target inertia triple fixes every component. -/
theorem targetNormal_smul_component_eq
    (x : (targetTriple d θ).normalSubgroup)
    (K : ComponentIndex G) :
    (x : targetInertiaGroup d θ) • K = K := by
  let g : G :=
    ((((x : targetInertiaGroup d θ) :
      d.ambientIntermediate) : G))
  have hgLocal : g ∈ d.ambientComponentLocal := by
    exact x.2
  have hgLayer : g ∈ layer G :=
    componentLocalSubgroup_le_layer G d.intermediate hgLocal
  apply Subtype.ext
  change K.1.map (MulAut.conj g).toMonoidHom = K.1
  exact
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (layer_le_normalizer_component K.2 hgLayer)

/-- The fixed-component statement restricted to a canonical orbit
coordinate. -/
theorem targetNormal_smul_orbitCoordinate_eq
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    (x : targetInertiaGroup d θ) • K = K := by
  apply Subtype.ext
  exact targetNormal_smul_component_eq x K.1

/-- Trace of the raw canonical source tensor at a target-normal element,
expressed as a product of local source-transport traces. -/
theorem canonicalSourceProjective_trace_normal
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    LinearMap.trace ℂ F.sourceTensorSpace
        (F.sourceProjective.operator
          (x : targetInertiaGroup d θ)) =
      ∏ o, ∏ K : LayerTargetOrbitCoordinate d θ o,
        LinearMap.trace ℂ (canonicalOrbitSourceSpace d θ o)
          ((canonicalLayerPairedTransport
            d hcoordinate θ o).sourceTransport
              (x : targetInertiaGroup d θ) K) := by
  let F :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  letI : ∀ o, Module.Finite ℂ (F.sourceOrbitSpace o) :=
    fun o ↦ F.sourceOrbitModuleFinite o
  change
    LinearMap.trace ℂ F.sourceTensorSpace
        (ProjectiveRepresentation.piTensorOperator
          (fun o ↦
            (F.sourceCocycle o).projectiveRepresentation)
          (x : targetInertiaGroup d θ)) =
      _
  rw [ProjectiveRepresentation.trace_piTensorOperator]
  apply Finset.prod_congr rfl
  intro o _
  exact
    (F.sourceCocycle o).trace_operator_of_fixed
      (x : targetInertiaGroup d θ)
      (targetNormal_smul_orbitCoordinate_eq x)

/-- Trace of the raw canonical target tensor at a target-normal element,
expressed as a product of local target-transport traces. -/
theorem canonicalTargetProjective_trace_normal
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    LinearMap.trace ℂ F.targetTensorSpace
        (F.targetProjective.operator
          (x : targetInertiaGroup d θ)) =
      ∏ o, ∏ K : LayerTargetOrbitCoordinate d θ o,
        LinearMap.trace ℂ (canonicalOrbitTargetSpace d θ o)
          ((canonicalLayerPairedTransport
            d hcoordinate θ o).targetTransport
              (x : targetInertiaGroup d θ) K) := by
  let F :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  letI : ∀ o, Module.Finite ℂ (F.targetOrbitSpace o) :=
    fun o ↦ F.targetOrbitModuleFinite o
  change
    LinearMap.trace ℂ F.targetTensorSpace
        (ProjectiveRepresentation.piTensorOperator
          (fun o ↦
            (F.targetCocycle o).projectiveRepresentation)
          (x : targetInertiaGroup d θ)) =
      _
  rw [ProjectiveRepresentation.trace_piTensorOperator]
  apply Finset.prod_congr rfl
  intro o _
  exact
    (F.targetCocycle o).trace_operator_of_fixed
      (x : targetInertiaGroup d θ)
      (targetNormal_smul_orbitCoordinate_eq x)

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
