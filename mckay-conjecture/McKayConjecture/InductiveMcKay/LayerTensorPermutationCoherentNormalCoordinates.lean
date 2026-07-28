/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerTensorPermutationTransporterCoordinates

/-!
# Coherent representative coordinates for normal layer elements

For a normal target-inertia element and a tensor coordinate `K`, this file
constructs an element of the selected orbit-representative intermediate.
The construction follows a fixed component-local-times-normalizer
decomposition of the transporter to `K`: first conjugate the chosen
central-product coordinate at `K` by the component-local coordinate, then
transport it back by the normalizer factor.
-/

noncomputable section

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

noncomputable local instance coherentNormalComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite _

/-- Reindexing a dependent intermediate family does not change the
underlying ambient element. -/
theorem intermediateFamily_value_coe_eq_of_index_eq
    (v : ∀ J : ComponentIndex G, d.intermediate J)
    {J L : ComponentIndex G}
    (hJL : J = L) :
    ((((v J : d.intermediate J) : J.1) : G)) =
      (((v L : d.intermediate L) : L.1) : G) := by
  subst L
  rfl

/-- The component-local part of a transporter decomposition, expressed in
the coordinate-product model. -/
def transporterComponentLocalCoordinateFamily
    {K : ComponentIndex G}
    (T :
      LayerTargetTransporterDecomposition d hcoordinate θ K) :
    ∀ J : ComponentIndex G, d.intermediate J :=
  Function.surjInv
    (layerLocalProductHom_surjective G d.intermediate)
    (d.toLayerComponentLocalData.componentLocalInLayerEquivLayerLocal
      (d.intermediateComponentLocalEquivInLayer
        T.componentLocalPart))

@[simp]
theorem transporterComponentLocalCoordinateFamily_product
    {K : ComponentIndex G}
    (T :
      LayerTargetTransporterDecomposition d hcoordinate θ K) :
    layerLocalProductHom G d.intermediate
        (transporterComponentLocalCoordinateFamily T) =
      d.toLayerComponentLocalData.componentLocalInLayerEquivLayerLocal
        (d.intermediateComponentLocalEquivInLayer
          T.componentLocalPart) :=
  Function.rightInverse_surjInv
    (layerLocalProductHom_surjective G d.intermediate)
    (d.toLayerComponentLocalData.componentLocalInLayerEquivLayerLocal
      (d.intermediateComponentLocalEquivInLayer
        T.componentLocalPart))

/-- The ambient product of the chosen transporter-component coordinates is
the original internal component-local factor. -/
theorem transporterComponentLocalCoordinateFamily_product_apply_coe
    {K : ComponentIndex G}
    (T :
      LayerTargetTransporterDecomposition d hcoordinate θ K) :
    layerProductHomToAmbient G
        (fun J : ComponentIndex G ↦
          (transporterComponentLocalCoordinateFamily T J : J.1)) =
      ((T.componentLocalPart : d.ambientIntermediate) : G) := by
  have h :=
    congrArg
      (fun y : layerLocalSubgroup G d.intermediate ↦
        (((y : layerLocalSubgroup G d.intermediate) : layer G) : G))
      (transporterComponentLocalCoordinateFamily_product T)
  change
    layerProductHomToAmbient G
        (fun J : ComponentIndex G ↦
          (transporterComponentLocalCoordinateFamily T J : J.1)) =
      _
    at h
  calc
    layerProductHomToAmbient G
        (fun J : ComponentIndex G ↦
          (transporterComponentLocalCoordinateFamily T J : J.1)) =
        (((d.toLayerComponentLocalData
          |>.componentLocalInLayerEquivLayerLocal
            (d.intermediateComponentLocalEquivInLayer
              T.componentLocalPart) :
            layerLocalSubgroup G d.intermediate) : layer G) : G) :=
      h
    _ = ((T.componentLocalPart : d.ambientIntermediate) : G) := by
      calc
        (((d.toLayerComponentLocalData
          |>.componentLocalInLayerEquivLayerLocal
            (d.intermediateComponentLocalEquivInLayer
              T.componentLocalPart) :
            layerLocalSubgroup G d.intermediate) : layer G) : G) =
            (((d.intermediateComponentLocalEquivInLayer
              T.componentLocalPart :
                componentLocalSubgroupInLayer
                  G d.intermediate) : layer G) : G) := by
          exact congrArg
            (fun z : layer G ↦ (z : G))
            (d.toLayerComponentLocalData
              |>.componentLocalInLayerEquivLayerLocal_apply_coe
                (d.intermediateComponentLocalEquivInLayer
                  T.componentLocalPart))
        _ = ((T.componentLocalPart : d.ambientIntermediate) : G) :=
          layerIntermediateComponentLocalEquivInLayer_apply_coe
            G Q d.intermediate T.componentLocalPart

/-- The ambient product of the chosen normal coordinates is the underlying
normal target-inertia element. -/
theorem targetNormalCoordinateFamily_product_apply_coe
    (x : (targetTriple d θ).normalSubgroup) :
    layerProductHomToAmbient G
        (fun J : ComponentIndex G ↦
          (targetNormalCoordinateFamily x J : J.1)) =
      ((((x : targetInertiaGroup d θ) :
        d.ambientIntermediate) : G)) := by
  have h :=
    congrArg
      (fun y : layerLocalSubgroup G d.intermediate ↦
        (((y : layerLocalSubgroup G d.intermediate) : layer G) : G))
      (targetNormalCoordinateFamily_product x)
  change
    layerProductHomToAmbient G
        (fun J : ComponentIndex G ↦
          (targetNormalCoordinateFamily x J : J.1)) =
      _
    at h
  change
    layerProductHomToAmbient G
        (fun J : ComponentIndex G ↦
          (targetNormalCoordinateFamily x J : J.1)) =
      ((((x : targetInertiaGroup d θ) :
        d.ambientIntermediate) : G))
  calc
    layerProductHomToAmbient G
        (fun J : ComponentIndex G ↦
          (targetNormalCoordinateFamily x J : J.1)) =
        (((targetNormalLayerLocal x :
          layerLocalSubgroup G d.intermediate) : layer G) : G) :=
      h
    _ =
        ((((x : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G)) := by
      change
        (((d.toLayerComponentLocalData
          |>.componentLocalInLayerEquivLayerLocal
            (d.intermediateComponentLocalEquivInLayer
              (targetNormalOriginal x)) :
            layerLocalSubgroup G d.intermediate) : layer G) : G) =
          _
      calc
        (((d.toLayerComponentLocalData
          |>.componentLocalInLayerEquivLayerLocal
            (d.intermediateComponentLocalEquivInLayer
              (targetNormalOriginal x)) :
            layerLocalSubgroup G d.intermediate) : layer G) : G) =
            (((d.intermediateComponentLocalEquivInLayer
              (targetNormalOriginal x) :
                componentLocalSubgroupInLayer
                  G d.intermediate) : layer G) : G) := by
          exact congrArg
            (fun z : layer G ↦ (z : G))
            (d.toLayerComponentLocalData
              |>.componentLocalInLayerEquivLayerLocal_apply_coe
                (d.intermediateComponentLocalEquivInLayer
                  (targetNormalOriginal x)))
        _ =
            (((targetNormalOriginal x :
              d.intermediateComponentLocal) :
              d.ambientIntermediate) : G) :=
          layerIntermediateComponentLocalEquivInLayer_apply_coe
            G Q d.intermediate (targetNormalOriginal x)
        _ =
            ((((x : targetInertiaGroup d θ) :
              d.ambientIntermediate) : G)) := by
          rfl

/-- Coordinatewise conjugation of the chosen normal-element preimage by
the component-local part of the selected transporter. -/
def transporterConjugatedNormalFamily
    (x : (targetTriple d θ).normalSubgroup)
    {K : ComponentIndex G}
    (T :
      LayerTargetTransporterDecomposition d hcoordinate θ K) :
    ∀ J : ComponentIndex G, d.intermediate J :=
  fun J ↦
    (transporterComponentLocalCoordinateFamily T J)⁻¹ *
      targetNormalCoordinateFamily x J *
      transporterComponentLocalCoordinateFamily T J

/-- The coherent normal coordinate obtained from a specified transporter
decomposition. -/
def coherentRepresentativeNormalCoordinateOfDecomposition
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    d.intermediate
      (layerTargetComponentOrbitRepresentative d θ o) :=
  let n :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate T.ambientNormalizerPart
  d.toLayerComponentLocalData.intermediateProductConjugationEquiv
      d.isConjugationEquivariantUnder n⁻¹
      (transporterConjugatedNormalFamily x T)
      (layerTargetComponentOrbitRepresentative d θ o)

/-- The coherent normal coordinate at the selected representative of the
target-inertia orbit of `K`, using the fixed selected transporter
decomposition. -/
def coherentRepresentativeNormalCoordinate
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    d.intermediate
      (layerTargetComponentOrbitRepresentative d θ o) :=
  coherentRepresentativeNormalCoordinateOfDecomposition
    x K
    (layerTargetTransporterDecomposition
      d hcoordinate θ K.1)

/-- The inverse normalizer factor carries `K` back to its selected
target-inertia orbit representative. -/
theorem transporterDecomposition_inv_smul_coordinate
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    let n :=
      layerIntermediateAmbientNormalizerEquiv
        G Q d.intermediate T.ambientNormalizerPart
    ((n⁻¹ : LayerSylowAmbientNormalizer G Q) : G) • K.1 =
      layerTargetComponentOrbitRepresentative d θ o := by
  let n :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate T.ambientNormalizerPart
  have hn :
      ((n : LayerSylowAmbientNormalizer G Q) : G) •
          layerTargetComponentOrbitRepresentative d θ o =
        K.1 := by
    have h := T.ambientNormalizer_smul_representative
    rw [K.2] at h
    exact h
  change ((n⁻¹ : LayerSylowAmbientNormalizer G Q) : G) • K.1 =
    layerTargetComponentOrbitRepresentative d θ o
  change (n : G)⁻¹ • K.1 =
    layerTargetComponentOrbitRepresentative d θ o
  rw [← hn, inv_smul_smul]

/-- Ambient-element formula for a coherent representative coordinate. -/
theorem coherentRepresentativeNormalCoordinateOfDecomposition_apply_coe
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    let n :=
      layerIntermediateAmbientNormalizerEquiv
        G Q d.intermediate T.ambientNormalizerPart
    (((coherentRepresentativeNormalCoordinateOfDecomposition
        x K T :
          d.intermediate
            (layerTargetComponentOrbitRepresentative d θ o)) :
        (layerTargetComponentOrbitRepresentative d θ o).1) : G) =
      ((n⁻¹ : LayerSylowAmbientNormalizer G Q) : G) *
        (((transporterConjugatedNormalFamily x T K.1 :
            (d.intermediate K.1)) : K.1.1) : G) *
        ((n : LayerSylowAmbientNormalizer G Q) : G) := by
  unfold coherentRepresentativeNormalCoordinateOfDecomposition
  dsimp only
  let n :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate T.ambientNormalizerPart
  let w := transporterConjugatedNormalFamily x T
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  change
    ((((d.toLayerComponentLocalData
      |>.intermediateProductConjugationEquiv
        d.isConjugationEquivariantUnder n⁻¹ w) R :
          d.intermediate R) : R.1) : G) =
      ((n⁻¹ : LayerSylowAmbientNormalizer G Q) : G) *
        (((w K.1 : d.intermediate K.1) : K.1.1) : G) *
        ((n : LayerSylowAmbientNormalizer G Q) : G)
  have hindex :
      ((n⁻¹ : LayerSylowAmbientNormalizer G Q) : G) • K.1 = R :=
    transporterDecomposition_inv_smul_coordinate K T
  change (n : G)⁻¹ • K.1 = R at hindex
  have happly :=
    d.toLayerComponentLocalData
      |>.intermediateProductConjugationEquiv_apply_apply
        d.isConjugationEquivariantUnder n⁻¹ w K.1
  have hcoe :=
    congrArg
      (fun y :
          d.intermediate ((n : G)⁻¹ • K.1) ↦
        (((y : d.intermediate ((n : G)⁻¹ • K.1)) :
          ((n : G)⁻¹ • K.1).1) : G))
      happly
  let v :=
    d.toLayerComponentLocalData
      |>.intermediateProductConjugationEquiv
        d.isConjugationEquivariantUnder n⁻¹ w
  calc
    ((((v R : d.intermediate R) : R.1) : G)) =
        ((((v ((n : G)⁻¹ • K.1) :
          d.intermediate ((n : G)⁻¹ • K.1)) :
            ((n : G)⁻¹ • K.1).1) : G)) :=
      (intermediateFamily_value_coe_eq_of_index_eq v hindex).symm
    _ =
        ((((d.toLayerComponentLocalData
          |>.relativeIntermediateConjugationEquiv
            d.isConjugationEquivariantUnder n⁻¹ K.1) (w K.1) :
              d.intermediate ((n : G)⁻¹ • K.1)) :
            ((n : G)⁻¹ • K.1).1) : G) :=
      hcoe
    _ =
        ((n⁻¹ : LayerSylowAmbientNormalizer G Q) : G) *
          (((w K.1 : d.intermediate K.1) : K.1.1) : G) *
          ((n : LayerSylowAmbientNormalizer G Q) : G) :=
      by
        simpa using
          (d.toLayerComponentLocalData
            |>.relativeIntermediateConjugationEquiv_apply_coe_ambient
              d.isConjugationEquivariantUnder n⁻¹ K.1 (w K.1))

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
