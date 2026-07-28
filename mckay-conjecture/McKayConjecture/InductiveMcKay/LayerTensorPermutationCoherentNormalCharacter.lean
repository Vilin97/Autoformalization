/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerCoordinateCharacterTransportValues
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentNormalAction

/-!
# Character values at coherent representative coordinates

Transporting a central-product coordinate to an orbit representative does
not change either matched local character value.  The normalizer factor is
handled by coordinate equivariance, while the component-local factor is an
inner conjugation and hence invisible to character values.
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

/-- The source component-character value at a coherent representative
coordinate is the original source value at the selected coordinate. -/
theorem coordinateLayerCharacter_values_coherentRepresentativeOfDecomposition
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    (ComponentOrbitLocalData.coordinateLayerCharacter θ
      (layerTargetComponentOrbitRepresentative d θ o)).1.values
        (coherentRepresentativeNormalCoordinateOfDecomposition
          x K T) =
      (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.values
        (targetNormalCoordinateFamily x K.1) := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let n :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate T.ambientNormalizerPart
  let q : d.intermediate K.1 :=
    transporterConjugatedNormalFamily x T K.1
  have hnθ :
      ((n : LayerSylowAmbientNormalizer G Q) : G) • θ = θ := by
    exact T.ambientNormalizer_smul_character
  have hindex :
      ((n⁻¹ : LayerSylowAmbientNormalizer G Q) : G) • K.1 = R :=
    transporterDecomposition_inv_smul_coordinate K T
  change
    componentConjugationPermutation G
        (((n : LayerSylowAmbientNormalizer G Q) : G)⁻¹) K.1 =
      R at hindex
  have hvalue :=
    LayerComponentLocalData.layerCoordinatePPrimeFamily_values_of_index_eq
      ((n : LayerSylowAmbientNormalizer G Q) : G)
      θ hnθ K.1 R hindex
      (q : K.1.1)
      (coherentRepresentativeNormalCoordinateOfDecomposition
        x K T : R.1)
      (coherentRepresentativeNormalCoordinateOfDecomposition_apply_coe
        x K T)
  have hinner :
      (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.values
          (q : K.1.1) =
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.values
          (targetNormalCoordinateFamily x K.1 : K.1.1) := by
    change
      (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.toClassFunction
          ((transporterComponentLocalCoordinateFamily T K.1 :
              K.1.1)⁻¹ *
            (targetNormalCoordinateFamily x K.1 : K.1.1) *
            (transporterComponentLocalCoordinateFamily T K.1 :
              K.1.1)) =
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.toClassFunction
          (targetNormalCoordinateFamily x K.1 : K.1.1)
    simpa only [inv_inv] using
      (ClassFunction.conj_apply
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.toClassFunction
        (targetNormalCoordinateFamily x K.1 : K.1.1)
        ((transporterComponentLocalCoordinateFamily T K.1 :
          K.1.1)⁻¹))
  exact hvalue.trans hinner

/-- The matched target component-character value at a coherent
representative coordinate is the original matched value at the selected
coordinate. -/
theorem coordinateLocalCharacter_values_coherentRepresentativeOfDecomposition
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    (d.correspondence
      (layerTargetComponentOrbitRepresentative d θ o)
      (ComponentOrbitLocalData.coordinateLayerCharacter θ
        (layerTargetComponentOrbitRepresentative d θ o))).1.values
          (coherentRepresentativeNormalCoordinateOfDecomposition
            x K T) =
      (d.correspondence K.1
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.values
          (targetNormalCoordinateFamily x K.1) := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let n :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate T.ambientNormalizerPart
  let q : d.intermediate K.1 :=
    transporterConjugatedNormalFamily x T K.1
  have hnθ :
      letI :=
        LayerComponentLocalData.ambientNormalizerLayerPPrimeCharacterMulAction
          (G := G) (p := p) (Q := Q)
      n • θ = θ := by
    exact T.ambientNormalizer_smul_character
  have hindex :
      ((n⁻¹ : LayerSylowAmbientNormalizer G Q) : G) • K.1 = R :=
    transporterDecomposition_inv_smul_coordinate K T
  change
    componentConjugationPermutation G
        ((n⁻¹ : LayerSylowAmbientNormalizer G Q) : G) K.1 =
      R at hindex
  have hvalue :=
    d.toLayerComponentLocalData
      |>.localCoordinatePPrimeFamily_values_of_index_eq
        d.isConjugationEquivariantUnder hcoordinate
        n θ hnθ K.1 R hindex q
        (coherentRepresentativeNormalCoordinateOfDecomposition
          x K T)
        (coherentRepresentativeNormalCoordinateOfDecomposition_apply_coe
          x K T)
  have hinner :
      (d.correspondence K.1
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.values
          q =
        (d.correspondence K.1
          (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.values
            (targetNormalCoordinateFamily x K.1) := by
    change
      (d.correspondence K.1
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.values
          ((transporterComponentLocalCoordinateFamily T K.1)⁻¹ *
            targetNormalCoordinateFamily x K.1 *
            transporterComponentLocalCoordinateFamily T K.1) =
        _
    simpa using
      (ClassFunction.conj_apply
        (d.correspondence K.1
          (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.toClassFunction
        (targetNormalCoordinateFamily x K.1)
        ((transporterComponentLocalCoordinateFamily T K.1)⁻¹))
  exact hvalue.trans hinner

/-- Source-value compatibility for the fixed selected transporter
decomposition. -/
theorem coordinateLayerCharacter_values_coherentRepresentative
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    (ComponentOrbitLocalData.coordinateLayerCharacter θ
      (layerTargetComponentOrbitRepresentative d θ o)).1.values
        (coherentRepresentativeNormalCoordinate
          (hcoordinate := hcoordinate) x K) =
      (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.values
        (targetNormalCoordinateFamily x K.1) :=
  coordinateLayerCharacter_values_coherentRepresentativeOfDecomposition
    x K
    (layerTargetTransporterDecomposition d hcoordinate θ K.1)

/-- Target-value compatibility for the fixed selected transporter
decomposition. -/
theorem coordinateLocalCharacter_values_coherentRepresentative
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    (d.correspondence
      (layerTargetComponentOrbitRepresentative d θ o)
      (ComponentOrbitLocalData.coordinateLayerCharacter θ
        (layerTargetComponentOrbitRepresentative d θ o))).1.values
          (coherentRepresentativeNormalCoordinate
            (hcoordinate := hcoordinate) x K) =
      (d.correspondence K.1
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.values
          (targetNormalCoordinateFamily x K.1) :=
  coordinateLocalCharacter_values_coherentRepresentativeOfDecomposition
    x K
    (layerTargetTransporterDecomposition d hcoordinate θ K.1)

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
