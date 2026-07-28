/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EquivarianceGeneration
import McKayConjecture.InductiveMcKay.LayerComponentCorrespondenceEquivariance
import McKayConjecture.InductiveMcKay.LayerIntermediateAction
import McKayConjecture.InductiveMcKay.LayerIntermediateCliffordReduction

/-!
# Equivariance of the layer-intermediate correspondence

Coordinate equivariance first gives equivariance under the ambient
normalizer of the selected layer Sylow subgroup.  Transport to the
component-local subgroup internal to the layer intermediate preserves
that law.  Finally, the internal component-local subgroup and the
internal ambient normalizer generate the whole layer intermediate, while
the former acts trivially on both character spaces.  Thus the
correspondence is equivariant under the full layer intermediate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

namespace ComponentOrbitLocalData

/-- Equivariance of the internal component-local correspondence under the
internal copy of the ambient layer-Sylow normalizer. -/
theorem intermediateComponentLocalPPrimeCharacterEquiv_map_ambientNormalizer_smul
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (a :
      layerIntermediateAmbientNormalizer
        G Q d.intermediate)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    d.intermediateComponentLocalPPrimeCharacterEquiv
        (((a : d.ambientIntermediate) : G) • θ) =
      (a : d.ambientIntermediate) •
        d.intermediateComponentLocalPPrimeCharacterEquiv θ := by
  letI :=
    LayerComponentLocalData.ambientNormalizerLayerPPrimeCharacterMulAction
      (G := G) (p := p) (Q := Q)
  letI :=
    d.toLayerComponentLocalData
      |>.ambientNormalizerComponentLocalInLayerPPrimeCharacterMulAction
        d.isConjugationEquivariantUnder
  let aN : LayerSylowAmbientNormalizer G Q :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate a
  have hsource :
      (((a : d.ambientIntermediate) : G) • θ) =
        aN • θ :=
    rfl
  have hcomponent :
      d.toLayerComponentLocalData.componentLocalPPrimeCharacterEquiv
          (aN • θ) =
        aN •
          (d.toLayerComponentLocalData
            |>.componentLocalPPrimeCharacterEquiv θ) :=
    d.toLayerComponentLocalData
      |>.componentLocalPPrimeCharacterEquiv_map_smul
        d.isConjugationEquivariantUnder
        hcoordinate aN θ
  calc
    d.intermediateComponentLocalPPrimeCharacterEquiv
        (((a : d.ambientIntermediate) : G) • θ) =
      d.intermediateComponentLocalPPrimeCharacterEquiv
        (aN • θ) :=
      congrArg d.intermediateComponentLocalPPrimeCharacterEquiv
        hsource
    _ =
      IrreducibleCharacter.pPrimeComapEquiv p
        d.intermediateComponentLocalEquivInLayer
        (d.toLayerComponentLocalData
          |>.componentLocalPPrimeCharacterEquiv (aN • θ)) :=
      rfl
    _ =
      IrreducibleCharacter.pPrimeComapEquiv p
        d.intermediateComponentLocalEquivInLayer
        (aN •
          (d.toLayerComponentLocalData
            |>.componentLocalPPrimeCharacterEquiv θ)) := by
      rw [hcomponent]
    _ =
      (a : d.ambientIntermediate) •
        IrreducibleCharacter.pPrimeComapEquiv p
          d.intermediateComponentLocalEquivInLayer
          (d.toLayerComponentLocalData
            |>.componentLocalPPrimeCharacterEquiv θ) :=
      d.pPrimeComap_intermediateComponentLocalEquivInLayer_smul
        a
        (d.toLayerComponentLocalData
          |>.componentLocalPPrimeCharacterEquiv θ)
    _ =
      (a : d.ambientIntermediate) •
        d.intermediateComponentLocalPPrimeCharacterEquiv θ :=
      rfl

/-- Coordinate equivariance implies equivariance of the internal
component-local correspondence under the full layer intermediate. -/
theorem intermediateComponentLocalPPrimeCharacterEquiv_map_smul
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (h : d.ambientIntermediate)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    d.intermediateComponentLocalPPrimeCharacterEquiv
        ((h : G) • θ) =
      h • d.intermediateComponentLocalPPrimeCharacterEquiv θ :=
  PPrimeIrreducibleCharacter.equivariant_of_normal_sup_eq_top
    (N := layer G)
    (H := d.ambientIntermediate)
    (M := d.intermediateComponentLocal)
    (A :=
      layerIntermediateAmbientNormalizer
        G Q d.intermediate)
    (p := p)
    (map_layerIntermediateComponentLocal_le_layer
      G Q d.intermediate)
    (layerIntermediateComponentLocal_sup_ambientNormalizer_eq_top
      G Q d.intermediate)
    d.intermediateComponentLocalPPrimeCharacterEquiv
    (d.intermediateComponentLocalPPrimeCharacterEquiv_map_ambientNormalizer_smul
      hcoordinate)
    h θ

/-- The component-local correspondence internal to the layer
intermediate, bundled with its full layer-intermediate equivariance. -/
def equivariantIntermediateComponentLocalPPrimeCorrespondence
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder) :
    EquivariantPPrimeCorrespondence
      d.ambientIntermediate p
      (layer G) d.intermediateComponentLocal where
  toCorrespondence :=
    d.intermediateComponentLocalPPrimeCharacterEquiv
  map_smul' :=
    d.intermediateComponentLocalPPrimeCharacterEquiv_map_smul
      hcoordinate

@[simp]
theorem equivariantIntermediateComponentLocalPPrimeCorrespondence_apply
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    d.equivariantIntermediateComponentLocalPPrimeCorrespondence
        hcoordinate θ =
      d.intermediateComponentLocalPPrimeCharacterEquiv θ :=
  rfl

end ComponentOrbitLocalData

section CanonicalIntersection

variable {P : Sylow p G}
variable
  {D :
    LayerSylowCoordinateData G p
      (layerSylowIntersection P)}

namespace LayerIntermediateCliffordReductionData

/-- The first layer-intermediate Clifford-reduction field follows from
coordinate equivariance. -/
theorem characterEquiv_smul_of_coordinateEquivariance
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder) :
    ∀ (h : d.ambientIntermediate)
      (θ : PPrimeIrreducibleCharacter (layer G) p),
      d.intermediateComponentLocalPPrimeCharacterEquiv (h • θ) =
        h • d.intermediateComponentLocalPPrimeCharacterEquiv θ :=
  d.intermediateComponentLocalPPrimeCharacterEquiv_map_smul
    hcoordinate

/-- Build the layer-intermediate Clifford-reduction data from coordinate
equivariance and the remaining central-witness family. -/
def ofCoordinateEquivariance
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (centralWitness :
      ∀ θ : PPrimeIrreducibleCharacter (layer G) p,
        CompleteCentralIsomorphismWitness
          (ofInertia (layer G) θ.1)
          (ofInertia d.intermediateComponentLocal
            (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1)) :
    LayerIntermediateCliffordReductionData d where
  characterEquiv_smul :=
    characterEquiv_smul_of_coordinateEquivariance
      d hcoordinate
  centralWitness := centralWitness

@[simp]
theorem ofCoordinateEquivariance_characterEquiv_smul
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (centralWitness :
      ∀ θ : PPrimeIrreducibleCharacter (layer G) p,
        CompleteCentralIsomorphismWitness
          (ofInertia (layer G) θ.1)
          (ofInertia d.intermediateComponentLocal
            (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1))
    (h : d.ambientIntermediate)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    (ofCoordinateEquivariance
      d hcoordinate centralWitness).characterEquiv_smul h θ =
        characterEquiv_smul_of_coordinateEquivariance
          d hcoordinate h θ :=
  rfl

end LayerIntermediateCliffordReductionData

end CanonicalIntersection

end InductiveMcKay
end McKayConjecture
