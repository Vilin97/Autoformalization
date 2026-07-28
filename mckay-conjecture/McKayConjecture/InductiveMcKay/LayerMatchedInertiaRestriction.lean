/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerIntermediateCorrespondenceEquivariance
import McKayConjecture.InductiveMcKay.MatchedInertiaRestriction

/-!
# Matched inertia restriction for the layer intermediate

This file specializes the generic matched-inertia group construction to
the layer and its component-local subgroup inside the layer
intermediate.  The exact base intersection is already a theorem of the
layer-intermediate construction.  In the canonical minimal-counterexample
case, the required centralizer containment is also available.
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

/-- The canonical embedding from the inertia group of the matched
component-local character into the inertia group of the layer
character. -/
def layerIntermediateInertiaEmbedding
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    IrreducibleCharacter.inertia
        d.intermediateComponentLocal
        (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1 →*
      IrreducibleCharacter.inertia (layer G) θ.1 :=
  MatchedInertiaRestriction.embedding
    (layer G) d.ambientIntermediate
      d.intermediateComponentLocal
      d.intermediateComponentLocalPPrimeCharacterEquiv
      (MatchedInertiaRestriction.subgroup_equivariance_of_ambient
        (layer G) d.ambientIntermediate
        d.intermediateComponentLocal
        d.intermediateComponentLocalPPrimeCharacterEquiv
        (d.intermediateComponentLocalPPrimeCharacterEquiv_map_smul
          hcoordinate))
      θ

@[simp]
theorem layerIntermediateInertiaEmbedding_apply_coe
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (b :
      IrreducibleCharacter.inertia
        d.intermediateComponentLocal
        (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1) :
    ((d.layerIntermediateInertiaEmbedding hcoordinate θ b :
        IrreducibleCharacter.inertia (layer G) θ.1) : G) =
      (((b :
        IrreducibleCharacter.inertia
          d.intermediateComponentLocal
          (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1) :
        d.ambientIntermediate) : G) :=
  rfl

/-- The exact group-theoretic restriction data for the two matched
layer-intermediate inertia triples. -/
theorem layerIntermediateInertiaRestrictionGroupData
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (hcentral :
      Subgroup.centralizer (layer G : Set G) ≤
        d.ambientIntermediate)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    CentralRestrictionGroupData
      (ofInertia (layer G) θ.1)
      (ofInertia d.intermediateComponentLocal
        (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1)
      (d.layerIntermediateInertiaEmbedding hcoordinate θ) := by
  have hintersection :
      layer G ⊓ d.ambientIntermediate =
        d.intermediateComponentLocal.map
          d.ambientIntermediate.subtype := by
    calc
      layer G ⊓ d.ambientIntermediate =
          d.ambientComponentLocal :=
        d.layer_inf_ambientIntermediate_eq_ambientComponentLocal
      _ =
          d.intermediateComponentLocal.map
            d.ambientIntermediate.subtype :=
        (map_layerIntermediateComponentLocal
          G Q d.intermediate).symm
  exact
    MatchedInertiaRestriction.centralRestrictionGroupData
      (layer G) d.ambientIntermediate
      d.intermediateComponentLocal
      d.intermediateComponentLocalPPrimeCharacterEquiv
      (MatchedInertiaRestriction.subgroup_equivariance_of_ambient
        (layer G) d.ambientIntermediate
        d.intermediateComponentLocal
        d.intermediateComponentLocalPPrimeCharacterEquiv
        (d.intermediateComponentLocalPPrimeCharacterEquiv_map_smul
          hcoordinate))
      d.layer_sup_ambientIntermediate_eq_top
      hcentral hintersection θ

end ComponentOrbitLocalData

section CanonicalIntersection

variable {P : Sylow p G}
variable
  {D :
    LayerSylowCoordinateData G p
      (layerSylowIntersection P)}

namespace ComponentOrbitLocalData

/-- In a minimal counterexample, all group-theoretic hypotheses for
matched projective restriction are automatic. -/
theorem layerIntermediateInertiaRestrictionGroupData_of_minimalCounterexample
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (hminimal : MinimalCounterexampleStructure P)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    CentralRestrictionGroupData
      (ofInertia (layer G) θ.1)
      (ofInertia d.intermediateComponentLocal
        (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1)
      (d.layerIntermediateInertiaEmbedding hcoordinate θ) :=
  d.layerIntermediateInertiaRestrictionGroupData
    hcoordinate
    (d.centralizer_layer_le_ambientIntermediate hminimal)
    θ

end ComponentOrbitLocalData

end CanonicalIntersection

end InductiveMcKay
end McKayConjecture
