/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.EquivariantTransport
import McKayConjecture.InductiveMcKay.LayerIntermediateReduction

/-!
# Normalizer actions inside the layer intermediate

The component-local subgroup occurs in two isomorphic forms: pulled back to
the layer and internal to the layer intermediate.  This file proves that the
canonical equivalence between those forms intertwines ambient
layer-Sylow-normalizer conjugation with ordinary conjugation inside the
intermediate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

namespace ComponentOrbitLocalData

/-- Conjugating the internal component-local normal subgroup by an internal
normalizer element agrees, across the canonical equivalence, with the
explicit ambient-normalizer action on its copy in the layer. -/
theorem intermediateComponentLocalEquivInLayer_congr_conjNormal
    (d : ComponentOrbitLocalData D)
    (a :
      layerIntermediateAmbientNormalizer
        G Q d.intermediate) :
    MulAut.congr d.intermediateComponentLocalEquivInLayer
        (MulAut.conjNormal
          (a : d.ambientIntermediate) :
            MulAut d.intermediateComponentLocal) =
      layerSylowAmbientNormalizerComponentLocalInLayerAction
        G Q d.intermediate
          d.isConjugationEquivariantUnder
          (layerIntermediateAmbientNormalizerEquiv
            G Q d.intermediate a) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ :=
    d.intermediateComponentLocalEquivInLayer.surjective x
  change
    d.intermediateComponentLocalEquivInLayer
        ((MulAut.conjNormal
          (a : d.ambientIntermediate) :
            MulAut d.intermediateComponentLocal)
          (d.intermediateComponentLocalEquivInLayer.symm
            (d.intermediateComponentLocalEquivInLayer y))) =
      layerSylowAmbientNormalizerComponentLocalInLayerAction
        G Q d.intermediate
          d.isConjugationEquivariantUnder
          (layerIntermediateAmbientNormalizerEquiv
            G Q d.intermediate a)
          (d.intermediateComponentLocalEquivInLayer y)
  rw [d.intermediateComponentLocalEquivInLayer.symm_apply_apply]
  apply Subtype.ext
  apply Subtype.ext
  change
    (((layerIntermediateComponentLocalEquivInLayer
        G Q d.intermediate
          ((MulAut.conjNormal
            (a : d.ambientIntermediate) :
              MulAut d.intermediateComponentLocal) y) :
        componentLocalSubgroupInLayer
          G d.intermediate) : layer G) : G) =
      (((layerSylowAmbientNormalizerComponentLocalInLayerAction
          G Q d.intermediate
            d.isConjugationEquivariantUnder
            (layerIntermediateAmbientNormalizerEquiv
              G Q d.intermediate a)
            (layerIntermediateComponentLocalEquivInLayer
              G Q d.intermediate y) :
        componentLocalSubgroupInLayer
          G d.intermediate) : layer G) : G)
  rw [
    layerIntermediateComponentLocalEquivInLayer_apply_coe,
    layerSylowAmbientNormalizerComponentLocalInLayerAction_apply_coe,
    layerIntermediateAmbientNormalizerEquiv_apply_coe,
    layerIntermediateComponentLocalEquivInLayer_apply_coe]
  rfl

/-- Pullback of characters across the canonical internal/layer equivalence
intertwines the same two normalizer actions. -/
theorem pPrimeComap_intermediateComponentLocalEquivInLayer_smul
    (d : ComponentOrbitLocalData D)
    (a :
      layerIntermediateAmbientNormalizer
        G Q d.intermediate)
    (ψ :
      PPrimeIrreducibleCharacter
        (componentLocalSubgroupInLayer
          G d.intermediate) p) :
    letI :
      MulAction (LayerSylowAmbientNormalizer G Q)
        (PPrimeIrreducibleCharacter
          (componentLocalSubgroupInLayer
            G d.intermediate) p) :=
      MulAction.compHom _
        (layerSylowAmbientNormalizerComponentLocalInLayerAction
          G Q d.intermediate
            d.isConjugationEquivariantUnder)
    IrreducibleCharacter.pPrimeComapEquiv p
        d.intermediateComponentLocalEquivInLayer
        ((layerIntermediateAmbientNormalizerEquiv
          G Q d.intermediate a) • ψ) =
      (a : d.ambientIntermediate) •
        IrreducibleCharacter.pPrimeComapEquiv p
          d.intermediateComponentLocalEquivInLayer ψ := by
  letI :
    MulAction (LayerSylowAmbientNormalizer G Q)
      (PPrimeIrreducibleCharacter
        (componentLocalSubgroupInLayer
          G d.intermediate) p) :=
    MulAction.compHom _
      (layerSylowAmbientNormalizerComponentLocalInLayerAction
        G Q d.intermediate
          d.isConjugationEquivariantUnder)
  have hcongr :=
    intermediateComponentLocalEquivInLayer_congr_conjNormal
      d a
  have hψ :
      (layerIntermediateAmbientNormalizerEquiv
          G Q d.intermediate a) • ψ =
        (MulAut.congr
          d.intermediateComponentLocalEquivInLayer
          (MulAut.conjNormal
            (a : d.ambientIntermediate) :
              MulAut d.intermediateComponentLocal)) • ψ := by
    change
      (layerSylowAmbientNormalizerComponentLocalInLayerAction
        G Q d.intermediate
          d.isConjugationEquivariantUnder
          (layerIntermediateAmbientNormalizerEquiv
            G Q d.intermediate a)) • ψ =
        (MulAut.congr
          d.intermediateComponentLocalEquivInLayer
          (MulAut.conjNormal
            (a : d.ambientIntermediate) :
              MulAut d.intermediateComponentLocal)) • ψ
    rw [hcongr]
  rw [hψ]
  exact
    pPrimeComapEquiv_congr_smul
      d.intermediateComponentLocalEquivInLayer p
      (MulAut.conjNormal
        (a : d.ambientIntermediate) :
          MulAut d.intermediateComponentLocal)
      ψ

end ComponentOrbitLocalData
end InductiveMcKay
end McKayConjecture
