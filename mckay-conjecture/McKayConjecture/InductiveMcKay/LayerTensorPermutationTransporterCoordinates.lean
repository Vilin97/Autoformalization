/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerTensorPermutationNormalCoordinateTrace

/-!
# Coordinate decompositions of selected layer transporters

A selected target-inertia transporter lies in the layer intermediate.  The
internal component-local subgroup and internal ambient layer-Sylow
normalizer generate that intermediate.  This file records a decomposition
into those two factors together with the two properties of its normalizer
factor needed by the normal-trace calculation: it carries the selected
component representative to the requested component and fixes the layer
character.
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

/-- A component-local-times-normalizer decomposition of a selected
target-inertia component transporter. -/
structure LayerTargetTransporterDecomposition
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) where
  /-- The factor in the internal component-local normal subgroup. -/
  componentLocalPart : d.intermediateComponentLocal
  /-- The factor in the internal ambient layer-Sylow normalizer. -/
  ambientNormalizerPart :
    layerIntermediateAmbientNormalizer G Q d.intermediate
  /-- The two factors multiply to the selected target transporter. -/
  mul_eq_transporter :
    (componentLocalPart : d.ambientIntermediate) *
        (ambientNormalizerPart : d.ambientIntermediate) =
      (layerTargetComponentTransporter d θ K :
        targetInertiaGroup d θ)
  /-- The normalizer factor alone carries the selected orbit representative
  to `K`; the component-local factor fixes every component. -/
  ambientNormalizer_smul_representative :
    (((layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate ambientNormalizerPart :
        LayerSylowAmbientNormalizer G Q) : G)) •
        layerTargetComponentOrbitRepresentative d θ
          (layerTargetComponentOrbitOf d θ K) =
      K
  /-- The normalizer factor fixes the layer character. -/
  ambientNormalizer_smul_character :
    letI :=
      LayerComponentLocalData.ambientNormalizerLayerPPrimeCharacterMulAction
        (G := G) (p := p) (Q := Q)
    layerIntermediateAmbientNormalizerEquiv
        G Q d.intermediate ambientNormalizerPart • θ =
      θ

/-- Every selected target-inertia transporter admits the decomposition
above. -/
theorem exists_layerTargetTransporterDecomposition
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    Nonempty
      (LayerTargetTransporterDecomposition d hcoordinate θ K) := by
  let t :=
    layerTargetComponentTransporter d θ K
  let h : d.ambientIntermediate :=
    (t : targetInertiaGroup d θ)
  let M : Subgroup d.ambientIntermediate :=
    d.intermediateComponentLocal
  let A : Subgroup d.ambientIntermediate :=
    layerIntermediateAmbientNormalizer G Q d.intermediate
  have hh : h ∈ M ⊔ A := by
    rw [show M ⊔ A = ⊤ from
      layerIntermediateComponentLocal_sup_ambientNormalizer_eq_top
        G Q d.intermediate]
    exact Subgroup.mem_top h
  obtain ⟨m, hm, n, hn, hmn⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hh
  let mM : M := ⟨m, hm⟩
  let nA : A := ⟨n, hn⟩
  let nN : LayerSylowAmbientNormalizer G Q :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate nA
  let mG : G := ((mM : d.ambientIntermediate) : G)
  let nG : G := ((nA : d.ambientIntermediate) : G)
  let hG : G := (h : G)
  have hfactor : mG * nG = hG := by
    exact congrArg
      (fun x : d.ambientIntermediate ↦ (x : G)) hmn
  have hmLayer : mG ∈ layer G :=
    componentLocalSubgroup_le_layer G d.intermediate mM.2
  have hmfix :
      ∀ J : ComponentIndex G, mG • J = J := by
    intro J
    rw [← MulAction.mem_stabilizer_iff,
      component_stabilizer_eq_normalizer G J]
    exact layer_le_normalizer_component J.2 hmLayer
  let R :=
    layerTargetComponentOrbitRepresentative d θ
      (layerTargetComponentOrbitOf d θ K)
  have htR : hG • R = K := by
    exact layerTargetComponentTransporter_smul_representative d θ K
  have hnR : nG • R = K := by
    calc
      nG • R = mG • (nG • R) :=
        (hmfix (nG • R)).symm
      _ = (mG * nG) • R := (mul_smul mG nG R).symm
      _ = hG • R := by rw [hfactor]
      _ = K := htR
  have hmCharacter :
      ∀ χ : PPrimeIrreducibleCharacter (layer G) p,
        mG • χ = χ := by
    intro χ
    exact
      PPrimeIrreducibleCharacter.normalSubgroup_smul_eq
        (layer G) p ⟨mG, hmLayer⟩ χ
  have hnθ : nG • θ = θ := by
    calc
      nG • θ = mG • (nG • θ) :=
        (hmCharacter (nG • θ)).symm
      _ = (mG * nG) • θ := (mul_smul mG nG θ).symm
      _ = hG • θ := by rw [hfactor]
      _ = θ :=
        targetInertiaAmbient_smul_layerCharacter_eq
          (d := d) (θ := θ) hcoordinate t
  refine ⟨{
    componentLocalPart := mM
    ambientNormalizerPart := nA
    mul_eq_transporter := ?_
    ambientNormalizer_smul_representative := ?_
    ambientNormalizer_smul_character := ?_
  }⟩
  · exact hmn
  · exact hnR
  · exact hnθ

/-- A fixed selected decomposition, used only after its proved existence. -/
def layerTargetTransporterDecomposition
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    LayerTargetTransporterDecomposition d hcoordinate θ K :=
  Classical.choice
    (exists_layerTargetTransporterDecomposition
      d hcoordinate θ K)

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
