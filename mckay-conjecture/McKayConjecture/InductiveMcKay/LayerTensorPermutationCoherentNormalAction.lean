/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentNormalCoordinates

/-!
# Action induced by coherent representative coordinates

The coherent representative coordinate attached to a normal
target-inertia element induces exactly the selected shifted transporter
defect on the orbit representative.  The proof uses only the
central-product residual property of distinct layer components.
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

/-- A coherent coordinate constructed from any valid transporter
decomposition induces the shifted transporter-defect automorphism. -/
theorem coherentRepresentativeNormalCoordinateOfDecomposition_inducedAction
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    MulAut.conj
        (coherentRepresentativeNormalCoordinateOfDecomposition
          x K T :
          (layerTargetComponentOrbitRepresentative d θ o).1) =
      layerTargetOrbitShiftedDefectAutomorphism
        (d := d) (θ := θ)
        (x : targetInertiaGroup d θ) K := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let n :=
    layerIntermediateAmbientNormalizerEquiv
      G Q d.intermediate T.ambientNormalizerPart
  let u : ∀ J : ComponentIndex G, J.1 :=
    fun J ↦ (targetNormalCoordinateFamily x J : J.1)
  let v : ∀ J : ComponentIndex G, J.1 :=
    fun J ↦ (transporterComponentLocalCoordinateFamily T J : J.1)
  let X := layerProductHomToAmbient G u
  let M := layerProductHomToAmbient G v
  let nG : G := (n : G)
  have hfixed :
      (x : targetInertiaGroup d θ) • K = K :=
    targetNormal_smul_orbitCoordinate_eq x K
  have hdefect :=
    congrArg
      (fun z : targetInertiaGroup d θ ↦
        (((z : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G))
      (layerTargetOrbitShiftedTransporterDefect_eq_conjugate_of_fixed
        d θ (x : targetInertiaGroup d θ) K hfixed)
  change
    (((layerTargetOrbitShiftedTransporterDefect d θ
        (x : targetInertiaGroup d θ) K :
          targetInertiaGroup d θ) :
        d.ambientIntermediate) : G) =
      (((layerTargetComponentTransporter d θ K.1 :
          targetInertiaGroup d θ) :
        d.ambientIntermediate) : G)⁻¹ *
        ((((x : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G)) *
      (((layerTargetComponentTransporter d θ K.1 :
          targetInertiaGroup d θ) :
        d.ambientIntermediate) : G)
    at hdefect
  have htransport :=
    congrArg
      (fun z : d.ambientIntermediate ↦ (z : G))
      T.mul_eq_transporter
  have hX : X =
      ((((x : targetInertiaGroup d θ) :
        d.ambientIntermediate) : G)) := by
    exact targetNormalCoordinateFamily_product_apply_coe x
  have hM : M =
      ((T.componentLocalPart : d.ambientIntermediate) : G) := by
    exact transporterComponentLocalCoordinateFamily_product_apply_coe T
  have hn :
      ((T.ambientNormalizerPart : d.ambientIntermediate) : G) =
        nG := by
    rfl
  have htransportG :
      (((layerTargetComponentTransporter d θ K.1 :
        targetInertiaGroup d θ) : d.ambientIntermediate) : G) =
        M * nG := by
    rw [hM, ← hn]
    exact htransport.symm
  have hdefectG :
      (((layerTargetOrbitShiftedTransporterDefect d θ
          (x : targetInertiaGroup d θ) K :
            targetInertiaGroup d θ) :
          d.ambientIntermediate) : G) =
        nG⁻¹ * M⁻¹ * X * M * nG := by
    rw [hdefect, htransportG, hX]
    group
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  change
    (((coherentRepresentativeNormalCoordinateOfDecomposition
        x K T : d.intermediate R) : R.1) : G) *
          (z : G) *
        (((coherentRepresentativeNormalCoordinateOfDecomposition
          x K T : d.intermediate R) : R.1) : G)⁻¹ =
      (((layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ)
          (x : targetInertiaGroup d θ) K z : R.1) : G))
  rw [layerTargetOrbitShiftedDefectAutomorphism_apply_coe, hdefectG]
  have hcoordinateCoe :=
    coherentRepresentativeNormalCoordinateOfDecomposition_apply_coe
      x K T
  change
    (((coherentRepresentativeNormalCoordinateOfDecomposition
        x K T : d.intermediate R) : R.1) : G) =
      nG⁻¹ *
        (((transporterConjugatedNormalFamily x T K.1 :
          d.intermediate K.1) : K.1.1) : G) *
        nG at hcoordinateCoe
  rw [hcoordinateCoe]
  have hnK :
      nG • R = K.1 := by
    change
      (((layerIntermediateAmbientNormalizerEquiv
        G Q d.intermediate T.ambientNormalizerPart :
          LayerSylowAmbientNormalizer G Q) : G)) • R =
        K.1
    have h := T.ambientNormalizer_smul_representative
    rw [K.2] at h
    exact h
  let zK : K.1.1 :=
    ⟨nG * (z : G) * nG⁻¹, by
      have hzmem :=
        (componentConjugationEquiv G nG R z).2
      change nG * (z : G) * nG⁻¹ ∈ (nG • R).1 at hzmem
      rw [hnK] at hzmem
      exact hzmem⟩
  have hzK :
      (zK : G) = nG * (z : G) * nG⁻¹ := by
    rfl
  have hlocal :=
    layerProductHomToAmbient_conjugateProduct_component
      u v K.1 zK
  change
    (M⁻¹ * X * M) * (zK : G) *
        (M⁻¹ * X * M)⁻¹ =
      ((v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G)) *
        (zK : G) *
      ((v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G))⁻¹
    at hlocal
  change
    (nG⁻¹ *
        ((v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G)) *
        nG) *
        (z : G) *
      (nG⁻¹ *
        ((v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G)) *
        nG)⁻¹ =
      (nG⁻¹ * M⁻¹ * X * M * nG) *
        (z : G) *
      (nG⁻¹ * M⁻¹ * X * M * nG)⁻¹
  calc
    (nG⁻¹ *
        ((v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G)) *
        nG) *
        (z : G) *
      (nG⁻¹ *
        ((v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G)) *
        nG)⁻¹ =
      nG⁻¹ *
        (((v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G)) *
          (zK : G) *
        ((v K.1 : G)⁻¹ * (u K.1 : G) * (v K.1 : G))⁻¹) *
      nG := by
        rw [hzK]
        group
    _ =
      nG⁻¹ *
        ((M⁻¹ * X * M) * (zK : G) *
          (M⁻¹ * X * M)⁻¹) *
      nG := by rw [hlocal]
    _ =
      (nG⁻¹ * M⁻¹ * X * M * nG) *
        (z : G) *
      (nG⁻¹ * M⁻¹ * X * M * nG)⁻¹ := by
        rw [hzK]
        group

/-- The fixed selected transporter decomposition gives the same induced
action identity. -/
theorem coherentRepresentativeNormalCoordinate_inducedAction
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o) :
    MulAut.conj
        (coherentRepresentativeNormalCoordinate
          (hcoordinate := hcoordinate) x K :
          (layerTargetComponentOrbitRepresentative d θ o).1) =
      layerTargetOrbitShiftedDefectAutomorphism
        (d := d) (θ := θ)
        (x : targetInertiaGroup d θ) K :=
  coherentRepresentativeNormalCoordinateOfDecomposition_inducedAction
    x K
    (layerTargetTransporterDecomposition d hcoordinate θ K.1)

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
