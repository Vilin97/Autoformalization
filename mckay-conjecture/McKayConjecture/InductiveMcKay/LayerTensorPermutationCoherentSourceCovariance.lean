/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteTensorPermutationCovariance
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentSourceRestriction

/-!
# Covariance of the intrinsic coherent source restriction

The selected semidirect coordinate transports conjugate the honest
representative-component actions by the corresponding shifted transporter
automorphisms.  Tensor-permutation covariance then assembles these local
identities, and component multiplication identifies the result with ambient
conjugation on the layer.
-/

noncomputable section

open scoped TensorProduct

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

noncomputable local instance coherentSourceCovarianceComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite _

/-- Conjugation by a selected source semidirect element carries the
canonical normal copy to the shifted-defect automorphism of its component
coordinate. -/
theorem coordinateSourceNormalCopyHom_conjNormal
    {o : LayerTargetComponentOrbit d θ}
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o)
    (y : (layerTargetComponentOrbitRepresentative d θ o).1) :
    MulAut.conjNormal (S.sourceElement a K)
        (coordinateSourceNormalCopyHom θ
          (layerTargetComponentOrbitRepresentative d θ o) y) =
      coordinateSourceNormalCopyHom θ
        (layerTargetComponentOrbitRepresentative d θ o)
        (layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K y) := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change
      ((S.sourceElement a K) *
        SemidirectProduct.inl y *
        (S.sourceElement a K)⁻¹).left =
      layerTargetOrbitShiftedDefectAutomorphism
        (d := d) (θ := θ) a K y
    calc
      ((S.sourceElement a K) *
          SemidirectProduct.inl y *
          (S.sourceElement a K)⁻¹).left =
        (S.sourceElement a K).left *
          PPrimeCharacterStabilizer.ambientAction
              (P := D.coordinate
                (layerTargetComponentOrbitRepresentative d θ o))
              (χ := ComponentOrbitLocalData.coordinateLayerCharacter θ
                (layerTargetComponentOrbitRepresentative d θ o))
              (S.sourceElement a K).right y *
          (S.sourceElement a K).left⁻¹ := by
        exact
          conjugate_semidirectNormal_left
            (PPrimeCharacterStabilizer.ambientAction
              (P := D.coordinate
                (layerTargetComponentOrbitRepresentative d θ o))
              (χ := ComponentOrbitLocalData.coordinateLayerCharacter θ
                (layerTargetComponentOrbitRepresentative d θ o)))
            (S.sourceElement a K)
            (coordinateSourceNormalCopyHom θ
              (layerTargetComponentOrbitRepresentative d θ o) y)
      _ =
        layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K y := by
        have h :=
          DFunLike.congr_fun (S.inducedAction a K) y
        simpa only [semidirectNormalAction_apply,
          CanonicalOrbitSemidirectSection.sourceElement] using h
  · change
      (S.sourceElement a K).right * 1 *
        (S.sourceElement a K).right⁻¹ =
      1
    group

/-- Each selected source coordinate transport intertwines the honest
representative action with the shifted-defect action. -/
theorem canonicalSourceTransport_mul_representativeNormalAction
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o)
    (y : (layerTargetComponentOrbitRepresentative d θ o).1) :
    (canonicalLayerPairedTransport
        d hcoordinate θ o).sourceTransport a K *
        canonicalRepresentativeSourceNormalAction d θ o y =
      canonicalRepresentativeSourceNormalAction d θ o
          (layerTargetOrbitShiftedDefectAutomorphism
            (d := d) (θ := θ) a K y) *
        (canonicalLayerPairedTransport
          d hcoordinate θ o).sourceTransport a K := by
  let S :=
    canonicalOrbitSemidirectSection d hcoordinate θ o
  let L :=
    canonicalOrbitSourceLift d θ o
  change
    L.projective.operator (S.sourceElement a K) *
        L.associated.restriction
          (coordinateSourceNormalCopyHom θ
            (layerTargetComponentOrbitRepresentative d θ o) y) =
      L.associated.restriction
          (coordinateSourceNormalCopyHom θ
            (layerTargetComponentOrbitRepresentative d θ o)
            (layerTargetOrbitShiftedDefectAutomorphism
              (d := d) (θ := θ) a K y)) *
        L.projective.operator (S.sourceElement a K)
  calc
    L.projective.operator (S.sourceElement a K) *
        L.associated.restriction
          (coordinateSourceNormalCopyHom θ
            (layerTargetComponentOrbitRepresentative d θ o) y) =
      L.associated.restriction
          (MulAut.conjNormal (S.sourceElement a K)
            (coordinateSourceNormalCopyHom θ
              (layerTargetComponentOrbitRepresentative d θ o) y)) *
        L.projective.operator (S.sourceElement a K) :=
      L.associated.operator_mul_restriction
        (S.sourceElement a K)
        (coordinateSourceNormalCopyHom θ
          (layerTargetComponentOrbitRepresentative d θ o) y)
    _ =
      L.associated.restriction
          (coordinateSourceNormalCopyHom θ
            (layerTargetComponentOrbitRepresentative d θ o)
            (layerTargetOrbitShiftedDefectAutomorphism
              (d := d) (θ := θ) a K y)) *
        L.projective.operator (S.sourceElement a K) := by
      congr 1
      exact
        congrArg L.associated.restriction
          (coordinateSourceNormalCopyHom_conjNormal S a K y)

/-- The representative-coordinate family obtained after applying one
target-inertia element. -/
def canonicalRepresentativeProductConjugate
    (a : targetInertiaGroup d θ)
    (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ)) :
    LayerOrbitRepresentativeProduct (d := d) (θ := θ) :=
  fun o K ↦
    layerTargetOrbitShiftedDefectAutomorphism
      (d := d) (θ := θ) a K
      (z o (a⁻¹ • K))

/-- Orbitwise source tensor-permutation covariance with the honest
representative tensor action. -/
theorem canonicalOrbitSourceOperator_mul_normalAction
    (o : LayerTargetComponentOrbit d θ)
    (a : targetInertiaGroup d θ)
    (z :
      ∀ _K : LayerTargetOrbitCoordinate d θ o,
        (layerTargetComponentOrbitRepresentative d θ o).1) :
    ((canonicalLayerPairedTransport
        d hcoordinate θ o).sourceCocycle.operator a) *
        canonicalOrbitSourceNormalAction d θ o z =
      canonicalOrbitSourceNormalAction d θ o
          (fun K ↦
            layerTargetOrbitShiftedDefectAutomorphism
              (d := d) (θ := θ) a K
              (z (a⁻¹ • K))) *
        ((canonicalLayerPairedTransport
          d hcoordinate θ o).sourceCocycle.operator a) := by
  exact
    FiniteTensorPermutationCocycle.operator_mul_piTensorCongr_eq_of_coordinate_covariance
      (canonicalLayerPairedTransport
        d hcoordinate θ o).sourceCocycle
      (canonicalRepresentativeSourceNormalAction d θ o)
      a z
      (fun K ↦
        layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K
          (z (a⁻¹ • K)))
      (fun K ↦
        canonicalSourceTransport_mul_representativeNormalAction
          (d := d) (hcoordinate := hcoordinate) (θ := θ)
          a K (z (a⁻¹ • K)))

/-- Tensoring the orbitwise identities gives covariance of the full raw
source tensor-permutation operator with the representative product action. -/
theorem canonicalSourceProjective_operator_mul_normalProductAction
    (a : targetInertiaGroup d θ)
    (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ)) :
    (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceProjective.operator a *
        canonicalSourceNormalProductAction d hcoordinate θ z =
      canonicalSourceNormalProductAction d hcoordinate θ
          (canonicalRepresentativeProductConjugate a z) *
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceProjective.operator a := by
  change
    PiTensorProduct.congr
        (fun o : LayerTargetComponentOrbit d θ ↦
          (canonicalLayerPairedTransport
            d hcoordinate θ o).sourceCocycle.operator a) *
        PiTensorProduct.congr
          (fun o : LayerTargetComponentOrbit d θ ↦
            canonicalOrbitSourceNormalAction d θ o (z o)) =
      PiTensorProduct.congr
          (fun o : LayerTargetComponentOrbit d θ ↦
            canonicalOrbitSourceNormalAction d θ o
              (canonicalRepresentativeProductConjugate a z o)) *
        PiTensorProduct.congr
          (fun o : LayerTargetComponentOrbit d θ ↦
            (canonicalLayerPairedTransport
              d hcoordinate θ o).sourceCocycle.operator a)
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change
    PiTensorProduct.congr
        (fun o : LayerTargetComponentOrbit d θ ↦
          (canonicalLayerPairedTransport
            d hcoordinate θ o).sourceCocycle.operator a)
        (PiTensorProduct.congr
          (fun o : LayerTargetComponentOrbit d θ ↦
            canonicalOrbitSourceNormalAction d θ o (z o))
          (PiTensorProduct.tprod ℂ v)) =
      PiTensorProduct.congr
          (fun o : LayerTargetComponentOrbit d θ ↦
            canonicalOrbitSourceNormalAction d θ o
              (canonicalRepresentativeProductConjugate a z o))
          (PiTensorProduct.congr
            (fun o : LayerTargetComponentOrbit d θ ↦
              (canonicalLayerPairedTransport
                d hcoordinate θ o).sourceCocycle.operator a)
            (PiTensorProduct.tprod ℂ v))
  rw [PiTensorProduct.congr_tprod,
    PiTensorProduct.congr_tprod,
    PiTensorProduct.congr_tprod,
    PiTensorProduct.congr_tprod]
  congr 1
  funext o
  exact
    DFunLike.congr_fun
      (canonicalOrbitSourceOperator_mul_normalAction
        (d := d) (hcoordinate := hcoordinate) (θ := θ)
        o a (z o))
      (v o)

/-- Transporting a shifted-defect coordinate to its output component is
the same as transporting the input coordinate first and then conjugating
by the ambient target-inertia element. -/
theorem layerTargetOrbitCoordinateTransportEquiv_shiftedDefect_apply_coe
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o)
    (y : (layerTargetComponentOrbitRepresentative d θ o).1) :
    ((layerTargetOrbitCoordinateTransportEquiv d θ K
        (layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K y) : K.1.1) : G) =
      (((a : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G) *
        ((layerTargetOrbitCoordinateTransportEquiv d θ
          (a⁻¹ • K) y : (a⁻¹ • K).1.1) : G) *
      (((a : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G)⁻¹ := by
  rw [layerTargetOrbitCoordinateTransportEquiv_apply_coe,
    layerTargetOrbitShiftedDefectAutomorphism_apply_coe,
    layerTargetOrbitCoordinateTransportEquiv_apply_coe]
  simp only [layerTargetOrbitShiftedTransporterDefect,
    layerTargetOrbitTransporterDefect,
    layerTargetOrbitCoordinate_smul_val, smul_inv_smul]
  let tK : G :=
    (((layerTargetComponentTransporter d θ K.1 :
      targetInertiaGroup d θ) : d.ambientIntermediate) : G)
  let tPrev : G :=
    (((layerTargetComponentTransporter d θ (a⁻¹ • K).1 :
      targetInertiaGroup d θ) : d.ambientIntermediate) : G)
  let aG : G :=
    (((a : targetInertiaGroup d θ) :
      d.ambientIntermediate) : G)
  change
    tK * ((tK⁻¹ * aG * tPrev) * (y : G) *
        (tK⁻¹ * aG * tPrev)⁻¹) * tK⁻¹ =
      aG * (tPrev * (y : G) * tPrev⁻¹) * aG⁻¹
  group

/-- The predecessor orbit coordinate is the canonical sigma-coordinate of
its underlying component. -/
theorem layerTargetOrbitCoordinateSigma_predecessor
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o) :
    (⟨o, a⁻¹ • K⟩ :
      Σ u : LayerTargetComponentOrbit d θ,
        LayerTargetOrbitCoordinate d θ u) =
      (layerTargetOrbitCoordinateSigmaEquiv d θ).symm
        (a⁻¹ • K).1 := by
  apply (layerTargetOrbitCoordinateSigmaEquiv d θ).injective
  rfl

/-- Evaluate one nested representative coordinate in the ambient group.
Naming this dependent evaluation keeps later transport arguments small. -/
def layerOrbitRepresentativeCoordinateToAmbient
    (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ))
    (s :
      Σ o : LayerTargetComponentOrbit d θ,
        LayerTargetOrbitCoordinate d θ o) :
    G :=
  ((layerTargetOrbitCoordinateTransportEquiv d θ s.2
    (z s.1 s.2) : s.2.1.1) : G)

/-- Looking up a predecessor representative through the nested orbit
coordinates agrees with the flattened component-product lookup. -/
theorem layerTargetOrbitCoordinateTransportEquiv_predecessor_apply_coe
    {o : LayerTargetComponentOrbit d θ}
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o)
    (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ)) :
    ((layerTargetOrbitCoordinateTransportEquiv d θ
        (a⁻¹ • K) (z o (a⁻¹ • K)) :
      (a⁻¹ • K).1.1) : G) =
      ((layerOrbitRepresentativeToComponentProduct d θ z
        (a⁻¹ • K).1 : (a⁻¹ • K).1.1) : G) := by
  have hs :=
    layerTargetOrbitCoordinateSigma_predecessor
      (d := d) (θ := θ) a K
  change
    layerOrbitRepresentativeCoordinateToAmbient
        (d := d) (θ := θ) z ⟨o, a⁻¹ • K⟩ =
      layerOrbitRepresentativeCoordinateToAmbient
        (d := d) (θ := θ) z
          ((layerTargetOrbitCoordinateSigmaEquiv d θ).symm
            (a⁻¹ • K).1)
  exact
    congrArg
      (layerOrbitRepresentativeCoordinateToAmbient
        (d := d) (θ := θ) z)
      hs

/-- Coordinatewise form of representative-product conjugation after
transport to the actual component. -/
theorem layerOrbitRepresentativeToComponentProduct_conjugate_apply_coe
    (a : targetInertiaGroup d θ)
    (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ))
    (K : ComponentIndex G) :
    ((layerOrbitRepresentativeToComponentProduct d θ
        (canonicalRepresentativeProductConjugate a z) K : K.1) : G) =
      ((layerComponentProductConjugation G
        ((((a : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G))
        (layerOrbitRepresentativeToComponentProduct d θ z) K : K.1) : G) := by
  let K₀ :
      LayerTargetOrbitCoordinate d θ
        (layerTargetComponentOrbitOf d θ K) :=
    ⟨K, rfl⟩
  change
    ((layerTargetOrbitCoordinateTransportEquiv d θ K₀
        (layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K₀
          (z (layerTargetComponentOrbitOf d θ K)
            (a⁻¹ • K₀))) : K.1) : G) =
      ((layerComponentProductConjugation G
        ((((a : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G))
        (layerOrbitRepresentativeToComponentProduct d θ z) K :
          K.1) : G)
  rw [
    layerTargetOrbitCoordinateTransportEquiv_shiftedDefect_apply_coe,
    layerComponentProductConjugation_apply_coe]
  congr 1
  rw [mul_left_cancel_iff]
  change
    ((layerTargetOrbitCoordinateTransportEquiv d θ
        (a⁻¹ • K₀)
        (z (layerTargetComponentOrbitOf d θ K)
          (a⁻¹ • K₀)) : (a⁻¹ • K₀).1.1) : G) =
      ((layerOrbitRepresentativeToComponentProduct d θ z
        (((((a : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G))⁻¹ • K) :
          (((((a : targetInertiaGroup d θ) :
            d.ambientIntermediate) : G))⁻¹ • K).1) : G)
  have hindex :
      (((((a : targetInertiaGroup d θ) :
        d.ambientIntermediate) : G))⁻¹ • K) =
        (a⁻¹ • K₀).1 := by
    rfl
  rw [hindex]
  exact
    layerTargetOrbitCoordinateTransportEquiv_predecessor_apply_coe
      (d := d) (θ := θ) a K₀ z

/-- The shifted representative family becomes ordinary component-product
conjugation after transporting every representative to its component. -/
theorem layerOrbitRepresentativeToComponentProduct_conjugate
    (a : targetInertiaGroup d θ)
    (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ)) :
    layerOrbitRepresentativeToComponentProduct d θ
        (canonicalRepresentativeProductConjugate a z) =
      layerComponentProductConjugation G
        ((((a : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G))
        (layerOrbitRepresentativeToComponentProduct d θ z) := by
  funext K
  apply Subtype.ext
  exact
    layerOrbitRepresentativeToComponentProduct_conjugate_apply_coe
      a z K

/-- Representative-product conjugation descends to ambient conjugation on
the layer. -/
theorem layerOrbitRepresentativeProductHom_conjugate
    (a : targetInertiaGroup d θ)
    (z : LayerOrbitRepresentativeProduct (d := d) (θ := θ)) :
    layerOrbitRepresentativeProductHom d θ
        (canonicalRepresentativeProductConjugate a z) =
      (MulAut.conjNormal
        ((((a : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G)) :
          MulAut (layer G))
        (layerOrbitRepresentativeProductHom d θ z) := by
  change
    layerProductHom G
        (layerOrbitRepresentativeToComponentProduct d θ
          (canonicalRepresentativeProductConjugate a z)) =
      (MulAut.conjNormal
        ((((a : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G)) :
          MulAut (layer G))
        (layerProductHom G
          (layerOrbitRepresentativeToComponentProduct d θ z))
  rw [layerOrbitRepresentativeToComponentProduct_conjugate]
  exact
    DFunLike.congr_fun
      (layerProductHom_comp_conjugation G
        ((((a : targetInertiaGroup d θ) :
          d.ambientIntermediate) : G)))
      (layerOrbitRepresentativeToComponentProduct d θ z)

/-- The canonical copy of the layer in its inertia group carries intrinsic
conjugation to ambient conjugation on the layer. -/
theorem sourceNormalCopyEquiv_conjNormal
    (a : sourceInertiaGroup θ)
    (x : (sourceTriple θ).normalSubgroup) :
    CliffordEquivalence.inertiaNormalCopyEquiv
        (layer G) θ.1
        (MulAut.conjNormal a x) =
      (MulAut.conjNormal (a : G) :
          MulAut (layer G))
        (CliffordEquivalence.inertiaNormalCopyEquiv
          (layer G) θ.1 x) := by
  apply Subtype.ext
  rfl

/-- Every raw source tensor-permutation operator implements the conjugation
action of the embedded target inertia group on the intrinsic irreducible
source normal restriction. -/
theorem canonicalSourceProjective_normalCovariance
    (a : targetInertiaGroup d θ)
    (x : (sourceTriple θ).normalSubgroup) :
    (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceProjective.operator a *
        canonicalCoherentSourceNormalRestriction
          d hcoordinate θ x =
      canonicalCoherentSourceNormalRestriction
          d hcoordinate θ
          (MulAut.conjNormal
            (inertiaEmbedding d hcoordinate θ a) x) *
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceProjective.operator a := by
  obtain ⟨z, hz⟩ :=
    layerOrbitRepresentativeProductHom_surjective d θ
      (CliffordEquivalence.inertiaNormalCopyEquiv
        (layer G) θ.1 x)
  have hconjugate :
      layerOrbitRepresentativeProductHom d θ
          (canonicalRepresentativeProductConjugate a z) =
        CliffordEquivalence.inertiaNormalCopyEquiv
          (layer G) θ.1
          (MulAut.conjNormal
            (inertiaEmbedding d hcoordinate θ a) x) := by
    rw [layerOrbitRepresentativeProductHom_conjugate,
      sourceNormalCopyEquiv_conjNormal, inertiaEmbedding_apply_coe, hz]
  calc
    (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceProjective.operator a *
        canonicalCoherentSourceNormalRestriction
          d hcoordinate θ x =
      (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceProjective.operator a *
        canonicalCoherentSourceLayerAction d hcoordinate θ
          (layerOrbitRepresentativeProductHom d θ z) := by
            rw [hz]
            rfl
    _ =
      (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceProjective.operator a *
        canonicalSourceNormalProductAction
          d hcoordinate θ z := by
            rw [canonicalCoherentSourceLayerAction_product]
    _ =
      canonicalSourceNormalProductAction d hcoordinate θ
          (canonicalRepresentativeProductConjugate a z) *
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceProjective.operator a :=
            canonicalSourceProjective_operator_mul_normalProductAction
              a z
    _ =
      canonicalCoherentSourceLayerAction d hcoordinate θ
          (layerOrbitRepresentativeProductHom d θ
            (canonicalRepresentativeProductConjugate a z)) *
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceProjective.operator a := by
            rw [canonicalCoherentSourceLayerAction_product]
    _ =
      canonicalCoherentSourceNormalRestriction
          d hcoordinate θ
          (MulAut.conjNormal
            (inertiaEmbedding d hcoordinate θ a) x) *
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).sourceProjective.operator a := by
            rw [hconjugate]
            rfl

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
