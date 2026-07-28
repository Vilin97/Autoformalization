/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteTensorScalarExtraction
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentNormalCharacter
import McKayConjecture.InductiveMcKay.LayerProjectiveRestrictionAssociation

/-!
# Common normal trace scalar from coherent coordinates

For every coordinate fixed by a target-normal element, the coherent
representative coordinate identifies the source and target local transport
traces with one common nonzero scalar times the matched local character
values.  Multiplying those scalars gives one global scalar for both raw
canonical tensor traces.
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

noncomputable local instance coherentNormalTraceComponentIndexFintype :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite _

/-- The normal map supplied by the canonical matched-inertia embedding is
the explicit source normal copy used by the coherent-coordinate formulas. -/
@[simp]
theorem centralRestriction_normalMap_eq_targetNormalSourceCopy
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
    (x : (targetTriple d θ).normalSubgroup) :
    g.normalMap x = targetNormalSourceCopy x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [g.normalMap_coe]
  rw [inertiaEmbedding_apply_coe]
  change
    ((((x : targetInertiaGroup d θ) :
      d.ambientIntermediate) : G)) =
      (((targetNormalLayerLocal x :
        layerLocalSubgroup G d.intermediate) : layer G) : G)
  calc
    ((((x : targetInertiaGroup d θ) :
        d.ambientIntermediate) : G)) =
        (((targetNormalOriginal x :
          d.intermediateComponentLocal) :
          d.ambientIntermediate) : G) := by
      rfl
    _ =
        (((targetNormalComponentLocalInLayer x :
          componentLocalSubgroupInLayer
            G d.intermediate) : layer G) : G) :=
      (layerIntermediateComponentLocalEquivInLayer_apply_coe
        G Q d.intermediate (targetNormalOriginal x)).symm
    _ =
        (((targetNormalLayerLocal x :
          layerLocalSubgroup G d.intermediate) : layer G) : G) := by
      exact congrArg
        (fun z : layer G ↦ (z : G))
        (d.toLayerComponentLocalData
          |>.componentLocalInLayerEquivLayerLocal_apply_coe
            (targetNormalComponentLocalInLayer x)).symm

/-- The common nonzero scalar at one coordinate, obtained from a specified
transporter decomposition and its coherent representative coordinate. -/
def coherentCoordinateTraceScalarOfDecomposition
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    ℂˣ :=
  Classical.choose
    (exists_common_coordinate_operator_scalar_of_inducedAction
      (canonicalOrbitSemidirectSection d hcoordinate θ o)
      (x : targetInertiaGroup d θ) K
      (coherentRepresentativeNormalCoordinateOfDecomposition
        x K T)
      (coherentRepresentativeNormalCoordinateOfDecomposition_inducedAction
        x K T))

/-- Local source transport operator in terms of the coherent normal
coordinate and the chosen common scalar. -/
theorem canonicalOrbitSourceTransport_operator_normal_of_decomposition
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    (canonicalLayerPairedTransport
      d hcoordinate θ o).sourceTransport
        (x : targetInertiaGroup d θ) K =
      scalarLinearEquiv ℂ
          (canonicalOrbitSourceSpace d θ o)
          (coherentCoordinateTraceScalarOfDecomposition x K T) *
        (d.coordinateAmbientLift θ
          (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
            (coordinateSourceNormalElement
              (d := d) (θ := θ)
              (layerTargetComponentOrbitRepresentative d θ o)
              (coherentRepresentativeNormalCoordinateOfDecomposition
                x K T)) := by
  change
    (canonicalOrbitSemidirectSection
      d hcoordinate θ o).sourceTransport
        (x : targetInertiaGroup d θ) K =
      _
  exact
    (Classical.choose_spec
      (exists_common_coordinate_operator_scalar_of_inducedAction
        (canonicalOrbitSemidirectSection d hcoordinate θ o)
        (x : targetInertiaGroup d θ) K
        (coherentRepresentativeNormalCoordinateOfDecomposition
          x K T)
        (coherentRepresentativeNormalCoordinateOfDecomposition_inducedAction
          x K T))).1

/-- Local target transport operator in terms of the same coherent normal
coordinate and common scalar. -/
theorem canonicalOrbitTargetTransport_operator_normal_of_decomposition
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    (canonicalLayerPairedTransport
      d hcoordinate θ o).targetTransport
        (x : targetInertiaGroup d θ) K =
      scalarLinearEquiv ℂ
          (canonicalOrbitTargetSpace d θ o)
          (coherentCoordinateTraceScalarOfDecomposition x K T) *
        (d.coordinateIntermediateLift θ
          (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
            (coordinateTargetNormalElement
              (d := d) (θ := θ)
              (layerTargetComponentOrbitRepresentative d θ o)
              (coherentRepresentativeNormalCoordinateOfDecomposition
                x K T)) := by
  change
    (canonicalOrbitSemidirectSection
      d hcoordinate θ o).targetTransport
        (x : targetInertiaGroup d θ) K =
      _
  exact
    (Classical.choose_spec
      (exists_common_coordinate_operator_scalar_of_inducedAction
        (canonicalOrbitSemidirectSection d hcoordinate θ o)
        (x : targetInertiaGroup d θ) K
        (coherentRepresentativeNormalCoordinateOfDecomposition
          x K T)
        (coherentRepresentativeNormalCoordinateOfDecomposition_inducedAction
          x K T))).2

/-- Local source transport trace in terms of the original central-product
coordinate and the common coherent-coordinate scalar. -/
theorem canonicalOrbitSourceTransport_trace_normal_of_decomposition
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    LinearMap.trace ℂ (canonicalOrbitSourceSpace d θ o)
        ((canonicalLayerPairedTransport
          d hcoordinate θ o).sourceTransport
            (x : targetInertiaGroup d θ) K) =
      (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) *
        (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.values
          (targetNormalCoordinateFamily x K.1) := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let y :=
    coherentRepresentativeNormalCoordinateOfDecomposition x K T
  let Ls := d.coordinateAmbientLift θ R
  let xn :=
    coordinateSourceNormalElement (d := d) (θ := θ) R y
  have hop :=
    canonicalOrbitSourceTransport_operator_normal_of_decomposition
      x K T
  have hopLinear :=
    congrArg LinearEquiv.toLinearMap hop
  change
    ((canonicalLayerPairedTransport
      d hcoordinate θ o).sourceTransport
        (x : targetInertiaGroup d θ) K :
      canonicalOrbitSourceSpace d θ o →ₗ[ℂ]
        canonicalOrbitSourceSpace d θ o) =
      (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) •
        (Ls.projective.operator
          (xn :
            ComponentOrbitLocalData.coordinateAmbientGroup
              (D := D) θ R) :
          canonicalOrbitSourceSpace d θ o →ₗ[ℂ]
            canonicalOrbitSourceSpace d θ o)
    at hopLinear
  rw [hopLinear, map_smul]
  have htrace := Ls.associated.traceFunction_normal xn
  change
    LinearMap.trace ℂ (canonicalOrbitSourceSpace d θ o)
        (Ls.projective.operator
          (xn :
            ComponentOrbitLocalData.coordinateAmbientGroup
              (D := D) θ R)) =
      (ComponentOrbitLocalData.coordinateLayerCharacter θ R).1.values y
    at htrace
  calc
    (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) •
        LinearMap.trace ℂ (canonicalOrbitSourceSpace d θ o)
          (Ls.projective.operator
            (xn :
              ComponentOrbitLocalData.coordinateAmbientGroup
                (D := D) θ R)) =
        (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) *
          (ComponentOrbitLocalData.coordinateLayerCharacter θ R).1.values
            y := by rw [htrace, smul_eq_mul]
    _ =
        (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) *
          (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1).1.values
            (targetNormalCoordinateFamily x K.1) := by
      rw [
        coordinateLayerCharacter_values_coherentRepresentativeOfDecomposition
          x K T]

/-- Local target transport trace in terms of the original central-product
coordinate and the same coherent-coordinate scalar. -/
theorem canonicalOrbitTargetTransport_trace_normal_of_decomposition
    (x : (targetTriple d θ).normalSubgroup)
    {o : LayerTargetComponentOrbit d θ}
    (K : LayerTargetOrbitCoordinate d θ o)
    (T :
      LayerTargetTransporterDecomposition
        d hcoordinate θ K.1) :
    LinearMap.trace ℂ (canonicalOrbitTargetSpace d θ o)
        ((canonicalLayerPairedTransport
          d hcoordinate θ o).targetTransport
            (x : targetInertiaGroup d θ) K) =
      (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) *
        (d.correspondence K.1
          (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.values
            (targetNormalCoordinateFamily x K.1) := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let y :=
    coherentRepresentativeNormalCoordinateOfDecomposition x K T
  let Lt := d.coordinateIntermediateLift θ R
  let yn :=
    coordinateTargetNormalElement (d := d) (θ := θ) R y
  have hop :=
    canonicalOrbitTargetTransport_operator_normal_of_decomposition
      x K T
  have hopLinear :=
    congrArg LinearEquiv.toLinearMap hop
  change
    ((canonicalLayerPairedTransport
      d hcoordinate θ o).targetTransport
        (x : targetInertiaGroup d θ) K :
      canonicalOrbitTargetSpace d θ o →ₗ[ℂ]
        canonicalOrbitTargetSpace d θ o) =
      (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) •
        (Lt.projective.operator
          (yn : d.coordinateIntermediateGroup θ R) :
          canonicalOrbitTargetSpace d θ o →ₗ[ℂ]
            canonicalOrbitTargetSpace d θ o)
    at hopLinear
  rw [hopLinear, map_smul]
  have htrace := Lt.associated.traceFunction_normal yn
  change
    LinearMap.trace ℂ (canonicalOrbitTargetSpace d θ o)
        (Lt.projective.operator
          (yn : d.coordinateIntermediateGroup θ R)) =
      (d.correspondence R
        (ComponentOrbitLocalData.coordinateLayerCharacter θ R)).1.values y
    at htrace
  calc
    (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) •
        LinearMap.trace ℂ (canonicalOrbitTargetSpace d θ o)
          (Lt.projective.operator
            (yn : d.coordinateIntermediateGroup θ R)) =
        (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) *
          (d.correspondence R
            (ComponentOrbitLocalData.coordinateLayerCharacter θ R)).1.values
              y := by rw [htrace, smul_eq_mul]
    _ =
        (coherentCoordinateTraceScalarOfDecomposition x K T : ℂ) *
          (d.correspondence K.1
            (ComponentOrbitLocalData.coordinateLayerCharacter θ K.1)).1.values
              (targetNormalCoordinateFamily x K.1) := by
      rw [
        coordinateLocalCharacter_values_coherentRepresentativeOfDecomposition
          x K T]

/-- A coherent transporter-decomposition choice at every canonical orbit
coordinate. -/
abbrev CoherentNormalTransporterDecompositionFamily :=
  ∀ (o : LayerTargetComponentOrbit d θ)
    (K : LayerTargetOrbitCoordinate d θ o),
    LayerTargetTransporterDecomposition d hcoordinate θ K.1

/-- Product of all local coherent-coordinate trace scalars for an arbitrary
coherent transporter-decomposition family. -/
def coherentNormalTraceScalarOfDecompositionFamily
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup) :
    ℂˣ :=
  ∏ o, ∏ K,
    coherentCoordinateTraceScalarOfDecomposition x K (T o K)

/-- The tensor of the coherent source normal-coordinate operators on one
component orbit. -/
def coherentOrbitSourceNormalOperator
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup)
    (o : LayerTargetComponentOrbit d θ) :
    (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
      canonicalOrbitSourceSpace d θ o) ≃ₗ[ℂ]
    (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
      canonicalOrbitSourceSpace d θ o) := by
  letI :
      ∀ _K : LayerTargetOrbitCoordinate d θ o,
        AddCommGroup (canonicalOrbitSourceSpace d θ o) :=
    fun _ ↦ inferInstance
  letI :
      ∀ _K : LayerTargetOrbitCoordinate d θ o,
        Module ℂ (canonicalOrbitSourceSpace d θ o) :=
    fun _ ↦ inferInstance
  change
    (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
      canonicalOrbitSourceSpace d θ o) ≃ₗ[ℂ]
    (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
      canonicalOrbitSourceSpace d θ o)
  exact
    PiTensorProduct.congr
      (fun K ↦
        (d.coordinateAmbientLift θ
          (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
            (coordinateSourceNormalElement
              (d := d) (θ := θ)
              (layerTargetComponentOrbitRepresentative d θ o)
              (coherentRepresentativeNormalCoordinateOfDecomposition
                x K (T o K))))

/-- The tensor of the coherent target normal-coordinate operators on one
component orbit. -/
def coherentOrbitTargetNormalOperator
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup)
    (o : LayerTargetComponentOrbit d θ) :
    (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
      canonicalOrbitTargetSpace d θ o) ≃ₗ[ℂ]
    (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
      canonicalOrbitTargetSpace d θ o) := by
  letI :
      ∀ _K : LayerTargetOrbitCoordinate d θ o,
        AddCommGroup (canonicalOrbitTargetSpace d θ o) :=
    fun _ ↦ inferInstance
  letI :
      ∀ _K : LayerTargetOrbitCoordinate d θ o,
        Module ℂ (canonicalOrbitTargetSpace d θ o) :=
    fun _ ↦ inferInstance
  change
    (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
      canonicalOrbitTargetSpace d θ o) ≃ₗ[ℂ]
    (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
      canonicalOrbitTargetSpace d θ o)
  exact
    PiTensorProduct.congr
      (fun K ↦
        (d.coordinateIntermediateLift θ
          (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
            (coordinateTargetNormalElement
              (d := d) (θ := θ)
              (layerTargetComponentOrbitRepresentative d θ o)
              (coherentRepresentativeNormalCoordinateOfDecomposition
                x K (T o K))))

/-- The full tensor of the coherent source normal-coordinate operators. -/
def coherentSourceNormalOperator
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup) :
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ]
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).sourceTensorSpace :=
  PiTensorProduct.congr
    (coherentOrbitSourceNormalOperator T x)

/-- The full tensor of the coherent target normal-coordinate operators. -/
def coherentTargetNormalOperator
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup) :
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).targetTensorSpace ≃ₗ[ℂ]
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).targetTensorSpace :=
  PiTensorProduct.congr
    (coherentOrbitTargetNormalOperator T x)

/-- On one orbit, the raw source tensor-permutation operator is the product
of the coherent coordinate scalars times the coherent normal operator. -/
theorem canonicalSourceCocycle_operator_normal_eq_commonScalar_mul_of_decompositionFamily
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup)
    (o : LayerTargetComponentOrbit d θ) :
    (canonicalLayerPairedTransport
      d hcoordinate θ o).sourceCocycle.operator
        (x : targetInertiaGroup d θ) =
      scalarLinearEquiv ℂ
          (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
            canonicalOrbitSourceSpace d θ o)
          (∏ K : LayerTargetOrbitCoordinate d θ o,
            coherentCoordinateTraceScalarOfDecomposition
              x K (T o K)) *
        coherentOrbitSourceNormalOperator T x o := by
  rw [
    (canonicalLayerPairedTransport
      d hcoordinate θ o).sourceCocycle.operator_eq_congr_of_fixed
        (x : targetInertiaGroup d θ)
        (targetNormal_smul_orbitCoordinate_eq x)]
  calc
    PiTensorProduct.congr
        (fun K ↦
          (canonicalLayerPairedTransport
            d hcoordinate θ o).sourceTransport
              (x : targetInertiaGroup d θ) K) =
      PiTensorProduct.congr
        (fun K ↦
          scalarLinearEquiv ℂ
              (canonicalOrbitSourceSpace d θ o)
              (coherentCoordinateTraceScalarOfDecomposition
                x K (T o K)) *
            (d.coordinateAmbientLift θ
              (layerTargetComponentOrbitRepresentative
                d θ o)).projective.operator
                (coordinateSourceNormalElement
                  (d := d) (θ := θ)
                  (layerTargetComponentOrbitRepresentative d θ o)
                  (coherentRepresentativeNormalCoordinateOfDecomposition
                    x K (T o K)))) := by
      congr 1
      funext K
      exact
        canonicalOrbitSourceTransport_operator_normal_of_decomposition
          x K (T o K)
    _ = _ :=
      piTensorCongr_scalar_mul
        (fun K ↦
          coherentCoordinateTraceScalarOfDecomposition x K (T o K))
        (fun K ↦
          (d.coordinateAmbientLift θ
            (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
              (coordinateSourceNormalElement
                (d := d) (θ := θ)
                (layerTargetComponentOrbitRepresentative d θ o)
                (coherentRepresentativeNormalCoordinateOfDecomposition
                  x K (T o K))))

/-- On one orbit, the raw target tensor-permutation operator has the same
product scalar times the coherent target normal operator. -/
theorem canonicalTargetCocycle_operator_normal_eq_commonScalar_mul_of_decompositionFamily
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup)
    (o : LayerTargetComponentOrbit d θ) :
    (canonicalLayerPairedTransport
      d hcoordinate θ o).targetCocycle.operator
        (x : targetInertiaGroup d θ) =
      scalarLinearEquiv ℂ
          (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
            canonicalOrbitTargetSpace d θ o)
          (∏ K : LayerTargetOrbitCoordinate d θ o,
            coherentCoordinateTraceScalarOfDecomposition
              x K (T o K)) *
        coherentOrbitTargetNormalOperator T x o := by
  rw [
    (canonicalLayerPairedTransport
      d hcoordinate θ o).targetCocycle.operator_eq_congr_of_fixed
        (x : targetInertiaGroup d θ)
        (targetNormal_smul_orbitCoordinate_eq x)]
  calc
    PiTensorProduct.congr
        (fun K ↦
          (canonicalLayerPairedTransport
            d hcoordinate θ o).targetTransport
              (x : targetInertiaGroup d θ) K) =
      PiTensorProduct.congr
        (fun K ↦
          scalarLinearEquiv ℂ
              (canonicalOrbitTargetSpace d θ o)
              (coherentCoordinateTraceScalarOfDecomposition
                x K (T o K)) *
            (d.coordinateIntermediateLift θ
              (layerTargetComponentOrbitRepresentative
                d θ o)).projective.operator
                (coordinateTargetNormalElement
                  (d := d) (θ := θ)
                  (layerTargetComponentOrbitRepresentative d θ o)
                  (coherentRepresentativeNormalCoordinateOfDecomposition
                    x K (T o K)))) := by
      congr 1
      funext K
      exact
        canonicalOrbitTargetTransport_operator_normal_of_decomposition
          x K (T o K)
    _ = _ :=
      piTensorCongr_scalar_mul
        (fun K ↦
          coherentCoordinateTraceScalarOfDecomposition x K (T o K))
        (fun K ↦
          (d.coordinateIntermediateLift θ
            (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
              (coordinateTargetNormalElement
                (d := d) (θ := θ)
                (layerTargetComponentOrbitRepresentative d θ o)
                (coherentRepresentativeNormalCoordinateOfDecomposition
                  x K (T o K))))

/-- The raw canonical source operator is the common nonzero scalar times the
full coherent source normal operator. -/
theorem canonicalSourceProjective_operator_normal_eq_commonScalar_mul_of_decompositionFamily
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    F.sourceProjective.operator
        (x : targetInertiaGroup d θ) =
      scalarLinearEquiv ℂ F.sourceTensorSpace
          (coherentNormalTraceScalarOfDecompositionFamily T x) *
        coherentSourceNormalOperator T x := by
  dsimp only [
    LayerTensorPermutationCocycleFamily.sourceProjective,
    ProjectiveRepresentation.piTensor_operator,
    ProjectiveRepresentation.piTensorOperator]
  calc
    PiTensorProduct.congr
        (fun o ↦
          (canonicalLayerPairedTransport
            d hcoordinate θ o).sourceCocycle.operator
              (x : targetInertiaGroup d θ)) =
      PiTensorProduct.congr
        (fun o ↦
          scalarLinearEquiv ℂ
              (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
                canonicalOrbitSourceSpace d θ o)
              (∏ K : LayerTargetOrbitCoordinate d θ o,
                coherentCoordinateTraceScalarOfDecomposition
                  x K (T o K)) *
            coherentOrbitSourceNormalOperator T x o) := by
      congr 1
      funext o
      exact
        canonicalSourceCocycle_operator_normal_eq_commonScalar_mul_of_decompositionFamily
          T x o
    _ = _ :=
      piTensorCongr_scalar_mul
        (fun o ↦ ∏ K,
          coherentCoordinateTraceScalarOfDecomposition x K (T o K))
        (coherentOrbitSourceNormalOperator T x)

/-- The raw canonical target operator has exactly the same common scalar
times the full coherent target normal operator. -/
theorem canonicalTargetProjective_operator_normal_eq_commonScalar_mul_of_decompositionFamily
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    F.targetProjective.operator
        (x : targetInertiaGroup d θ) =
      scalarLinearEquiv ℂ F.targetTensorSpace
          (coherentNormalTraceScalarOfDecompositionFamily T x) *
        coherentTargetNormalOperator T x := by
  dsimp only [
    LayerTensorPermutationCocycleFamily.targetProjective,
    ProjectiveRepresentation.piTensor_operator,
    ProjectiveRepresentation.piTensorOperator]
  calc
    PiTensorProduct.congr
        (fun o ↦
          (canonicalLayerPairedTransport
            d hcoordinate θ o).targetCocycle.operator
              (x : targetInertiaGroup d θ)) =
      PiTensorProduct.congr
        (fun o ↦
          scalarLinearEquiv ℂ
              (⨂[ℂ] _K : LayerTargetOrbitCoordinate d θ o,
                canonicalOrbitTargetSpace d θ o)
              (∏ K : LayerTargetOrbitCoordinate d θ o,
                coherentCoordinateTraceScalarOfDecomposition
                  x K (T o K)) *
            coherentOrbitTargetNormalOperator T x o) := by
      congr 1
      funext o
      exact
        canonicalTargetCocycle_operator_normal_eq_commonScalar_mul_of_decompositionFamily
          T x o
    _ = _ :=
      piTensorCongr_scalar_mul
        (fun o ↦ ∏ K,
          coherentCoordinateTraceScalarOfDecomposition x K (T o K))
        (coherentOrbitTargetNormalOperator T x)

/-- With any coherent decomposition family, the raw canonical source trace
is one nonzero global scalar times the source normal-character value. -/
theorem canonicalSourceProjective_trace_normal_eq_commonScalar_mul_of_decompositionFamily
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    LinearMap.trace ℂ F.sourceTensorSpace
        (F.sourceProjective.operator
          (x : targetInertiaGroup d θ)) =
      (coherentNormalTraceScalarOfDecompositionFamily T x : ℂ) *
        (sourceTriple θ).character.values (targetNormalSourceCopy x) := by
  dsimp only
  rw [canonicalSourceProjective_trace_normal]
  simp_rw [
    canonicalOrbitSourceTransport_trace_normal_of_decomposition
      x _ (T _ _)]
  rw [
    sourceTriple_character_values_targetNormalSourceCopy_eq_orbitCoordinateProduct]
  simp only [coherentNormalTraceScalarOfDecompositionFamily,
    Finset.prod_mul_distrib, Units.coe_prod]

/-- With the same arbitrary coherent decomposition family, the raw
canonical target trace uses exactly the same nonzero global scalar. -/
theorem canonicalTargetProjective_trace_normal_eq_commonScalar_mul_of_decompositionFamily
    (T : CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ))
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    LinearMap.trace ℂ F.targetTensorSpace
        (F.targetProjective.operator
          (x : targetInertiaGroup d θ)) =
      (coherentNormalTraceScalarOfDecompositionFamily T x : ℂ) *
        (targetTriple d θ).character.values x := by
  dsimp only
  rw [canonicalTargetProjective_trace_normal]
  simp_rw [
    canonicalOrbitTargetTransport_trace_normal_of_decomposition
      x _ (T _ _)]
  rw [targetTriple_character_values_normal_eq_orbitCoordinateProduct]
  simp only [coherentNormalTraceScalarOfDecompositionFamily,
    Finset.prod_mul_distrib, Units.coe_prod]

/-- The canonical selected transporter decomposition at every orbit
coordinate. -/
def coherentNormalTransporterDecompositionFamily
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    CoherentNormalTransporterDecompositionFamily
      (d := d) (hcoordinate := hcoordinate) (θ := θ) :=
  fun _ K ↦
    layerTargetTransporterDecomposition d hcoordinate θ K.1

/-- The canonical product of the selected coherent-coordinate trace
scalars. -/
def coherentNormalTraceScalar
    (x : (targetTriple d θ).normalSubgroup) :
    ℂˣ :=
  coherentNormalTraceScalarOfDecompositionFamily
    (coherentNormalTransporterDecompositionFamily d hcoordinate θ) x

/-- The canonically selected coherent source normal operator. -/
def canonicalCoherentSourceNormalOperator
    (x : (targetTriple d θ).normalSubgroup) :
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ]
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).sourceTensorSpace :=
  coherentSourceNormalOperator
    (coherentNormalTransporterDecompositionFamily
      d hcoordinate θ) x

/-- The canonically selected coherent target normal operator. -/
def canonicalCoherentTargetNormalOperator
    (x : (targetTriple d θ).normalSubgroup) :
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).targetTensorSpace ≃ₗ[ℂ]
    (canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ).targetTensorSpace :=
  coherentTargetNormalOperator
    (coherentNormalTransporterDecompositionFamily
      d hcoordinate θ) x

/-- Canonical selected-coordinate source normal-operator formula. -/
theorem canonicalSourceProjective_operator_normal_eq_commonScalar_mul
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    F.sourceProjective.operator
        (x : targetInertiaGroup d θ) =
      scalarLinearEquiv ℂ F.sourceTensorSpace
          (coherentNormalTraceScalar
            (hcoordinate := hcoordinate) x) *
        canonicalCoherentSourceNormalOperator
          (hcoordinate := hcoordinate) x :=
  canonicalSourceProjective_operator_normal_eq_commonScalar_mul_of_decompositionFamily
    (coherentNormalTransporterDecompositionFamily d hcoordinate θ) x

/-- Canonical selected-coordinate target normal-operator formula, with the
same scalar as the source formula. -/
theorem canonicalTargetProjective_operator_normal_eq_commonScalar_mul
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    F.targetProjective.operator
        (x : targetInertiaGroup d θ) =
      scalarLinearEquiv ℂ F.targetTensorSpace
          (coherentNormalTraceScalar
            (hcoordinate := hcoordinate) x) *
        canonicalCoherentTargetNormalOperator
          (hcoordinate := hcoordinate) x :=
  canonicalTargetProjective_operator_normal_eq_commonScalar_mul_of_decompositionFamily
    (coherentNormalTransporterDecompositionFamily d hcoordinate θ) x

/-- Canonical selected-coordinate source normal-trace formula. -/
theorem canonicalSourceProjective_trace_normal_eq_commonScalar_mul
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    LinearMap.trace ℂ F.sourceTensorSpace
        (F.sourceProjective.operator
          (x : targetInertiaGroup d θ)) =
      (coherentNormalTraceScalar
        (hcoordinate := hcoordinate) x : ℂ) *
        (sourceTriple θ).character.values (targetNormalSourceCopy x) :=
  canonicalSourceProjective_trace_normal_eq_commonScalar_mul_of_decompositionFamily
    (coherentNormalTransporterDecompositionFamily d hcoordinate θ) x

/-- Canonical selected-coordinate target normal-trace formula, with exactly
the same scalar as the source formula. -/
theorem canonicalTargetProjective_trace_normal_eq_commonScalar_mul
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    LinearMap.trace ℂ F.targetTensorSpace
        (F.targetProjective.operator
          (x : targetInertiaGroup d θ)) =
      (coherentNormalTraceScalar
        (hcoordinate := hcoordinate) x : ℂ) *
        (targetTriple d θ).character.values x :=
  canonicalTargetProjective_trace_normal_eq_commonScalar_mul_of_decompositionFamily
    (coherentNormalTransporterDecompositionFamily d hcoordinate θ) x

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
