/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.Product
import McKayConjecture.InductiveMcKay.LayerProjectiveRestrictionAssembly

/-!
# Independent target projective assembly for the layer inertia triples

A central-isomorphism witness does not require its two associated projective
representations to act on the same vector space.  This file therefore replaces
literal restriction by an independently assembled associated lift on the
target inertia triple.

The comparison is made on realized coordinate charts.  Exact agreement of the
coordinate and complementary factor sets implies exact agreement of the
global factor sets on every chart.  Likewise, common scalar actions on the two
coordinate factors and on the two complementary factors imply common scalar
actions on the two global lifts.

The final layer structure records chart coverage separately.  Thus no global
factor-set or centralizer-scalar conclusion is assumed as a field: both are
derived from local tensor data and coverage by realized charts.
-/

noncomputable section

open scoped TensorProduct

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open GroupTheory

/-! ### Comparison of two independently assembled charts -/

variable {A₀ B₀ A B : Type}
variable [Group A₀] [Finite A₀] [Group B₀] [Finite B₀]
variable [Group A] [Finite A] [Group B] [Finite B]
variable {R₀ : CompleteProjectiveLift A₀}
variable {S₀ : CompleteProjectiveLift B₀}
variable {R : CompleteProjectiveLift A}
variable {S : CompleteProjectiveLift B}

/-- Exact comparison data between a source chart and an independently
assembled target chart.

The coordinate and global homomorphisms need not be inclusions.  This
generality is useful for quotient charts and avoids asserting that all
abstract coordinate automorphisms are realized in an inertia group. -/
structure ProjectiveLiftChartAgreement
    (source : ProjectiveLiftChart R₀ R)
    (target : ProjectiveLiftChart S₀ S)
    (coordinateEmbedding : B₀ →* A₀)
    (globalEmbedding : B →* A) where
  /-- Inclusion of the realized target chart into the source chart. -/
  chartEmbedding : target.chartGroup →* source.chartGroup
  /-- The coordinate chart square commutes. -/
  coordinateChart_embedding :
    ∀ x : target.chartGroup,
      source.coordinateChart (chartEmbedding x) =
        coordinateEmbedding (target.coordinateChart x)
  /-- The global chart square commutes. -/
  globalChart_embedding :
    ∀ x : target.chartGroup,
      source.globalChart (chartEmbedding x) =
        globalEmbedding (target.globalChart x)
  /-- The coordinate factor sets agree under the coordinate embedding. -/
  coordinateFactor_agreement :
    ∀ x y : target.chartGroup,
      R₀.projective.factor
          (coordinateEmbedding (target.coordinateChart x))
          (coordinateEmbedding (target.coordinateChart y)) =
        S₀.projective.factor
          (target.coordinateChart x) (target.coordinateChart y)
  /-- The complementary factor sets agree under chart inclusion. -/
  complementFactor_agreement :
    ∀ x y : target.chartGroup,
      source.complementProjective.factor
          (chartEmbedding x) (chartEmbedding y) =
        target.complementProjective.factor x y

namespace ProjectiveLiftChart

/-- If both tensor factors act by scalars on a chart element, then the
assembled global operator acts by their product. -/
theorem globalOperator_isScalar
    (chart : ProjectiveLiftChart R₀ R)
    (x : chart.chartGroup)
    (c d : ℂˣ)
    (hcoordinate :
      R₀.projective.operator (chart.coordinateChart x) =
        scalarLinearEquiv ℂ R₀.space c)
    (hcomplement :
      chart.complementProjective.operator x =
        scalarLinearEquiv ℂ chart.complementSpace d) :
    R.projective.operator (chart.globalChart x) =
      scalarLinearEquiv ℂ R.space (c * d) := by
  ext z
  obtain ⟨w, rfl⟩ := chart.realization.surjective z
  rw [← chart.operator_intertwining]
  change
    chart.realization
        (TensorProduct.congr
          (R₀.projective.operator (chart.coordinateChart x))
          (chart.complementProjective.operator x) w) =
      (c * d : ℂˣ) • chart.realization w
  rw [hcoordinate, hcomplement,
    TensorProduct.congr_scalarLinearEquiv]
  exact chart.realization.map_smul (c * d : ℂ) w

end ProjectiveLiftChart

namespace ProjectiveLiftChartAgreement

variable
  {source : ProjectiveLiftChart R₀ R}
  {target : ProjectiveLiftChart S₀ S}
  {coordinateEmbedding : B₀ →* A₀}
  {globalEmbedding : B →* A}

/-- Exact global factor agreement on every element represented by one target
chart. -/
theorem globalFactor_agreement
    (C :
      ProjectiveLiftChartAgreement source target
        coordinateEmbedding globalEmbedding)
    (x y : target.chartGroup) :
    R.projective.factor
        (globalEmbedding (target.globalChart x))
        (globalEmbedding (target.globalChart y)) =
      S.projective.factor
        (target.globalChart x) (target.globalChart y) := by
  rw [← C.globalChart_embedding, ← C.globalChart_embedding,
    ← source.factor_compatibility, C.coordinateChart_embedding,
    C.coordinateChart_embedding, C.coordinateFactor_agreement,
    C.complementFactor_agreement, target.factor_compatibility]

/-- Common scalar actions on the two coordinate lifts and on their
complements yield a common scalar action on the two assembled global lifts. -/
theorem globalScalar_agreement
    (C :
      ProjectiveLiftChartAgreement source target
        coordinateEmbedding globalEmbedding)
    (x : target.chartGroup)
    (c d : ℂˣ)
    (hsourceCoordinate :
      R₀.projective.operator
          (coordinateEmbedding (target.coordinateChart x)) =
        scalarLinearEquiv ℂ R₀.space c)
    (htargetCoordinate :
      S₀.projective.operator (target.coordinateChart x) =
        scalarLinearEquiv ℂ S₀.space c)
    (hsourceComplement :
      source.complementProjective.operator (C.chartEmbedding x) =
        scalarLinearEquiv ℂ source.complementSpace d)
    (htargetComplement :
      target.complementProjective.operator x =
        scalarLinearEquiv ℂ target.complementSpace d) :
    ∃ z : ℂˣ,
      R.projective.operator
          (globalEmbedding (target.globalChart x)) =
          scalarLinearEquiv ℂ R.space z ∧
        S.projective.operator (target.globalChart x) =
          scalarLinearEquiv ℂ S.space z := by
  refine ⟨c * d, ?_, ?_⟩
  · rw [← C.globalChart_embedding]
    exact
      source.globalOperator_isScalar
        (C.chartEmbedding x) c d
        (by simpa only [C.coordinateChart_embedding] using hsourceCoordinate)
        hsourceComplement
  · exact
      target.globalOperator_isScalar
        x c d htargetCoordinate htargetComplement

/-- The local tensor condition needed for common scalar action.  The scalar
on the coordinate factor and the scalar on the complementary factor are each
allowed to vary with the chart element. -/
def HasCommonTensorScalarAction
    (C :
      ProjectiveLiftChartAgreement source target
        coordinateEmbedding globalEmbedding)
    (x : target.chartGroup) : Prop :=
  ∃ c d : ℂˣ,
    R₀.projective.operator
          (coordinateEmbedding (target.coordinateChart x)) =
        scalarLinearEquiv ℂ R₀.space c ∧
      S₀.projective.operator (target.coordinateChart x) =
        scalarLinearEquiv ℂ S₀.space c ∧
      source.complementProjective.operator (C.chartEmbedding x) =
        scalarLinearEquiv ℂ source.complementSpace d ∧
      target.complementProjective.operator x =
        scalarLinearEquiv ℂ target.complementSpace d

/-- The predicate-form local tensor condition implies the exact common
global scalar conclusion. -/
theorem globalScalar_agreement_of_hasCommonTensorScalarAction
    (C :
      ProjectiveLiftChartAgreement source target
        coordinateEmbedding globalEmbedding)
    (x : target.chartGroup)
    (h : C.HasCommonTensorScalarAction x) :
    ∃ z : ℂˣ,
      R.projective.operator
          (globalEmbedding (target.globalChart x)) =
          scalarLinearEquiv ℂ R.space z ∧
        S.projective.operator (target.globalChart x) =
          scalarLinearEquiv ℂ S.space z := by
  obtain ⟨c, d, hsourceCoordinate, htargetCoordinate,
    hsourceComplement, htargetComplement⟩ := h
  exact
    C.globalScalar_agreement x c d
      hsourceCoordinate htargetCoordinate
      hsourceComplement htargetComplement

end ProjectiveLiftChartAgreement

/-! ### Independent source and target layer assemblies -/

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

namespace ComponentOrbitLocalData

/-- The two coordinate factor sets extracted from one complete local
central-isomorphism witness agree along the canonical semidirect-product
embedding. -/
theorem coordinateProjective_factor_agreement
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G)
    (b c : d.coordinateIntermediateGroup θ K) :
    (d.coordinateAmbientLift θ K).projective.factor
          (d.coordinateEmbedding θ K b)
          (d.coordinateEmbedding θ K c) =
      (d.coordinateIntermediateLift θ K).projective.factor b c := by
  let C :=
    d.toLayerComponentLocalData.coordinateCompleteTripleWitness θ K
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  change
    C.witness.leftProjective.factor
          ((d.data K).toEquivariant.semidirectEmbedding
            (coordinateLayerCharacter θ K) b)
          ((d.data K).toEquivariant.semidirectEmbedding
            (coordinateLayerCharacter θ K) c) =
      C.witness.rightProjective.factor b c
  have h := C.witness.factor_agreement b c
  convert h using 1 <;>
    rw [C.embedding_eq] <;>
    simp only [toLayerComponentLocalData_data, coordinateLayerCharacter] <;>
    rfl

/-- The two coordinate projective lifts have the same scalar on every target
element whose canonical image centralizes the ambient normal subgroup.  This
is exactly the scalar field of the complete local central witness. -/
theorem coordinateProjective_scalar_agreement
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G)
    (b : d.coordinateIntermediateGroup θ K)
    (hb :
      d.coordinateEmbedding θ K b ∈
        Subgroup.centralizer
          ((coordinateAmbientTriple (D := D) θ K).normalSubgroup :
            Set (coordinateAmbientGroup (D := D) θ K))) :
    ∃ c : ℂˣ,
      (d.coordinateAmbientLift θ K).projective.operator
            (d.coordinateEmbedding θ K b) =
          scalarLinearEquiv ℂ
            (d.coordinateAmbientLift θ K).space c ∧
        (d.coordinateIntermediateLift θ K).projective.operator b =
          scalarLinearEquiv ℂ
            (d.coordinateIntermediateLift θ K).space c := by
  let C :=
    d.toLayerComponentLocalData.coordinateCompleteTripleWitness θ K
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  have hb' :
      C.witness.embedding b ∈
        Subgroup.centralizer
          ((coordinateAmbientTriple (D := D) θ K).normalSubgroup :
            Set (coordinateAmbientGroup (D := D) θ K)) := by
    rw [C.embedding_eq]
    convert hb using 1 <;>
      simp only [toLayerComponentLocalData_data, coordinateLayerCharacter,
        coordinateEmbedding] <;>
      rfl
  have h := C.witness.scalar_agreement b hb'
  change
    ∃ c : ℂˣ,
      C.witness.leftProjective.operator
            ((d.data K).toEquivariant.semidirectEmbedding
              (coordinateLayerCharacter θ K) b) =
          scalarLinearEquiv ℂ C.leftSpace c ∧
        C.witness.rightProjective.operator b =
          scalarLinearEquiv ℂ C.rightSpace c
  obtain ⟨c, hleft, hright⟩ := h
  refine ⟨c, ?_, hright⟩
  convert hleft using 1 <;>
    rw [C.embedding_eq] <;>
    simp only [toLayerComponentLocalData_data, coordinateLayerCharacter] <;>
    rfl

end ComponentOrbitLocalData

namespace LayerProjectiveRestrictionAssembly

/-- Ambient group of the source layer inertia triple. -/
abbrev sourceInertiaGroup
    (θ : PPrimeIrreducibleCharacter (layer G) p) :=
  IrreducibleCharacter.inertia (layer G) θ.1

/-- Ambient group of the matched target layer inertia triple. -/
abbrev targetInertiaGroup
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :=
  IrreducibleCharacter.inertia
    d.intermediateComponentLocal
    (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1

/-- The canonical normalized associated lift on the target layer inertia
triple.  It is independent of the source lift and may have a different
dimension. -/
def canonicalTargetLift
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    CompleteAssociatedProjectiveLift (targetTriple d θ) :=
  CompleteAssociatedProjectiveLift.canonical (targetTriple d θ)

/-- Operator-and-factor data assembling the intermediate halves of all
coordinate witnesses into an independently associated target lift. -/
structure TargetCoordinatePermutationProjectiveAssembly
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- Independently assembled associated lift on the target inertia group. -/
  targetLift :
    CompleteAssociatedProjectiveLift (targetTriple d θ)
  /-- Realization of every intermediate coordinate lift inside the target
  lift. -/
  intermediateChart :
    ∀ K : ComponentIndex G,
      ProjectiveLiftChart
        (d.coordinateIntermediateLift θ K).forget
        targetLift.forget
  /-- Compatibility under component permutations induced by the target
  inertia group. -/
  intermediatePermutationCoherence :
    ∀ (a :
        IrreducibleCharacter.inertia
          d.intermediateComponentLocal
          (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1)
      (K : ComponentIndex G),
      ProjectiveLiftChart.PermutationCoherence
        (intermediateChart K)
        (intermediateChart
          ((((a : d.ambientIntermediate) : G)) • K))
        a

/-- The source and independently associated target chart families. -/
structure IndependentTargetProjectiveChartFamilies
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- Assembled associated source lift. -/
  source :
    CoordinatePermutationProjectiveAssembly d θ
  /-- Independently assembled associated target lift. -/
  target :
    TargetCoordinatePermutationProjectiveAssembly d θ

/-- The embedding squares relating the two independent chart families. -/
structure IndependentTargetProjectiveChartEmbedding
    {d : ComponentOrbitLocalData D}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (C : IndependentTargetProjectiveChartFamilies d θ) where
  /-- Inclusion of each realized target chart into its source chart. -/
  chartEmbedding :
    ∀ K : ComponentIndex G,
      (C.target.intermediateChart K).chartGroup →*
        (C.source.ambientChart K).chartGroup
  /-- The coordinate chart squares commute. -/
  coordinateChart_embedding :
    ∀ (K : ComponentIndex G)
      (x : (C.target.intermediateChart K).chartGroup),
      (C.source.ambientChart K).coordinateChart
          (chartEmbedding K x) =
        d.coordinateEmbedding θ K
          ((C.target.intermediateChart K).coordinateChart x)
  /-- The global chart squares commute. -/
  globalChart_embedding :
    ∀ (K : ComponentIndex G)
      (x : (C.target.intermediateChart K).chartGroup),
      (C.source.ambientChart K).globalChart
          (chartEmbedding K x) =
        inertiaEmbedding d hcoordinate θ
          ((C.target.intermediateChart K).globalChart x)

/-- Complementary factor-set agreement for embedded independent charts. -/
structure IndependentTargetComplementFactorAgreement
    {d : ComponentOrbitLocalData D}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    (C : IndependentTargetProjectiveChartFamilies d θ)
    (E : IndependentTargetProjectiveChartEmbedding hcoordinate C) where
  /-- The complementary tensor factor sets agree.  The coordinate factor
  agreement is already a theorem of the canonical local witness. -/
  factor_agreement :
    ∀ (K : ComponentIndex G)
      (x y : (C.target.intermediateChart K).chartGroup),
      (C.source.ambientChart K).complementProjective.factor
          (E.chartEmbedding K x) (E.chartEmbedding K y) =
        (C.target.intermediateChart K).complementProjective.factor x y

/-- Source and independent-target assemblies, together with exact comparison
data on every coordinate chart.  The bundle is split into small dependent
records so that elaboration remains within the project heartbeat budget. -/
structure IndependentTargetProjectiveCharts
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- The two chart families. -/
  families :
    IndependentTargetProjectiveChartFamilies d θ
  /-- Their embedding squares. -/
  embedding :
    IndependentTargetProjectiveChartEmbedding hcoordinate families
  /-- Complementary factor-set agreement. -/
  complement :
    IndependentTargetComplementFactorAgreement families embedding

namespace IndependentTargetProjectiveCharts

variable
  {d : ComponentOrbitLocalData D}
  {hcoordinate :
    d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
      d.isConjugationEquivariantUnder}
  {θ : PPrimeIrreducibleCharacter (layer G) p}

/-- The source chart assembly stored in the split bundle. -/
abbrev source
    (C : IndependentTargetProjectiveCharts d hcoordinate θ) :=
  C.families.source

/-- The target chart assembly stored in the split bundle. -/
abbrev target
    (C : IndependentTargetProjectiveCharts d hcoordinate θ) :=
  C.families.target

/-- Exact comparison of one source/target chart pair.  Its coordinate
factor-set field is discharged by the canonical component local witness, so
only complementary factor agreement remains in the assembly input. -/
def agreement
    (C : IndependentTargetProjectiveCharts d hcoordinate θ)
    (K : ComponentIndex G) :
    ProjectiveLiftChartAgreement
      (C.source.ambientChart K)
      (C.target.intermediateChart K)
      (d.coordinateEmbedding θ K)
      (inertiaEmbedding d hcoordinate θ) where
  chartEmbedding := C.embedding.chartEmbedding K
  coordinateChart_embedding :=
    C.embedding.coordinateChart_embedding K
  globalChart_embedding :=
    C.embedding.globalChart_embedding K
  coordinateFactor_agreement := by
    intro x y
    exact
      d.coordinateProjective_factor_agreement θ K
        ((C.target.intermediateChart K).coordinateChart x)
        ((C.target.intermediateChart K).coordinateChart y)
  complementFactor_agreement :=
    C.complement.factor_agreement K

/-- The remaining scalar input on one chart element after using the complete
local central witness: the coordinate image must lie in the coordinate
centralizer, and the two complementary tensor factors must act by a common
scalar. -/
def HasCanonicalCommonTensorScalarAction
    (C : IndependentTargetProjectiveCharts d hcoordinate θ)
    (K : ComponentIndex G)
    (x : (C.target.intermediateChart K).chartGroup) : Prop :=
  d.coordinateEmbedding θ K
        ((C.target.intermediateChart K).coordinateChart x) ∈
      Subgroup.centralizer
        ((ComponentOrbitLocalData.coordinateAmbientTriple
            (D := D) θ K).normalSubgroup :
          Set (ComponentOrbitLocalData.coordinateAmbientGroup
            (D := D) θ K)) ∧
    ∃ z : ℂˣ,
      (C.source.ambientChart K).complementProjective.operator
            (C.embedding.chartEmbedding K x) =
          scalarLinearEquiv ℂ
            (C.source.ambientChart K).complementSpace z ∧
        (C.target.intermediateChart K).complementProjective.operator x =
          scalarLinearEquiv ℂ
            (C.target.intermediateChart K).complementSpace z

/-- The canonical local central witness supplies the common coordinate
scalar, so the reduced scalar input above gives the full tensor condition. -/
theorem hasCommonTensorScalarAction
    (C : IndependentTargetProjectiveCharts d hcoordinate θ)
    (K : ComponentIndex G)
    (x : (C.target.intermediateChart K).chartGroup)
    (h : C.HasCanonicalCommonTensorScalarAction K x) :
    (C.agreement K).HasCommonTensorScalarAction x := by
  obtain ⟨hcentral, z, hsourceComplement,
    htargetComplement⟩ := h
  obtain ⟨c, hsourceCoordinate, htargetCoordinate⟩ :=
    d.coordinateProjective_scalar_agreement θ K
      ((C.target.intermediateChart K).coordinateChart x)
      hcentral
  exact
    ⟨c, z, hsourceCoordinate, htargetCoordinate,
      hsourceComplement, htargetComplement⟩

end IndependentTargetProjectiveCharts

end LayerProjectiveRestrictionAssembly

end InductiveMcKay
end McKayConjecture
