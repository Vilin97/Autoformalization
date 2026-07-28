/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerTargetProjectiveAssembly

/-!
# Central witnesses from an independent target projective assembly

This file gives a sufficient local-to-global endpoint for
`LayerTargetProjectiveAssembly`.  Pair coverage of the target inertia group
turns chartwise factor agreement into full factor agreement.  Centralizer
coverage, with common scalar action on coordinate and complementary tensor
factors, turns the chartwise tensor calculation into the scalar agreement
required by a central-isomorphism witness.

The pair-coverage hypothesis is deliberately not claimed to follow from the
component construction.  It can fail when inertia elements permute every
component: for three isomorphic components cyclically permuted by an element
fixing a tensor product character, that element belongs to no chart based at
a stabilized component.  The general layer construction must instead use
the tensor-permutation cocycles in
`LayerTensorPermutationCentralWitnessAssembly`.

The source and target associated projective representations remain
independent throughout; in particular, no equality of their dimensions is
assumed.
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

namespace LayerProjectiveRestrictionAssembly

/-- A sound sufficient local-to-global assembly criterion for the two
independent associated lifts.

`factorChartCoverage` is the exact coverage statement needed to compare every
pair of target inertia elements.  `centralizerChartCoverage` asks only for the
local tensor scalar data at embedded centralizer elements.  The two global
conclusions required by a central-isomorphism witness are theorems below, not
fields of this structure.  No claim is made that `factorChartCoverage` holds
for a genuine component-permutation action. -/
structure IndependentTargetCentralWitnessAssembly
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- The two independently associated lifts and their coordinate-chart
  comparisons. -/
  charts :
    IndependentTargetProjectiveCharts d hcoordinate θ
  /-- Every pair of elements of the target inertia group is simultaneously
  represented in a target coordinate chart. -/
  factorChartCoverage :
    ∀ b c : targetInertiaGroup d θ,
      ∃ (K : ComponentIndex G)
        (x y : (charts.target.intermediateChart K).chartGroup),
        (charts.target.intermediateChart K).globalChart x = b ∧
          (charts.target.intermediateChart K).globalChart y = c
  /-- Every embedded target element in the source centralizer is represented
  by a chart whose coordinate image lies in the coordinate centralizer and
  whose two complementary factors have a common scalar action.  The common
  coordinate scalar is a theorem of the canonical local witness. -/
  centralizerChartCoverage :
    ∀ (h : targetInertiaGroup d θ),
      inertiaEmbedding d hcoordinate θ h ∈
          Subgroup.centralizer
            ((sourceTriple θ).normalSubgroup :
              Set (sourceInertiaGroup θ)) →
        ∃ (K : ComponentIndex G)
          (x : (charts.target.intermediateChart K).chartGroup),
          (charts.target.intermediateChart K).globalChart x = h ∧
            charts.HasCanonicalCommonTensorScalarAction K x

namespace IndependentTargetCentralWitnessAssembly

variable
  {d : ComponentOrbitLocalData D}
  {hcoordinate :
    d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
      d.isConjugationEquivariantUnder}
  {θ : PPrimeIrreducibleCharacter (layer G) p}

/-- The associated source lift selected by the assembly. -/
abbrev sourceLift
    (C :
      IndependentTargetCentralWitnessAssembly d hcoordinate θ) :
    CompleteAssociatedProjectiveLift (sourceTriple θ) :=
  C.charts.source.sourceLift

/-- The independently associated target lift selected by the assembly. -/
abbrev targetLift
    (C :
      IndependentTargetCentralWitnessAssembly d hcoordinate θ) :
    CompleteAssociatedProjectiveLift (targetTriple d θ) :=
  C.charts.target.targetLift

/-- Exact factor agreement on the full target inertia group, derived from
chartwise tensor factor agreement and pair coverage. -/
theorem factor_agreement
    (C :
      IndependentTargetCentralWitnessAssembly d hcoordinate θ)
    (b c : targetInertiaGroup d θ) :
    C.sourceLift.projective.factor
          (inertiaEmbedding d hcoordinate θ b)
          (inertiaEmbedding d hcoordinate θ c) =
      C.targetLift.projective.factor b c := by
  obtain ⟨K, x, y, hx, hy⟩ :=
    C.factorChartCoverage b c
  have h :=
    (C.charts.agreement K).globalFactor_agreement x y
  change
    C.charts.source.sourceLift.forget.projective.factor
          (inertiaEmbedding d hcoordinate θ b)
          (inertiaEmbedding d hcoordinate θ c) =
      C.charts.target.targetLift.forget.projective.factor b c
  simpa only [hx, hy] using h

/-- Exact common scalar action on the full embedded centralizer, derived
from common scalar action on the two tensor factors of a covering chart. -/
theorem scalar_agreement
    (C :
      IndependentTargetCentralWitnessAssembly d hcoordinate θ)
    (h : targetInertiaGroup d θ)
    (hh :
      inertiaEmbedding d hcoordinate θ h ∈
        Subgroup.centralizer
          ((sourceTriple θ).normalSubgroup :
            Set (sourceInertiaGroup θ))) :
    ∃ z : ℂˣ,
      C.sourceLift.projective.operator
          (inertiaEmbedding d hcoordinate θ h) =
          scalarLinearEquiv ℂ C.sourceLift.space z ∧
        C.targetLift.projective.operator h =
          scalarLinearEquiv ℂ C.targetLift.space z := by
  obtain ⟨K, x, hx, hscalar⟩ :=
    C.centralizerChartCoverage h hh
  have hscalar' :=
    C.charts.hasCommonTensorScalarAction K x hscalar
  have hz :=
    ProjectiveLiftChartAgreement.globalScalar_agreement_of_hasCommonTensorScalarAction
      (C.charts.agreement K) x hscalar'
  change
    ∃ z : ℂˣ,
      C.charts.source.sourceLift.forget.projective.operator
          (inertiaEmbedding d hcoordinate θ h) =
          scalarLinearEquiv ℂ
            C.charts.source.sourceLift.forget.space z ∧
        C.charts.target.targetLift.forget.projective.operator h =
          scalarLinearEquiv ℂ
            C.charts.target.targetLift.forget.space z
  simpa only [hx] using hz

/-- Combine the independently associated lifts, the local-to-global chart
proofs, and the ordinary group conditions into a complete
central-isomorphism witness. -/
def toCompleteCentralIsomorphismWitness
    (C :
      IndependentTargetCentralWitnessAssembly d hcoordinate θ)
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ)) :
    CompleteCentralIsomorphismWitness
      (sourceTriple θ) (targetTriple d θ) := by
  letI := C.sourceLift.addCommGroup
  letI := C.sourceLift.module
  letI := C.sourceLift.moduleFinite
  letI := C.sourceLift.nontrivial
  letI := C.targetLift.addCommGroup
  letI := C.targetLift.module
  letI := C.targetLift.moduleFinite
  letI := C.targetLift.nontrivial
  exact
    { leftSpace := C.sourceLift.space
      rightSpace := C.targetLift.space
      witness :=
        { leftProjective := C.sourceLift.projective
          leftAssociated := C.sourceLift.associated
          rightProjective := C.targetLift.projective
          rightAssociated := C.targetLift.associated
          embedding := inertiaEmbedding d hcoordinate θ
          embedding_injective := g.embedding_injective
          centralizer_le := g.centralizer_le
          ambient_eq_product := g.ambient_eq_product
          intersection_eq := g.intersection_eq
          factor_agreement := C.factor_agreement
          scalar_agreement := C.scalar_agreement } }

section CanonicalIntersection

variable {P : Sylow p G}
variable
  {D :
    LayerSylowCoordinateData G p
      (layerSylowIntersection P)}

/-- In a minimal counterexample the required ordinary group data is
canonical, so an independent target assembly directly produces the desired
complete central witness. -/
def toCompleteCentralIsomorphismWitness_of_minimalCounterexample
    {d : ComponentOrbitLocalData D}
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    (C :
      IndependentTargetCentralWitnessAssembly d hcoordinate θ)
    (hminimal : MinimalCounterexampleStructure P) :
    CompleteCentralIsomorphismWitness
      (sourceTriple θ) (targetTriple d θ) :=
  C.toCompleteCentralIsomorphismWitness
    (d.layerIntermediateInertiaRestrictionGroupData_of_minimalCounterexample
      hcoordinate hminimal θ)

end CanonicalIntersection

end IndependentTargetCentralWitnessAssembly
end LayerProjectiveRestrictionAssembly

end InductiveMcKay
end McKayConjecture
