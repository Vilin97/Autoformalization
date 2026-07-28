/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedUniqueness
import McKayConjecture.CharacterTriple.FiniteProjectiveTensorComparison
import McKayConjecture.CharacterTriple.FiniteTensorPermutationComparison
import McKayConjecture.InductiveMcKay.LayerTargetCentralWitnessAssembly

/-!
# Central witnesses from tensor-permutation cocycles

The coordinate-chart coverage criterion in
`LayerTargetCentralWitnessAssembly` is useful only when every relevant pair
of inertia elements stabilizes one common component.  That need not happen:
an inertia element may permute every component of an orbit.

This file gives the sound replacement.  On each component orbit it uses an
actual tensor-permutation cocycle.  The orbitwise actions are then tensored
together.  Exact global factor agreement and centralizer scalar agreement
are derived from coordinatewise data; neither is a field of the assembly.

The remaining layer-specific construction problem is consequently explicit:
build the orbitwise transport cocycles and prove that their tensor actions
realize associated lifts of the two layer inertia triples.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

namespace LayerProjectiveRestrictionAssembly

/-- Orbitwise tensor-permutation data comparing the source restriction with
the target lift.  All cocycles are actions of the target inertia group.  The
source cocycles therefore describe the source action after pullback along
the canonical inertia embedding. -/
structure LayerTensorPermutationCocycleFamily
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- Finite set of component orbits. -/
  orbit : Type
  [orbitFintype : Fintype orbit]
  /-- Finite coordinate set in each orbit. -/
  coordinate : orbit → Type
  [coordinateFintype : ∀ o, Fintype (coordinate o)]
  /-- The target inertia action on each coordinate orbit. -/
  [coordinateAction :
    ∀ o, MulAction (targetInertiaGroup d θ) (coordinate o)]
  /-- One source representation space, transported around each orbit. -/
  sourceCoordinateSpace : orbit → Type
  [sourceCoordinateAddCommGroup :
    ∀ o, AddCommGroup (sourceCoordinateSpace o)]
  [sourceCoordinateModule :
    ∀ o, Module ℂ (sourceCoordinateSpace o)]
  [sourceCoordinateModuleFinite :
    ∀ o, Module.Finite ℂ (sourceCoordinateSpace o)]
  [sourceCoordinateNontrivial :
    ∀ o, Nontrivial (sourceCoordinateSpace o)]
  /-- One target representation space, transported around each orbit. -/
  targetCoordinateSpace : orbit → Type
  [targetCoordinateAddCommGroup :
    ∀ o, AddCommGroup (targetCoordinateSpace o)]
  [targetCoordinateModule :
    ∀ o, Module ℂ (targetCoordinateSpace o)]
  [targetCoordinateModuleFinite :
    ∀ o, Module.Finite ℂ (targetCoordinateSpace o)]
  [targetCoordinateNontrivial :
    ∀ o, Nontrivial (targetCoordinateSpace o)]
  /-- Source coordinate transports on every component orbit. -/
  sourceCocycle :
    ∀ o,
      FiniteTensorPermutationCocycle
        (K := ℂ) (A := targetInertiaGroup d θ)
        (ι := coordinate o) (sourceCoordinateSpace o)
  /-- Target coordinate transports on every component orbit. -/
  targetCocycle :
    ∀ o,
      FiniteTensorPermutationCocycle
        (K := ℂ) (A := targetInertiaGroup d θ)
        (ι := coordinate o) (targetCoordinateSpace o)
  /-- The local component witnesses give the same transport factor in every
  coordinate. -/
  cocycleAgreement :
    ∀ o,
      FiniteTensorPermutationCocycleAgreement
        (sourceCocycle o) (targetCocycle o)
  /-- At an embedded element centralizing the layer, the local component
  witnesses give common coordinate scalars.  Fixing the coordinates is part
  of `FiniteTensorPermutationCommonScalar`, so this cannot be used for a
  genuinely permuting inertia element. -/
  centralCoordinateScalar :
    ∀ (h : targetInertiaGroup d θ),
      inertiaEmbedding d hcoordinate θ h ∈
          Subgroup.centralizer
            ((sourceTriple θ).normalSubgroup :
              Set (sourceInertiaGroup θ)) →
        ∀ o,
          FiniteTensorPermutationCommonScalar
            (sourceCocycle o) (targetCocycle o) h

attribute [instance]
  LayerTensorPermutationCocycleFamily.orbitFintype
  LayerTensorPermutationCocycleFamily.coordinateFintype
  LayerTensorPermutationCocycleFamily.coordinateAction
  LayerTensorPermutationCocycleFamily.sourceCoordinateAddCommGroup
  LayerTensorPermutationCocycleFamily.sourceCoordinateModule
  LayerTensorPermutationCocycleFamily.sourceCoordinateModuleFinite
  LayerTensorPermutationCocycleFamily.sourceCoordinateNontrivial
  LayerTensorPermutationCocycleFamily.targetCoordinateAddCommGroup
  LayerTensorPermutationCocycleFamily.targetCoordinateModule
  LayerTensorPermutationCocycleFamily.targetCoordinateModuleFinite
  LayerTensorPermutationCocycleFamily.targetCoordinateNontrivial

namespace LayerTensorPermutationCocycleFamily

variable
  {d : ComponentOrbitLocalData D}
  {hcoordinate :
    d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
      d.isConjugationEquivariantUnder}
  {θ : PPrimeIrreducibleCharacter (layer G) p}

/-- Source tensor space on one component orbit. -/
abbrev sourceOrbitSpace
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ)
    (o : F.orbit) :=
  ⨂[ℂ] _i : F.coordinate o, F.sourceCoordinateSpace o

/-- Target tensor space on one component orbit. -/
abbrev targetOrbitSpace
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ)
    (o : F.orbit) :=
  ⨂[ℂ] _i : F.coordinate o, F.targetCoordinateSpace o

/-- Full source tensor space, with one tensor factor for each component
orbit. -/
abbrev sourceTensorSpace
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ) :=
  ⨂[ℂ] o : F.orbit, F.sourceOrbitSpace o

/-- Full target tensor space, with one tensor factor for each component
orbit. -/
abbrev targetTensorSpace
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ) :=
  ⨂[ℂ] o : F.orbit, F.targetOrbitSpace o

/-- Source tensor-permutation representation after restriction to the target
inertia group. -/
def sourceProjective
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ) :
    ProjectiveRepresentation ℂ
      (targetInertiaGroup d θ) F.sourceTensorSpace :=
  ProjectiveRepresentation.piTensor
    (fun o ↦ (F.sourceCocycle o).projectiveRepresentation)

/-- Target tensor-permutation representation. -/
def targetProjective
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ) :
    ProjectiveRepresentation ℂ
      (targetInertiaGroup d θ) F.targetTensorSpace :=
  ProjectiveRepresentation.piTensor
    (fun o ↦ (F.targetCocycle o).projectiveRepresentation)

/-- The orbitwise cocycle agreements form an agreement of the outer finite
projective tensor families. -/
theorem projectiveAgreement
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ) :
    ProjectiveRepresentation.PiTensorAgreement
      (fun o ↦ (F.sourceCocycle o).projectiveRepresentation)
      (fun o ↦ (F.targetCocycle o).projectiveRepresentation) where
  factor_eq o a b :=
    (F.cocycleAgreement o).projective_factor_eq a b

/-- Exact factor agreement on the two full tensor-permutation
representations, derived from the coordinate witness factors. -/
theorem factor_agreement
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ)
    (a b : targetInertiaGroup d θ) :
    F.sourceProjective.factor a b =
      F.targetProjective.factor a b :=
  F.projectiveAgreement.piTensor_factor_eq a b

/-- A finite-dimensionality witness for each source orbit tensor. -/
theorem sourceOrbitModuleFinite
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ)
    (o : F.orbit) :
    Module.Finite ℂ (F.sourceOrbitSpace o) :=
  ProjectiveRepresentation.piTensorModuleFinite

/-- A nontriviality witness for each source orbit tensor. -/
theorem sourceOrbitNontrivial
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ)
    (o : F.orbit) :
    Nontrivial (F.sourceOrbitSpace o) :=
  ProjectiveRepresentation.piTensorNontrivial

/-- A finite-dimensionality witness for each target orbit tensor. -/
theorem targetOrbitModuleFinite
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ)
    (o : F.orbit) :
    Module.Finite ℂ (F.targetOrbitSpace o) :=
  ProjectiveRepresentation.piTensorModuleFinite

/-- A nontriviality witness for each target orbit tensor. -/
theorem targetOrbitNontrivial
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ)
    (o : F.orbit) :
    Nontrivial (F.targetOrbitSpace o) :=
  ProjectiveRepresentation.piTensorNontrivial

/-- A finite-dimensionality witness for the full source tensor. -/
theorem sourceTensorModuleFinite
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ) :
    Module.Finite ℂ F.sourceTensorSpace := by
  letI : ∀ o, Module.Finite ℂ (F.sourceOrbitSpace o) :=
    fun o ↦ F.sourceOrbitModuleFinite o
  exact ProjectiveRepresentation.piTensorModuleFinite

/-- A nontriviality witness for the full source tensor. -/
theorem sourceTensorNontrivial
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ) :
    Nontrivial F.sourceTensorSpace := by
  letI : ∀ o, Nontrivial (F.sourceOrbitSpace o) :=
    fun o ↦ F.sourceOrbitNontrivial o
  exact ProjectiveRepresentation.piTensorNontrivial

/-- A finite-dimensionality witness for the full target tensor. -/
theorem targetTensorModuleFinite
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ) :
    Module.Finite ℂ F.targetTensorSpace := by
  letI : ∀ o, Module.Finite ℂ (F.targetOrbitSpace o) :=
    fun o ↦ F.targetOrbitModuleFinite o
  exact ProjectiveRepresentation.piTensorModuleFinite

/-- A nontriviality witness for the full target tensor. -/
theorem targetTensorNontrivial
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ) :
    Nontrivial F.targetTensorSpace := by
  letI : ∀ o, Nontrivial (F.targetOrbitSpace o) :=
    fun o ↦ F.targetOrbitNontrivial o
  exact ProjectiveRepresentation.piTensorNontrivial

/-- Common coordinate scalars on all component orbits give one common scalar
on the two full tensor-permutation representations. -/
theorem scalar_agreement
    (F : LayerTensorPermutationCocycleFamily d hcoordinate θ)
    (h : targetInertiaGroup d θ)
    (hh :
      inertiaEmbedding d hcoordinate θ h ∈
        Subgroup.centralizer
          ((sourceTriple θ).normalSubgroup :
            Set (sourceInertiaGroup θ))) :
    ∃ z : ℂˣ,
      F.sourceProjective.operator h =
          scalarLinearEquiv ℂ F.sourceTensorSpace z ∧
        F.targetProjective.operator h =
          scalarLinearEquiv ℂ F.targetTensorSpace z := by
  let orbitScalar : F.orbit → ℂˣ :=
    fun o ↦
      Classical.choose
        ((F.centralCoordinateScalar h hh o).operator_agreement)
  have horbit :
      ∀ o,
        (F.sourceCocycle o).projectiveRepresentation.operator h =
            scalarLinearEquiv ℂ (F.sourceOrbitSpace o)
              (orbitScalar o) ∧
          (F.targetCocycle o).projectiveRepresentation.operator h =
            scalarLinearEquiv ℂ (F.targetOrbitSpace o)
              (orbitScalar o) := by
    intro o
    exact
      Classical.choose_spec
        ((F.centralCoordinateScalar h hh o).operator_agreement)
  let common :
      ProjectiveRepresentation.PiTensorCommonScalar
        (fun o ↦ (F.sourceCocycle o).projectiveRepresentation)
        (fun o ↦ (F.targetCocycle o).projectiveRepresentation) h :=
    { scalar := orbitScalar
      left := fun o ↦ (horbit o).1
      right := fun o ↦ (horbit o).2 }
  exact common.operator_agreement

end LayerTensorPermutationCocycleFamily

/-- Associated source and target lifts realized by a pair of orbitwise
tensor-permutation constructions after one common scalar gauge.  The common
gauge allows harmless normalization of the chosen tensor lifts while
preserving exact source/target factor and scalar agreement.  The operator
intertwining fields are constructive realization data; the required factor
and scalar agreements are proved below. -/
structure LayerTensorPermutationCentralWitnessAssembly
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- Coordinate transport cocycles and their local comparisons. -/
  family :
    LayerTensorPermutationCocycleFamily d hcoordinate θ
  /-- One common rescaling of the two assembled projective
  representations. -/
  gauge : targetInertiaGroup d θ → ℂˣ
  /-- Associated source lift on the full source inertia group. -/
  sourceLift :
    CompleteAssociatedProjectiveLift (sourceTriple θ)
  /-- Associated target lift. -/
  targetLift :
    CompleteAssociatedProjectiveLift (targetTriple d θ)
  /-- Realization of the restricted source lift by its tensor-permutation
  space. -/
  sourceRealization :
    family.sourceTensorSpace ≃ₗ[ℂ] sourceLift.space
  /-- Realization of the target lift by its tensor-permutation space. -/
  targetRealization :
    family.targetTensorSpace ≃ₗ[ℂ] targetLift.space
  /-- The source tensor-permutation action is the pullback of the source
  associated lift. -/
  sourceOperator_intertwining :
    ∀ (a : targetInertiaGroup d θ)
      (v : family.sourceTensorSpace),
      sourceRealization
          ((family.sourceProjective.rescale gauge).operator a v) =
        sourceLift.projective.operator
          (inertiaEmbedding d hcoordinate θ a)
          (sourceRealization v)
  /-- The target tensor-permutation action realizes the target associated
  lift. -/
  targetOperator_intertwining :
    ∀ (a : targetInertiaGroup d θ)
      (v : family.targetTensorSpace),
      targetRealization
          ((family.targetProjective.rescale gauge).operator a v) =
        targetLift.projective.operator a
          (targetRealization v)

namespace LayerTensorPermutationCentralWitnessAssembly

variable
  {d : ComponentOrbitLocalData D}
  {hcoordinate :
    d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
      d.isConjugationEquivariantUnder}
  {θ : PPrimeIrreducibleCharacter (layer G) p}

/-- Exact factor agreement for the associated lifts, derived from the two
tensor realizations and coordinatewise cocycle agreement. -/
theorem factor_agreement
    (C : LayerTensorPermutationCentralWitnessAssembly
      d hcoordinate θ)
    (a b : targetInertiaGroup d θ) :
    C.sourceLift.projective.factor
          (inertiaEmbedding d hcoordinate θ a)
          (inertiaEmbedding d hcoordinate θ b) =
      C.targetLift.projective.factor a b := by
  letI : Nontrivial C.family.sourceTensorSpace :=
    C.family.sourceTensorNontrivial
  letI : Nontrivial C.family.targetTensorSpace :=
    C.family.targetTensorNontrivial
  have hsource :
      (C.family.sourceProjective.rescale C.gauge).factor a b =
        C.sourceLift.projective.factor
          (inertiaEmbedding d hcoordinate θ a)
          (inertiaEmbedding d hcoordinate θ b) := by
    exact
      AssociatedProjectiveRepresentation.factor_eq_of_equiv_operator_eq
        (P := C.family.sourceProjective.rescale C.gauge)
        (Q := C.sourceLift.projective.comap
          (inertiaEmbedding d hcoordinate θ))
        C.sourceRealization
        (by
          intro x v
          exact C.sourceOperator_intertwining x v)
        a b
  have htarget :
      (C.family.targetProjective.rescale C.gauge).factor a b =
        C.targetLift.projective.factor a b := by
    exact
      AssociatedProjectiveRepresentation.factor_eq_of_equiv_operator_eq
        (P := C.family.targetProjective.rescale C.gauge)
        (Q := C.targetLift.projective)
        C.targetRealization C.targetOperator_intertwining a b
  have hfamily :
      (C.family.sourceProjective.rescale C.gauge).factor a b =
        (C.family.targetProjective.rescale C.gauge).factor a b := by
    simp only [ProjectiveRepresentation.rescale_factor,
      C.family.factor_agreement a b]
  exact hsource.symm.trans
    (hfamily.trans htarget)

/-- Scalar action transports through a linear realization. -/
private theorem realized_operator_eq_scalar
    {A V W : Type}
    [Group A]
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {P : ProjectiveRepresentation ℂ A V}
    {R : ProjectiveRepresentation ℂ A W}
    (E : V ≃ₗ[ℂ] W)
    (hintertwining :
      ∀ (a : A) (v : V),
        E (P.operator a v) = R.operator a (E v))
    (a : A) (z : ℂˣ)
    (hscalar :
      P.operator a = scalarLinearEquiv ℂ V z) :
    R.operator a = scalarLinearEquiv ℂ W z := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := E.surjective w
  calc
    R.operator a (E v) =
        E (P.operator a v) :=
      (hintertwining a v).symm
    _ = E ((scalarLinearEquiv ℂ V z) v) := by
      rw [hscalar]
    _ = E ((z : ℂ) • v) := by
      rw [scalarLinearEquiv_apply]
    _ = (z : ℂ) • E v := E.map_smul _ _
    _ = (scalarLinearEquiv ℂ W z) (E v) := by
      rw [scalarLinearEquiv_apply]

/-- Exact common scalar action for the associated lifts, derived from the
coordinatewise centralizer scalars. -/
theorem scalar_agreement
    (C : LayerTensorPermutationCentralWitnessAssembly
      d hcoordinate θ)
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
  obtain ⟨z, hsource, htarget⟩ :=
    C.family.scalar_agreement h hh
  let z' : ℂˣ := C.gauge h * z
  have hsource' :
      (C.family.sourceProjective.rescale C.gauge).operator h =
        scalarLinearEquiv ℂ C.family.sourceTensorSpace z' := by
    rw [ProjectiveRepresentation.rescale_operator, hsource,
      ← scalarLinearEquiv_mul]
  have htarget' :
      (C.family.targetProjective.rescale C.gauge).operator h =
        scalarLinearEquiv ℂ C.family.targetTensorSpace z' := by
    rw [ProjectiveRepresentation.rescale_operator, htarget,
      ← scalarLinearEquiv_mul]
  refine ⟨z', ?_, ?_⟩
  · exact
      realized_operator_eq_scalar C.sourceRealization
        (P := C.family.sourceProjective.rescale C.gauge)
        (R := C.sourceLift.projective.comap
          (inertiaEmbedding d hcoordinate θ))
        (by
          intro x v
          exact C.sourceOperator_intertwining x v)
        h z' hsource'
  · exact
      realized_operator_eq_scalar C.targetRealization
        C.targetOperator_intertwining h z' htarget'

/-- Assemble a complete central-isomorphism witness from tensor-permutation
data and the ordinary group-theoretic restriction conditions. -/
def toCompleteCentralIsomorphismWitness
    (C : LayerTensorPermutationCentralWitnessAssembly
      d hcoordinate θ)
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

/-- In a minimal counterexample the ordinary group conditions are canonical,
so a tensor-permutation assembly gives the desired complete central witness. -/
def toCompleteCentralIsomorphismWitness_of_minimalCounterexample
    {d : ComponentOrbitLocalData D}
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    (C : LayerTensorPermutationCentralWitnessAssembly
      d hcoordinate θ)
    (hminimal : MinimalCounterexampleStructure P) :
    CompleteCentralIsomorphismWitness
      (sourceTriple θ) (targetTriple d θ) :=
  C.toCompleteCentralIsomorphismWitness
    (d.layerIntermediateInertiaRestrictionGroupData_of_minimalCounterexample
      hcoordinate hminimal θ)

end CanonicalIntersection

end LayerTensorPermutationCentralWitnessAssembly
end LayerProjectiveRestrictionAssembly

end InductiveMcKay
end McKayConjecture
