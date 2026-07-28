/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedGeneralExistence
import McKayConjecture.InductiveMcKay.ComponentOrbitCorrespondenceTransport
import McKayConjecture.InductiveMcKay.LayerCentralTripleCompatibility
import McKayConjecture.InductiveMcKay.LayerIntermediateCorrespondenceEquivariance
import McKayConjecture.InductiveMcKay.LayerMatchedInertiaRestriction

/-!
# Projective restriction assembly for the layer inertia triples

For coherent component-orbit local data and a layer character `θ`, the
inductive-McKay hypothesis supplies a complete local triple witness at every
component coordinate.  Its two projective lifts are therefore available
without any further hypothesis.

The desired layer witness is not their ordinary direct product.  Elements of
the matched inertia group can permute components, so a projective tensor
assembly must also identify the realized coordinate stabilizers and their
operators across those permutations.  This file records that missing datum
at exactly the operator-and-factor level:

* `ProjectiveLiftChart` realizes a coordinate lift inside one global
  projective lift;
* `ProjectiveLiftChart.PermutationCoherence` compares two such charts under
  conjugation by an inertia element, up to the scalar ambiguity inherent in
  projective representations; and
* `CoordinatePermutationProjectiveAssembly` packages these charts for all
  components.

No target association or central-isomorphism witness is assumed.
`LayerProjectiveRestrictionAssociation` proves that the multiplication laws
of a literal restriction are automatic and isolates its remaining simplicity
and character laws.  It also records the degree obstruction showing why those
laws do not follow from general inductive-McKay data.
`LayerTargetProjectiveAssembly` instead keeps an independently associated
target lift and compares the two global factor sets through tensor charts,
without imposing equality of representation spaces or degrees.
-/

noncomputable section

open scoped TensorProduct

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open GroupTheory

/-! ### Bundled lifts and realized charts -/

/-- A finite-dimensional projective lift without an association assertion. -/
structure CompleteProjectiveLift
    (A : Type) [Group A] [Finite A] where
  /-- Representation space. -/
  space : Type
  [addCommGroup : AddCommGroup space]
  [module : Module ℂ space]
  [moduleFinite : Module.Finite ℂ space]
  [nontrivial : Nontrivial space]
  /-- Projective representation on `A`. -/
  projective : ProjectiveRepresentation ℂ A space

attribute [instance]
  CompleteProjectiveLift.addCommGroup
  CompleteProjectiveLift.module
  CompleteProjectiveLift.moduleFinite
  CompleteProjectiveLift.nontrivial

namespace CompleteProjectiveLift

variable {A : Type} [Group A] [Finite A]

/-- Pull a bundled projective lift back along a group homomorphism. -/
def comap
    {B : Type} [Group B] [Finite B]
    (R : CompleteProjectiveLift A)
    (e : B →* A) :
    CompleteProjectiveLift B where
  space := R.space
  addCommGroup := R.addCommGroup
  module := R.module
  moduleFinite := R.moduleFinite
  nontrivial := R.nontrivial
  projective := R.projective.comap e

end CompleteProjectiveLift

/-- A finite-dimensional projective lift together with its association to a
character triple. -/
structure CompleteAssociatedProjectiveLift
    {A : Type} [Group A] [Finite A]
    (T : CharacterTriple A) where
  /-- Representation space. -/
  space : Type
  [addCommGroup : AddCommGroup space]
  [module : Module ℂ space]
  [moduleFinite : Module.Finite ℂ space]
  [nontrivial : Nontrivial space]
  /-- Projective lift on the ambient group of the triple. -/
  projective : ProjectiveRepresentation ℂ A space
  /-- Association of the lift to the triple. -/
  associated :
    AssociatedProjectiveRepresentation T space projective

attribute [instance]
  CompleteAssociatedProjectiveLift.addCommGroup
  CompleteAssociatedProjectiveLift.module
  CompleteAssociatedProjectiveLift.moduleFinite
  CompleteAssociatedProjectiveLift.nontrivial

namespace CompleteAssociatedProjectiveLift

variable {A : Type} [Group A] [Finite A]
variable {T : CharacterTriple A}

/-- The canonical normalized associated lift on the chosen realization of a
triple character. -/
def canonical (T : CharacterTriple A) :
    CompleteAssociatedProjectiveLift T where
  space := T.character.realization
  projective :=
    AssociatedGeneralExistence.projectiveRepresentation T
  associated :=
    AssociatedGeneralExistence.associated T

@[simp]
theorem canonical_projective (T : CharacterTriple A) :
    (canonical T).projective =
      AssociatedGeneralExistence.projectiveRepresentation T :=
  rfl

/-- The canonical lift is normalized. -/
theorem canonical_isNormalized (T : CharacterTriple A) :
    (canonical T).projective.IsNormalized :=
  AssociatedGeneralExistence.projectiveRepresentation_isNormalized T

/-- Forget association while retaining the selected projective lift. -/
def forget
    (R : CompleteAssociatedProjectiveLift T) :
    CompleteProjectiveLift A where
  space := R.space
  addCommGroup := R.addCommGroup
  module := R.module
  moduleFinite := R.moduleFinite
  nontrivial := R.nontrivial
  projective := R.projective

/-- Regard the restriction of a bundled lift as a bundled associated lift,
once association with the target triple has been supplied. -/
def comap
    {B : Type} [Group B] [Finite B]
    {U : CharacterTriple B}
    (R : CompleteAssociatedProjectiveLift T)
    (e : B →* A)
    (h :
      AssociatedProjectiveRepresentation
        U R.space (R.projective.comap e)) :
    CompleteAssociatedProjectiveLift U where
  space := R.space
  addCommGroup := R.addCommGroup
  module := R.module
  moduleFinite := R.moduleFinite
  nontrivial := R.nontrivial
  projective := R.projective.comap e
  associated := h

end CompleteAssociatedProjectiveLift

/-- A common realized subgroup on which a coordinate projective lift and a
global projective lift can be compared.

The chart group is deliberately caller-supplied.  This avoids asserting that
every abstract coordinate automorphism is realized by the ambient inertia
group.  A coordinate representation is not normally an invariant subspace
of the full tensor product, so the chart includes the complementary
projective factor and a linear equivalence from their tensor product. -/
structure ProjectiveLiftChart
    {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (R : CompleteProjectiveLift A)
    (S : CompleteProjectiveLift B) where
  /-- The actually realized coordinate stabilizer. -/
  chartGroup : Type
  [chartGroupGroup : Group chartGroup]
  [chartGroupFinite : Finite chartGroup]
  /-- Its action through the coordinate ambient group. -/
  coordinateChart : chartGroup →* A
  /-- Its action through the assembled ambient group. -/
  globalChart : chartGroup →* B
  /-- Tensor factor complementary to the selected coordinate. -/
  complementSpace : Type
  [complementAddCommGroup : AddCommGroup complementSpace]
  [complementModule : Module ℂ complementSpace]
  [complementModuleFinite : Module.Finite ℂ complementSpace]
  [complementNontrivial : Nontrivial complementSpace]
  /-- Projective action carried by all remaining tensor factors. -/
  complementProjective :
    ProjectiveRepresentation ℂ chartGroup complementSpace
  /-- Identification of the coordinate tensor its complement with the
  assembled space. -/
  realization :
    (R.space ⊗[ℂ] complementSpace) ≃ₗ[ℂ] S.space
  /-- The tensor operator and the global operator agree under the
  realization. -/
  operator_intertwining :
    ∀ (x : chartGroup)
      (w : R.space ⊗[ℂ] complementSpace),
      realization
          (((R.projective.comap coordinateChart).tensor
            complementProjective).operator x w) =
        S.projective.operator (globalChart x) (realization w)
  /-- The global factor is the product of the coordinate and complement
  factors. -/
  factor_compatibility :
    ∀ x y : chartGroup,
      R.projective.factor (coordinateChart x) (coordinateChart y) *
          complementProjective.factor x y =
        S.projective.factor (globalChart x) (globalChart y)

attribute [instance]
  ProjectiveLiftChart.chartGroupGroup
  ProjectiveLiftChart.chartGroupFinite
  ProjectiveLiftChart.complementAddCommGroup
  ProjectiveLiftChart.complementModule
  ProjectiveLiftChart.complementModuleFinite
  ProjectiveLiftChart.complementNontrivial

namespace ProjectiveLiftChart

variable {A B C : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable [Group C] [Finite C]
variable {R : CompleteProjectiveLift A}
variable {S : CompleteProjectiveLift B}
variable {L : CompleteProjectiveLift C}

/-- Operator-and-factor coherence between two coordinate charts which are
permuted by an element of the global ambient group.

The coordinate and complementary operators are compared only up to
element-dependent scalars, and their factor equations include the resulting
coboundaries.  Thus the structure respects projective equivalence rather
than silently demanding equality of chosen linear lifts. -/
structure PermutationCoherence
    (cR : InductiveMcKay.ProjectiveLiftChart R L)
    (cS : InductiveMcKay.ProjectiveLiftChart S L)
    (a : C) where
  /-- Relabelling of the two realized chart groups. -/
  chartRelabel : cR.chartGroup ≃* cS.chartGroup
  /-- Relabelling of the two coordinate ambient groups. -/
  coordinateRelabel : A ≃* B
  /-- The global charts are conjugate by the specified inertia element. -/
  globalChart_conjugation :
    ∀ x : cR.chartGroup,
      cS.globalChart (chartRelabel x) =
        a * cR.globalChart x * a⁻¹
  /-- The coordinate charts agree after relabelling. -/
  coordinateChart_relabel :
    ∀ x : cR.chartGroup,
      cS.coordinateChart (chartRelabel x) =
        coordinateRelabel (cR.coordinateChart x)
  /-- Relabelling of the two selected coordinate representation spaces. -/
  spaceRelabel : R.space ≃ₗ[ℂ] S.space
  /-- Scalar cochain comparing the chosen coordinate operators. -/
  coordinateScalar : cR.chartGroup → ℂˣ
  /-- Coordinate projective operators are transported up to their scalar
  cochain. -/
  coordinateOperator_relabel :
    ∀ (x : cR.chartGroup) (v : R.space),
      spaceRelabel
          (R.projective.operator (cR.coordinateChart x) v) =
        (coordinateScalar x : ℂ) •
          S.projective.operator
            (cS.coordinateChart (chartRelabel x))
            (spaceRelabel v)
  /-- Coordinate factor sets differ by the coboundary of
  `coordinateScalar`. -/
  coordinateFactor_relabel :
    ∀ x y : cR.chartGroup,
      R.projective.factor
            (cR.coordinateChart x) (cR.coordinateChart y) *
          coordinateScalar (x * y) =
        coordinateScalar x * coordinateScalar y *
          S.projective.factor
            (cS.coordinateChart (chartRelabel x))
            (cS.coordinateChart (chartRelabel y))
  /-- Relabelling of the complementary tensor factors. -/
  complementRelabel :
    cR.complementSpace ≃ₗ[ℂ] cS.complementSpace
  /-- Scalar cochain comparing the chosen complementary operators. -/
  complementScalar : cR.chartGroup → ℂˣ
  /-- Complementary projective operators are transported up to their scalar
  cochain. -/
  complementOperator_relabel :
    ∀ (x : cR.chartGroup) (w : cR.complementSpace),
      complementRelabel (cR.complementProjective.operator x w) =
        (complementScalar x : ℂ) •
          cS.complementProjective.operator (chartRelabel x)
            (complementRelabel w)
  /-- Complementary factor sets differ by the corresponding coboundary. -/
  complementFactor_relabel :
    ∀ x y : cR.chartGroup,
      cR.complementProjective.factor x y *
          complementScalar (x * y) =
        complementScalar x * complementScalar y *
          cS.complementProjective.factor
            (chartRelabel x) (chartRelabel y)
  /-- Tensor relabelling built from the coordinate and complement
  relabellings. -/
  tensorRelabel :
    (R.space ⊗[ℂ] cR.complementSpace) ≃ₗ[ℂ]
      (S.space ⊗[ℂ] cS.complementSpace)
  /-- The tensor relabelling has the expected value on pure tensors. -/
  tensorRelabel_tmul :
    ∀ (v : R.space) (w : cR.complementSpace),
      tensorRelabel (v ⊗ₜ[ℂ] w) =
        spaceRelabel v ⊗ₜ[ℂ] complementRelabel w
  /-- The scalar ambiguity comparing the global permutation operator with
  the relabelled full tensor product. -/
  permutationScalar : ℂˣ
  /-- The two tensor realizations agree up to that scalar. -/
  realization_permutation :
    ∀ w : R.space ⊗[ℂ] cR.complementSpace,
      cS.realization (tensorRelabel w) =
        (permutationScalar : ℂ) •
          L.projective.operator a (cR.realization w)

end ProjectiveLiftChart

/-! ### Coordinate lifts supplied by the inductive-McKay hypothesis -/

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

namespace ComponentOrbitLocalData

/-- The component character at coordinate `K` in the canonical
factorization of `θ`. -/
abbrev coordinateLayerCharacter
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    PPrimeIrreducibleCharacter K.1 p :=
  LayerComponentLocalData.coordinateCharacter θ K

/-- Ambient semidirect-product group at one component coordinate. -/
abbrev coordinateAmbientGroup
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :=
  K.1 ⋊[PPrimeCharacterStabilizer.ambientAction]
    PPrimeCharacterStabilizer (D.coordinate K)
      (coordinateLayerCharacter θ K)

/-- Intermediate semidirect-product group at one component coordinate. -/
abbrev coordinateIntermediateGroup
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :=
  (d.data K).toEquivariant.intermediate ⋊[
      EquivariantLocalCorrespondence.stabilizerIntermediateAction
        (d.data K).toEquivariant
        (coordinateLayerCharacter θ K)]
    PPrimeCharacterStabilizer (D.coordinate K)
      (coordinateLayerCharacter θ K)

/-- The ambient character triple occurring in the complete witness at
coordinate `K`. -/
abbrev coordinateAmbientTriple
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :=
  EquivariantLocalCorrespondence.ambientTriple
    (P := D.coordinate K) (coordinateLayerCharacter θ K)

/-- The intermediate character triple occurring in the complete witness at
coordinate `K`. -/
abbrev coordinateIntermediateTriple
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :=
  (d.data K).toEquivariant.intermediateTriple
    (coordinateLayerCharacter θ K)

/-- The canonical coordinate embedding connecting the two projective lifts
extracted below. -/
abbrev coordinateEmbedding
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :=
  (d.data K).toEquivariant.semidirectEmbedding
    (coordinateLayerCharacter θ K)

/-- The ambient associated projective lift extracted from the complete
component witness. -/
def coordinateAmbientLift
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    CompleteAssociatedProjectiveLift
      (coordinateAmbientTriple (D := D) θ K) := by
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
  exact
    { space := C.leftSpace
      projective := C.witness.leftProjective
      associated := C.witness.leftAssociated }

/-- The intermediate associated projective lift extracted from the same
complete component witness. -/
def coordinateIntermediateLift
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    CompleteAssociatedProjectiveLift
      (d.coordinateIntermediateTriple θ K) := by
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
  exact
    { space := C.rightSpace
      projective := C.witness.rightProjective
      associated := C.witness.rightAssociated }

end ComponentOrbitLocalData

/-! ### Matched layer inertia triples -/

namespace LayerProjectiveRestrictionAssembly

/-- The source inertia triple attached to a layer character. -/
abbrev sourceTriple
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    CharacterTriple
      (IrreducibleCharacter.inertia (layer G) θ.1) :=
  ofInertia (layer G) θ.1

/-- The matched local inertia triple attached to coherent component-orbit
data. -/
abbrev targetTriple
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    CharacterTriple
      (IrreducibleCharacter.inertia
        d.intermediateComponentLocal
        (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1) :=
  ofInertia d.intermediateComponentLocal
    (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1

/-- The canonical embedding of the matched local inertia group into the
source layer inertia group. -/
abbrev inertiaEmbedding
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    IrreducibleCharacter.inertia
        d.intermediateComponentLocal
        (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1 →*
      IrreducibleCharacter.inertia (layer G) θ.1 :=
  d.layerIntermediateInertiaEmbedding hcoordinate θ

@[simp]
theorem inertiaEmbedding_apply_coe
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (x :
      IrreducibleCharacter.inertia
        d.intermediateComponentLocal
        (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1) :
    ((inertiaEmbedding d hcoordinate θ x :
        IrreducibleCharacter.inertia (layer G) θ.1) : G) =
      (((x :
        IrreducibleCharacter.inertia
          d.intermediateComponentLocal
          (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1) :
        d.ambientIntermediate) : G) :=
  d.layerIntermediateInertiaEmbedding_apply_coe hcoordinate θ x

/-- The canonical normalized associated lift on the source layer inertia
triple. -/
def canonicalSourceLift
    (θ : PPrimeIrreducibleCharacter (layer G) p) :
    CompleteAssociatedProjectiveLift (sourceTriple θ) :=
  CompleteAssociatedProjectiveLift.canonical (sourceTriple θ)

/-- Operator-and-factor data assembling the ambient halves of all canonical
coordinate witnesses into one associated lift on the layer inertia group.

The two equations in each chart and the permutation coherences are the
concrete conditions which a dependent tensor construction must establish.
They are kept separate from association of the matched restriction. -/
structure CoordinatePermutationProjectiveAssembly
    (d : ComponentOrbitLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- The assembled associated projective lift on the layer inertia group. -/
  sourceLift :
    CompleteAssociatedProjectiveLift (sourceTriple θ)
  /-- Realization of every ambient coordinate lift inside `sourceLift`. -/
  ambientChart :
    ∀ K : ComponentIndex G,
      ProjectiveLiftChart
        (d.coordinateAmbientLift θ K).forget
        sourceLift.forget
  /-- Compatibility of those realizations with every component permutation
  induced by the layer inertia group. -/
  ambientPermutationCoherence :
    ∀ (a : IrreducibleCharacter.inertia (layer G) θ.1)
      (K : ComponentIndex G),
      ProjectiveLiftChart.PermutationCoherence
        (ambientChart K)
        (ambientChart ((a : G) • K))
        a

/-- The literal raw projective restriction of an assembled source lift. -/
def CoordinatePermutationProjectiveAssembly.restrictedLift
    {d : ComponentOrbitLocalData D}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    (A : CoordinatePermutationProjectiveAssembly d θ)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder) :
    CompleteProjectiveLift
      (IrreducibleCharacter.inertia
        d.intermediateComponentLocal
        (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1) :=
  A.sourceLift.forget.comap
    (inertiaEmbedding d hcoordinate θ)

/-- The two families of coordinate charts for the matched inertia triples.

The target global lift is literally the raw restriction of the source lift,
but no association of that restriction is assumed. -/
structure MatchedCoordinateProjectiveCharts
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- Ambient-side coordinate assembly. -/
  sourceAssembly :
    CoordinatePermutationProjectiveAssembly d θ
  /-- Realization of every intermediate coordinate lift inside the
  restricted global lift. -/
  intermediateChart :
    ∀ K : ComponentIndex G,
      ProjectiveLiftChart
        (d.coordinateIntermediateLift θ K).forget
        (sourceAssembly.restrictedLift hcoordinate)

/-- Compatibility of the source and target chart families with the canonical
coordinate and global embeddings. -/
structure MatchedCoordinateChartEmbedding
    {d : ComponentOrbitLocalData D}
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    (C : MatchedCoordinateProjectiveCharts d hcoordinate θ) where
  /-- Realized inclusion from each intermediate chart group to its ambient
  coordinate chart group. -/
  chartEmbedding :
    ∀ K : ComponentIndex G,
      (C.intermediateChart K).chartGroup →*
        (C.sourceAssembly.ambientChart K).chartGroup
  /-- The realized chart inclusion agrees with the canonical coordinate
  semidirect-product embedding. -/
  coordinateChart_embedding :
    ∀ (K : ComponentIndex G)
      (x : (C.intermediateChart K).chartGroup),
      (C.sourceAssembly.ambientChart K).coordinateChart
          (chartEmbedding K x) =
        d.coordinateEmbedding θ K
          ((C.intermediateChart K).coordinateChart x)
  /-- The same chart inclusion commutes with the canonical matched-inertia
  embedding on the assembled groups. -/
  globalChart_embedding :
    ∀ (K : ComponentIndex G)
      (x : (C.intermediateChart K).chartGroup),
      (C.sourceAssembly.ambientChart K).globalChart
          (chartEmbedding K x) =
        inertiaEmbedding d hcoordinate θ
          ((C.intermediateChart K).globalChart x)

/-- Permutation coherence for the intermediate coordinate charts. -/
structure MatchedIntermediatePermutationCoherence
    {d : ComponentOrbitLocalData D}
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    (C : MatchedCoordinateProjectiveCharts d hcoordinate θ) where
  /-- Compatibility of the intermediate coordinate realizations with every
  component permutation induced by the matched local inertia group. -/
  coherence :
    ∀ (a :
        IrreducibleCharacter.inertia
          d.intermediateComponentLocal
          (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1)
      (K : ComponentIndex G),
      ProjectiveLiftChart.PermutationCoherence
        (C.intermediateChart K)
        (C.intermediateChart
          ((((a : d.ambientIntermediate) : G)) • K))
        a

/-- Full two-sided coordinate permutation assembly.  It contains only raw
operator, factor, embedding, and permutation data; target association is not
one of its fields. -/
structure MatchedCoordinatePermutationProjectiveAssembly
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p) where
  /-- Source and target coordinate chart families. -/
  charts :
    MatchedCoordinateProjectiveCharts d hcoordinate θ
  /-- Compatibility with the canonical embeddings. -/
  embedding :
    MatchedCoordinateChartEmbedding charts
  /-- Compatibility under target component permutations. -/
  permutation :
    MatchedIntermediatePermutationCoherence charts

/-! ### Canonical coherent component-orbit specializations -/

/-- Two-sided projective assembly for the canonical coherent orbit data
chosen from pointwise nonempty local inductive-McKay data. -/
abbrev NonemptyMatchedCoordinatePermutationProjectiveAssembly
    (hdata :
      ∀ K : ComponentIndex G,
        Nonempty
          (LocalInductiveMcKayData (D.coordinate K)))
    (θ : PPrimeIrreducibleCharacter (layer G) p) :=
  MatchedCoordinatePermutationProjectiveAssembly
    (ComponentOrbitLocalData.ofNonempty hdata)
    (ComponentOrbitLocalData.ofNonempty_isCoordinateCorrespondenceEquivariant
      hdata)
    θ

/-- Two-sided projective assembly for the canonical coherent orbit data
chosen from the quasisimple inductive-McKay hypothesis. -/
abbrev QuasisimpleMatchedCoordinatePermutationProjectiveAssembly
    (h : QuasisimpleInductiveMcKayHypothesis.{0} p)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :=
  MatchedCoordinatePermutationProjectiveAssembly
    (ComponentOrbitLocalData.ofQuasisimpleHypothesis
      (D := D) h)
    (ComponentOrbitLocalData.ofQuasisimpleHypothesis_isCoordinateCorrespondenceEquivariant
      (D := D) h)
    θ

end LayerProjectiveRestrictionAssembly

end InductiveMcKay
end McKayConjecture
