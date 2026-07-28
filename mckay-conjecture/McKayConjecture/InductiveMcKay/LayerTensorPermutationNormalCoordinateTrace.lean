/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralizerNormalTrace
import McKayConjecture.InductiveMcKay.LayerTensorPermutationNormalTrace

/-!
# Coordinate traces at normal layer elements

This file isolates the local representation-theoretic step in the normal
trace calculation.  If a selected semidirect representative induces the
same automorphism as an element of the coordinate intermediate, then their
quotient centralizes the source coordinate normal subgroup.  The complete
local central witness consequently expresses both coordinate traces using
one common nonzero scalar.
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

/-- The canonical source normal-copy element attached to an intermediate
coordinate element. -/
def coordinateSourceNormalElement
    (R : ComponentIndex G)
    (y : d.intermediate R) :
    (ComponentOrbitLocalData.coordinateAmbientTriple
      (D := D) θ R).normalSubgroup :=
  ⟨SemidirectProduct.inl (y : R.1), ⟨(y : R.1), rfl⟩⟩

/-- The canonical target normal-copy element attached to an intermediate
coordinate element. -/
def coordinateTargetNormalElement
    (R : ComponentIndex G)
    (y : d.intermediate R) :
    (d.coordinateIntermediateTriple θ R).normalSubgroup :=
  ⟨SemidirectProduct.inl y, ⟨y, rfl⟩⟩

@[simp]
theorem coordinateEmbedding_targetNormalElement
    (R : ComponentIndex G)
    (y : d.intermediate R) :
    d.coordinateEmbedding θ R
        (coordinateTargetNormalElement (d := d) (θ := θ) R y) =
      coordinateSourceNormalElement (d := d) (θ := θ) R y := by
  apply SemidirectProduct.ext
  · rfl
  · rfl

@[simp]
theorem coordinateSourceNormalElement_character
    (R : ComponentIndex G)
    (y : d.intermediate R) :
    (ComponentOrbitLocalData.coordinateAmbientTriple
      (D := D) θ R).character.values
        (coordinateSourceNormalElement (d := d) (θ := θ) R y) =
      (ComponentOrbitLocalData.coordinateLayerCharacter θ R).1.values y := by
  rfl

@[simp]
theorem coordinateTargetNormalElement_character
    (R : ComponentIndex G)
    (y : d.intermediate R) :
    (d.coordinateIntermediateTriple θ R).character.values
        (coordinateTargetNormalElement (d := d) (θ := θ) R y) =
      (d.correspondence R
        (ComponentOrbitLocalData.coordinateLayerCharacter θ R)).1.values y := by
  rfl

@[simp]
theorem semidirectNormalAction_coordinateTargetNormalElement
    (R : ComponentIndex G)
    (y : d.intermediate R) :
    semidirectNormalAction
        (PPrimeCharacterStabilizer.ambientAction
          (P := D.coordinate R)
          (χ := ComponentOrbitLocalData.coordinateLayerCharacter θ R))
        (d.coordinateEmbedding θ R
          (coordinateTargetNormalElement
            (d := d) (θ := θ) R y)) =
      MulAut.conj (y : R.1) := by
  apply MulEquiv.ext
  intro z
  rfl

/-- The quotient of a selected semidirect representative by a coordinate
normal element centralizes the source normal copy as soon as the two
elements induce the same automorphism of the representative component. -/
theorem coordinateNormalResidual_mem_centralizer
    {o : LayerTargetComponentOrbit d θ}
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o)
    (y :
      d.intermediate
        (layerTargetComponentOrbitRepresentative d θ o))
    (hy :
      MulAut.conj
          (y :
            (layerTargetComponentOrbitRepresentative d θ o).1) =
        layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K) :
    d.coordinateEmbedding θ
          (layerTargetComponentOrbitRepresentative d θ o)
          (S.element a K *
            ((coordinateTargetNormalElement
                (d := d) (θ := θ)
                (layerTargetComponentOrbitRepresentative d θ o) y :
              (d.coordinateIntermediateTriple θ
                (layerTargetComponentOrbitRepresentative
                  d θ o)).normalSubgroup) :
              d.coordinateIntermediateGroup θ
                (layerTargetComponentOrbitRepresentative d θ o))⁻¹) ∈
      Subgroup.centralizer
        ((ComponentOrbitLocalData.coordinateAmbientTriple
          (D := D) θ
          (layerTargetComponentOrbitRepresentative d θ o)).normalSubgroup :
          Set (ComponentOrbitLocalData.coordinateAmbientGroup
            (D := D) θ
            (layerTargetComponentOrbitRepresentative d θ o))) := by
  apply mem_centralizer_semidirectNormalSubgroup_of_action_eq_one
  simp only [map_mul, map_inv, S.inducedAction]
  rw [
    semidirectNormalAction_coordinateTargetNormalElement, hy,
    mul_inv_cancel]

/-- Coordinate source and target transports are one common nonzero scalar
times the two matched normal-coordinate operators whenever the chosen
normal element induces the selected shifted-defect automorphism. -/
theorem exists_common_coordinate_operator_scalar_of_inducedAction
    {o : LayerTargetComponentOrbit d θ}
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o)
    (y :
      d.intermediate
        (layerTargetComponentOrbitRepresentative d θ o))
    (hy :
      MulAut.conj
          (y :
            (layerTargetComponentOrbitRepresentative d θ o).1) =
        layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K) :
    ∃ c : ℂˣ,
      S.sourceTransport a K =
          scalarLinearEquiv ℂ
              (canonicalOrbitSourceSpace d θ o) c *
            (d.coordinateAmbientLift θ
              (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
              (coordinateSourceNormalElement
                (d := d) (θ := θ)
                (layerTargetComponentOrbitRepresentative d θ o) y) ∧
        S.targetTransport a K =
          scalarLinearEquiv ℂ
              (canonicalOrbitTargetSpace d θ o) c *
            (d.coordinateIntermediateLift θ
              (layerTargetComponentOrbitRepresentative d θ o)).projective.operator
              (coordinateTargetNormalElement
                (d := d) (θ := θ)
                (layerTargetComponentOrbitRepresentative d θ o) y) := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let Ls := d.coordinateAmbientLift θ R
  let Lt := d.coordinateIntermediateLift θ R
  let xn :=
    coordinateSourceNormalElement (d := d) (θ := θ) R y
  let yn :=
    coordinateTargetNormalElement (d := d) (θ := θ) R y
  let b := S.element a K
  let z := b * (yn : d.coordinateIntermediateGroup θ R)⁻¹
  have hz :
      d.coordinateEmbedding θ R z ∈
        Subgroup.centralizer
          ((ComponentOrbitLocalData.coordinateAmbientTriple
            (D := D) θ R).normalSubgroup :
            Set (ComponentOrbitLocalData.coordinateAmbientGroup
              (D := D) θ R)) := by
    simpa only [R, z, b, yn] using
      coordinateNormalResidual_mem_centralizer
        (d := d) (θ := θ) S a K y hy
  obtain ⟨c, hsourceScalar, htargetScalar⟩ :=
    d.coordinateProjective_scalar_agreement θ R z hz
  have hb : z * (yn : d.coordinateIntermediateGroup θ R) = b := by
    simp only [z]
    group
  have hbSource :
      d.coordinateEmbedding θ R b =
        d.coordinateEmbedding θ R z *
          (xn :
            ComponentOrbitLocalData.coordinateAmbientGroup
              (D := D) θ R) := by
    rw [← hb, map_mul]
    exact congrArg
      (d.coordinateEmbedding θ R z * ·)
      (coordinateEmbedding_targetNormalElement
        (d := d) (θ := θ) R y)
  refine ⟨c, ?_, ?_⟩
  · change
      Ls.projective.operator (d.coordinateEmbedding θ R b) =
        scalarLinearEquiv ℂ (canonicalOrbitSourceSpace d θ o) c *
          Ls.projective.operator
            (xn :
              ComponentOrbitLocalData.coordinateAmbientGroup
                (D := D) θ R)
    rw [hbSource, Ls.associated.mul_normal, hsourceScalar]
  · change
      Lt.projective.operator b =
        scalarLinearEquiv ℂ (canonicalOrbitTargetSpace d θ o) c *
          Lt.projective.operator
            (yn : d.coordinateIntermediateGroup θ R)
    rw [← hb, Lt.associated.mul_normal, htargetScalar]

/-- Coordinate source and target traces are one common nonzero scalar times
the two matched normal-character values whenever the chosen normal element
induces the selected shifted-defect automorphism. -/
theorem exists_common_coordinate_trace_scalar_of_inducedAction
    {o : LayerTargetComponentOrbit d θ}
    (S : CanonicalOrbitSemidirectSection d θ o)
    (a : targetInertiaGroup d θ)
    (K : LayerTargetOrbitCoordinate d θ o)
    (y :
      d.intermediate
        (layerTargetComponentOrbitRepresentative d θ o))
    (hy :
      MulAut.conj
          (y :
            (layerTargetComponentOrbitRepresentative d θ o).1) =
        layerTargetOrbitShiftedDefectAutomorphism
          (d := d) (θ := θ) a K) :
    ∃ c : ℂˣ,
      LinearMap.trace ℂ (canonicalOrbitSourceSpace d θ o)
          (S.sourceTransport a K) =
          (c : ℂ) *
            (ComponentOrbitLocalData.coordinateLayerCharacter θ
              (layerTargetComponentOrbitRepresentative d θ o)).1.values y ∧
        LinearMap.trace ℂ (canonicalOrbitTargetSpace d θ o)
          (S.targetTransport a K) =
          (c : ℂ) *
            (d.correspondence
              (layerTargetComponentOrbitRepresentative d θ o)
              (ComponentOrbitLocalData.coordinateLayerCharacter θ
                (layerTargetComponentOrbitRepresentative d θ o))).1.values
                  y := by
  let R :=
    layerTargetComponentOrbitRepresentative d θ o
  let Ls := d.coordinateAmbientLift θ R
  let Lt := d.coordinateIntermediateLift θ R
  let xn :=
    coordinateSourceNormalElement (d := d) (θ := θ) R y
  let yn :=
    coordinateTargetNormalElement (d := d) (θ := θ) R y
  let b := S.element a K
  let z := b * (yn : d.coordinateIntermediateGroup θ R)⁻¹
  have hz :
      d.coordinateEmbedding θ R z ∈
        Subgroup.centralizer
          ((ComponentOrbitLocalData.coordinateAmbientTriple
            (D := D) θ R).normalSubgroup :
            Set (ComponentOrbitLocalData.coordinateAmbientGroup
              (D := D) θ R)) := by
    simpa only [R, z, b, yn] using
      coordinateNormalResidual_mem_centralizer
        (d := d) (θ := θ) S a K y hy
  obtain ⟨c, hsourceScalar, htargetScalar⟩ :=
    d.coordinateProjective_scalar_agreement θ R z hz
  have hb : z * (yn : d.coordinateIntermediateGroup θ R) = b := by
    simp only [z]
    group
  have hbSource :
      d.coordinateEmbedding θ R b =
        d.coordinateEmbedding θ R z *
          (xn :
            ComponentOrbitLocalData.coordinateAmbientGroup
              (D := D) θ R) := by
    rw [← hb, map_mul]
    exact congrArg
      (d.coordinateEmbedding θ R z * ·)
      (coordinateEmbedding_targetNormalElement
        (d := d) (θ := θ) R y)
  have hsourceOperatorEquiv :
      S.sourceTransport a K =
        scalarLinearEquiv ℂ (canonicalOrbitSourceSpace d θ o) c *
          Ls.projective.operator
            (xn :
              ComponentOrbitLocalData.coordinateAmbientGroup
                (D := D) θ R) := by
    change
      Ls.projective.operator (d.coordinateEmbedding θ R b) =
        scalarLinearEquiv ℂ (canonicalOrbitSourceSpace d θ o) c *
          Ls.projective.operator
            (xn :
              ComponentOrbitLocalData.coordinateAmbientGroup
                (D := D) θ R)
    rw [hbSource, Ls.associated.mul_normal, hsourceScalar]
  have hsourceOperator :
      (S.sourceTransport a K :
        canonicalOrbitSourceSpace d θ o →ₗ[ℂ]
          canonicalOrbitSourceSpace d θ o) =
        (c : ℂ) •
          (Ls.projective.operator
            (xn :
              ComponentOrbitLocalData.coordinateAmbientGroup
                (D := D) θ R) :
            canonicalOrbitSourceSpace d θ o →ₗ[ℂ]
              canonicalOrbitSourceSpace d θ o) := by
    exact congrArg LinearEquiv.toLinearMap hsourceOperatorEquiv
  have htargetOperatorEquiv :
      S.targetTransport a K =
        scalarLinearEquiv ℂ (canonicalOrbitTargetSpace d θ o) c *
          Lt.projective.operator
            (yn : d.coordinateIntermediateGroup θ R) := by
    change
      Lt.projective.operator b =
        scalarLinearEquiv ℂ (canonicalOrbitTargetSpace d θ o) c *
          Lt.projective.operator
            (yn : d.coordinateIntermediateGroup θ R)
    rw [← hb, Lt.associated.mul_normal, htargetScalar]
  have htargetOperator :
      (S.targetTransport a K :
        canonicalOrbitTargetSpace d θ o →ₗ[ℂ]
          canonicalOrbitTargetSpace d θ o) =
        (c : ℂ) •
          (Lt.projective.operator
            (yn : d.coordinateIntermediateGroup θ R) :
            canonicalOrbitTargetSpace d θ o →ₗ[ℂ]
              canonicalOrbitTargetSpace d θ o) := by
    exact congrArg LinearEquiv.toLinearMap htargetOperatorEquiv
  refine ⟨c, ?_, ?_⟩
  · rw [hsourceOperator, map_smul]
    have htrace := Ls.associated.traceFunction_normal xn
    change
      LinearMap.trace ℂ (canonicalOrbitSourceSpace d θ o)
          (Ls.projective.operator
            (xn :
              ComponentOrbitLocalData.coordinateAmbientGroup
                (D := D) θ R)) =
        (ComponentOrbitLocalData.coordinateAmbientTriple
          (D := D) θ R).character.values xn at htrace
    rw [htrace]
    rfl
  · rw [htargetOperator, map_smul]
    have htrace := Lt.associated.traceFunction_normal yn
    change
      LinearMap.trace ℂ (canonicalOrbitTargetSpace d θ o)
          (Lt.projective.operator
            (yn : d.coordinateIntermediateGroup θ R)) =
        (d.coordinateIntermediateTriple θ R).character.values yn at htrace
    rw [htrace]
    rfl

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
