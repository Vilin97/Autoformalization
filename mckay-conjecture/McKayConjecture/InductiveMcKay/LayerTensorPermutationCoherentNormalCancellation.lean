/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentNormalTrace

/-!
# Operator-level cancellation of coherent normal scalars

The raw source tensor-permutation operator at a target-normal element is a
nonzero scalar times its coherent normal-coordinate operator.  If an exact
source realization intertwines both the rescaled raw operator and that
coherent normal operator with the same associated source operator, then the
two operators cancel.  This proves the scalar identity without dividing by a
possibly zero character value.
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

/-- Intertwining the coherent source normal operator with the same source
operator as the rescaled tensor-permutation realization forces the gauge to
cancel the coherent common scalar. -/
theorem coherentNormalScalarCancellation_of_sourceNormalOperatorIntertwining
    (gauge : targetInertiaGroup d θ → ℂˣ)
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ))
    (E :
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ] R.space)
    (hsource :
      ∀ (a : targetInertiaGroup d θ)
        (v :
          (canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).sourceTensorSpace),
        E
            (((canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).sourceProjective.rescale gauge).operator a v) =
          R.projective.operator
            (inertiaEmbedding d hcoordinate θ a) (E v))
    (hnormal :
      ∀ (x : (targetTriple d θ).normalSubgroup)
        (v :
          (canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).sourceTensorSpace),
        E
            (canonicalCoherentSourceNormalOperator
              (hcoordinate := hcoordinate) x v) =
          R.projective.operator
            (inertiaEmbedding d hcoordinate θ
              (x : targetInertiaGroup d θ)) (E v)) :
    ∀ x : (targetTriple d θ).normalSubgroup,
      gauge (x : targetInertiaGroup d θ) *
          coherentNormalTraceScalar
            (hcoordinate := hcoordinate) x =
        1 := by
  intro x
  let F :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  let N : F.sourceTensorSpace ≃ₗ[ℂ] F.sourceTensorSpace :=
    canonicalCoherentSourceNormalOperator
      (hcoordinate := hcoordinate) x
  letI : Nontrivial F.sourceTensorSpace :=
    F.sourceTensorNontrivial
  have hrescaled :
      (F.sourceProjective.rescale gauge).operator
          (x : targetInertiaGroup d θ) =
        N := by
    ext v
    apply E.injective
    exact
      (hsource (x : targetInertiaGroup d θ) v).trans
        (hnormal x v).symm
  have hscaled :
      scalarLinearEquiv ℂ F.sourceTensorSpace
            (gauge (x : targetInertiaGroup d θ) *
              coherentNormalTraceScalar
                (hcoordinate := hcoordinate) x) *
          N =
        N := by
    rw [scalarLinearEquiv_mul, mul_assoc]
    rw [
      ← canonicalSourceProjective_operator_normal_eq_commonScalar_mul
        (hcoordinate := hcoordinate) x]
    rw [← ProjectiveRepresentation.rescale_operator]
    exact hrescaled
  have hscalar :
      scalarLinearEquiv ℂ F.sourceTensorSpace
          (gauge (x : targetInertiaGroup d θ) *
            coherentNormalTraceScalar
              (hcoordinate := hcoordinate) x) =
        1 := by
    apply mul_right_cancel (b := N)
    simpa using hscaled
  apply scalarLinearEquiv_injective ℂ F.sourceTensorSpace
  simpa using hscalar

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
