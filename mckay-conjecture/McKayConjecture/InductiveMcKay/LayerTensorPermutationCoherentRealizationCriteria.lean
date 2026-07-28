/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentNormalCancellation
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentSourceRestriction
import McKayConjecture.InductiveMcKay.LayerTensorPermutationRealizationCriteria

/-!
# Realization criterion after coherent normal-coordinate assembly

The coherent-coordinate calculation removes the target normal-trace field
from the canonical realization problem.  After an exact source realization,
it is enough to know that its chosen gauge cancels the explicitly
constructed common normal scalar.  The target normal-trace formula then
follows formally.
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

/-- Cancellation of the coherent common scalar gives the exact target
normal-trace formula after rescaling. -/
theorem canonicalTargetTensor_trace_rescaled_normal_of_coherentScalarCancellation
    (gauge : targetInertiaGroup d θ → ℂˣ)
    (hcancel :
      ∀ x : (targetTriple d θ).normalSubgroup,
        gauge (x : targetInertiaGroup d θ) *
            coherentNormalTraceScalar
              (hcoordinate := hcoordinate) x =
          1)
    (x : (targetTriple d θ).normalSubgroup) :
    let F :=
      canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ
    LinearMap.trace ℂ F.targetTensorSpace
        ((F.targetProjective.rescale gauge).operator
          (x : targetInertiaGroup d θ)) =
      (targetTriple d θ).character.values x := by
  dsimp only
  rw [ProjectiveRepresentation.rescale_operator]
  change
    LinearMap.trace ℂ
        (canonicalLayerTensorPermutationCocycleFamily
          d hcoordinate θ).targetTensorSpace
        ((gauge (x : targetInertiaGroup d θ) : ℂ) •
          ((canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).targetProjective.operator
              (x : targetInertiaGroup d θ) :
            (canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).targetTensorSpace →ₗ[ℂ]
            (canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).targetTensorSpace)) =
      _
  rw [map_smul,
    canonicalTargetProjective_trace_normal_eq_commonScalar_mul]
  rw [smul_eq_mul]
  calc
    (gauge (x : targetInertiaGroup d θ) : ℂ) *
        ((coherentNormalTraceScalar
          (hcoordinate := hcoordinate) x : ℂ) *
          (targetTriple d θ).character.values x) =
      ((gauge (x : targetInertiaGroup d θ) *
        coherentNormalTraceScalar
          (hcoordinate := hcoordinate) x : ℂˣ) : ℂ) *
        (targetTriple d θ).character.values x := by
      simp only [Units.val_mul, mul_assoc]
    _ = (targetTriple d θ).character.values x := by
      rw [hcancel x]
      simp

/-- Exact source realization plus cancellation of the coherent normal scalar
constructs all canonical realization data; no separate target trace or
target association hypothesis remains. -/
def canonicalRealizationDataOfSourceRealizationAndCoherentScalarCancellation
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
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
    (hcancel :
      ∀ x : (targetTriple d θ).normalSubgroup,
        gauge (x : targetInertiaGroup d θ) *
            coherentNormalTraceScalar
              (hcoordinate := hcoordinate) x =
          1) :
    CanonicalLayerTensorPermutationRealizationData
      d hcoordinate θ :=
  canonicalRealizationDataOfSourceRealizationAndTrace
    g gauge R E hsource
    (canonicalTargetTensor_trace_rescaled_normal_of_coherentScalarCancellation
      gauge hcancel)

/-- Exact source realization plus its intrinsic coherent normal-operator
intertwining constructs all canonical realization data.  Operator
cancellation supplies the scalar identity, so no character-value division
or separate scalar-cancellation hypothesis is needed. -/
def canonicalRealizationDataOfSourceRealizationAndCoherentNormalIntertwining
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
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
    CanonicalLayerTensorPermutationRealizationData
      d hcoordinate θ :=
  canonicalRealizationDataOfSourceRealizationAndCoherentScalarCancellation
    g gauge R E hsource
    (coherentNormalScalarCancellation_of_sourceNormalOperatorIntertwining
      gauge R E hsource hnormal)

/-- With the source equivalence selected from the intrinsic descended
normal representation, exact source realization alone constructs all
canonical realization data.  The coherent normal intertwining used for
scalar cancellation is supplied by the construction itself. -/
def canonicalRealizationDataOfIntrinsicSourceRealization
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
    (gauge : targetInertiaGroup d θ → ℂˣ)
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ))
    (hsource :
      ∀ (a : targetInertiaGroup d θ)
        (v :
          (canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).sourceTensorSpace),
        canonicalCoherentSourceRestrictionLinearEquiv
            d hcoordinate θ R
            (((canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).sourceProjective.rescale gauge).operator a v) =
          R.projective.operator
            (inertiaEmbedding d hcoordinate θ a)
            (canonicalCoherentSourceRestrictionLinearEquiv
              d hcoordinate θ R v)) :
    CanonicalLayerTensorPermutationRealizationData
      d hcoordinate θ :=
  canonicalRealizationDataOfSourceRealizationAndCoherentNormalIntertwining
    g gauge R
    (canonicalCoherentSourceRestrictionLinearEquiv
      d hcoordinate θ R)
    hsource
    (canonicalCoherentSourceRestrictionLinearEquiv_coherentNormal_intertwines
      g R)

/-- Projective-linear compatibility of the canonical tensor operators with
one complete source lift is now the only source-realization input: the
common gauge and every normal-operator identity follow intrinsically. -/
theorem nonempty_canonicalRealizationData_of_intrinsicSourceProjectiveCompatibility
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ))
    (hprojective :
      ∀ a : targetInertiaGroup d θ,
        ProjectiveLinearGroup.mk ℂ R.space
            (AssociatedProjectiveRepresentation.conjugateOperator
              (canonicalCoherentSourceRestrictionLinearEquiv
                d hcoordinate θ R)
              ((canonicalLayerTensorPermutationCocycleFamily
                d hcoordinate θ).sourceProjective.operator a)) =
          (R.projective.comap
            (inertiaEmbedding d hcoordinate θ)).toProjectiveLinearGroup a) :
    Nonempty
      (CanonicalLayerTensorPermutationRealizationData
        d hcoordinate θ) := by
  obtain ⟨gauge, hsource⟩ :=
    exists_canonicalSourceGaugeRealization
      R
      (canonicalCoherentSourceRestrictionLinearEquiv
        d hcoordinate θ R)
      hprojective
  exact
    ⟨canonicalRealizationDataOfIntrinsicSourceRealization
      g gauge R hsource⟩

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
