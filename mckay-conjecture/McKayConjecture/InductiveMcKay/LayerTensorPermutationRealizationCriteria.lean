/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedOperatorTransport
import McKayConjecture.InductiveMcKay.LayerProjectiveRestrictionAssociation
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCanonicalAssembly

/-!
# Realization criteria for the canonical layer tensor construction

The canonical source and target tensor-permutation representations have
equal factor sets.  Consequently, once a common gauge realizes the source
tensor as the restriction of an associated source lift, the target factors
are automatically trivial whenever either input lies in the target normal
subgroup.  Intrinsic target association then reduces to one concrete
normal-trace identity.
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

/-- Projective-linear compatibility with a full associated source lift
constructs the common gauge and the exact source realization. -/
theorem exists_canonicalSourceGaugeRealization
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ))
    (E :
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceTensorSpace ≃ₗ[ℂ] R.space)
    (hprojective :
      ∀ a : targetInertiaGroup d θ,
        ProjectiveLinearGroup.mk ℂ R.space
            (AssociatedProjectiveRepresentation.conjugateOperator E
              ((canonicalLayerTensorPermutationCocycleFamily
                d hcoordinate θ).sourceProjective.operator a)) =
          (R.projective.comap
            (inertiaEmbedding d hcoordinate θ)).toProjectiveLinearGroup a) :
    ∃ gauge : targetInertiaGroup d θ → ℂˣ,
      ∀ (a : targetInertiaGroup d θ)
        (v :
          (canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).sourceTensorSpace),
        E
            (((canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).sourceProjective.rescale gauge).operator a v) =
          R.projective.operator
            (inertiaEmbedding d hcoordinate θ a) (E v) :=
  AssociatedProjectiveRepresentation.exists_gauge_operatorEquiv
    E hprojective

/-- The source realization forces the target tensor factor to be trivial
when its first input lies in the target normal subgroup. -/
theorem canonicalTargetTensor_factor_normal_left
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
    (x : (targetTriple d θ).normalSubgroup)
    (a : targetInertiaGroup d θ) :
    ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).targetProjective.rescale gauge).factor
          (x : targetInertiaGroup d θ) a =
      1 := by
  let F :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  have hsourceFactor :
      (F.sourceProjective.rescale gauge).factor
            (x : targetInertiaGroup d θ) a =
        R.projective.factor
          (inertiaEmbedding d hcoordinate θ x)
          (inertiaEmbedding d hcoordinate θ a) := by
    exact
      AssociatedProjectiveRepresentation.factor_eq_of_equiv_operator_eq
        (P := F.sourceProjective.rescale gauge)
        (Q := R.projective.comap
          (inertiaEmbedding d hcoordinate θ))
        E hsource (x : targetInertiaGroup d θ) a
  calc
    (F.targetProjective.rescale gauge).factor
          (x : targetInertiaGroup d θ) a =
        (F.sourceProjective.rescale gauge).factor
          (x : targetInertiaGroup d θ) a := by
      simp only [ProjectiveRepresentation.rescale_factor,
        F.factor_agreement]
    _ = R.projective.factor
          (inertiaEmbedding d hcoordinate θ x)
          (inertiaEmbedding d hcoordinate θ a) :=
      hsourceFactor
    _ = 1 := by
      rw [← g.normalMap_coe x]
      exact
        R.associated.factor_normal_left
          (g.normalMap x)
          (inertiaEmbedding d hcoordinate θ a)

/-- The source realization forces the target tensor factor to be trivial
when its second input lies in the target normal subgroup. -/
theorem canonicalTargetTensor_factor_normal_right
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
    (a : targetInertiaGroup d θ)
    (x : (targetTriple d θ).normalSubgroup) :
    ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).targetProjective.rescale gauge).factor
          a (x : targetInertiaGroup d θ) =
      1 := by
  let F :=
    canonicalLayerTensorPermutationCocycleFamily
      d hcoordinate θ
  have hsourceFactor :
      (F.sourceProjective.rescale gauge).factor
            a (x : targetInertiaGroup d θ) =
        R.projective.factor
          (inertiaEmbedding d hcoordinate θ a)
          (inertiaEmbedding d hcoordinate θ x) := by
    exact
      AssociatedProjectiveRepresentation.factor_eq_of_equiv_operator_eq
        (P := F.sourceProjective.rescale gauge)
        (Q := R.projective.comap
          (inertiaEmbedding d hcoordinate θ))
        E hsource a (x : targetInertiaGroup d θ)
  calc
    (F.targetProjective.rescale gauge).factor
          a (x : targetInertiaGroup d θ) =
        (F.sourceProjective.rescale gauge).factor
          a (x : targetInertiaGroup d θ) := by
      simp only [ProjectiveRepresentation.rescale_factor,
        F.factor_agreement]
    _ = R.projective.factor
          (inertiaEmbedding d hcoordinate θ a)
          (inertiaEmbedding d hcoordinate θ x) :=
      hsourceFactor
    _ = 1 := by
      rw [← g.normalMap_coe x]
      exact
        R.associated.factor_normal_right
          (inertiaEmbedding d hcoordinate θ a)
          (g.normalMap x)

/-- Once the source tensor has been extended with the common gauge,
intrinsic target association follows from the target normal-trace formula.
-/
def canonicalTargetTensorAssociatedOfSourceRealizationAndTrace
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
    (htrace :
      ∀ x : (targetTriple d θ).normalSubgroup,
        LinearMap.trace ℂ
            (canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).targetTensorSpace
            (((canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).targetProjective.rescale gauge).operator
                (x : targetInertiaGroup d θ)) =
          (targetTriple d θ).character.values x) :
    AssociatedProjectiveRepresentation
      (targetTriple d θ)
      (canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).targetTensorSpace
      ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).targetProjective.rescale gauge) :=
  AssociatedProjectiveRepresentation.ofFactorNormalAndTrace
    (canonicalTargetTensor_factor_normal_left
      g gauge R E hsource)
    (canonicalTargetTensor_factor_normal_right
      g gauge R E hsource)
    htrace

/-- Source realization together with the target normal-trace formula
constructs the complete canonical realization record. -/
def canonicalRealizationDataOfSourceRealizationAndTrace
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
    (htrace :
      ∀ x : (targetTriple d θ).normalSubgroup,
        LinearMap.trace ℂ
            (canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).targetTensorSpace
            (((canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).targetProjective.rescale gauge).operator
                (x : targetInertiaGroup d θ)) =
          (targetTriple d θ).character.values x) :
    CanonicalLayerTensorPermutationRealizationData
      d hcoordinate θ where
  gauge := gauge
  sourceLift := R
  sourceRealization := E
  sourceOperator_intertwining := hsource
  targetAssociated :=
    canonicalTargetTensorAssociatedOfSourceRealizationAndTrace
      g gauge R E hsource htrace

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
