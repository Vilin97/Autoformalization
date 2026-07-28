/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveOperatorUniqueness
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentSourceRestriction

/-!
# Projective uniqueness for the coherent layer source action

Once a tensor-permutation operator is known to implement the ambient
conjugation action on the intrinsic irreducible layer restriction, Schur's
lemma identifies its projective class with the pullback of any complete
associated source lift.
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

/-- Covariance of the raw coherent source operators on the intrinsic layer
restriction implies the projective compatibility required by the canonical
realization criterion. -/
theorem canonicalSourceProjectiveCompatibility_of_normalCovariance
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ))
    (hcovariance :
      ∀ (a : targetInertiaGroup d θ)
        (x : (sourceTriple θ).normalSubgroup),
        (canonicalLayerTensorPermutationCocycleFamily
            d hcoordinate θ).sourceProjective.operator a *
            canonicalCoherentSourceNormalRestriction
              d hcoordinate θ x =
          canonicalCoherentSourceNormalRestriction
              d hcoordinate θ
              (MulAut.conjNormal
                (inertiaEmbedding d hcoordinate θ a) x) *
            (canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).sourceProjective.operator a) :
    ∀ a : targetInertiaGroup d θ,
      ProjectiveLinearGroup.mk ℂ R.space
          (AssociatedProjectiveRepresentation.conjugateOperator
            (canonicalCoherentSourceRestrictionLinearEquiv
              d hcoordinate θ R)
            ((canonicalLayerTensorPermutationCocycleFamily
              d hcoordinate θ).sourceProjective.operator a)) =
        (R.projective.comap
          (inertiaEmbedding d hcoordinate θ)).toProjectiveLinearGroup a := by
  intro a
  exact
    AssociatedProjectiveRepresentation.projectiveClass_conjugateOperator_eq_of_normal_covariance
      R.associated
      (canonicalCoherentSourceNormalRestriction
        d hcoordinate θ)
      (canonicalCoherentSourceNormalRestriction_simple
        d hcoordinate θ)
      (canonicalCoherentSourceRestrictionEquiv
        d hcoordinate θ R)
      (inertiaEmbedding d hcoordinate θ a)
      ((canonicalLayerTensorPermutationCocycleFamily
        d hcoordinate θ).sourceProjective.operator a)
      (hcovariance a)

end LayerProjectiveRestrictionAssembly
end InductiveMcKay
end McKayConjecture
