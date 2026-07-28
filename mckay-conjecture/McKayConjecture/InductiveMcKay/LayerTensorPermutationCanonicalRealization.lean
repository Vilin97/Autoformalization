/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerMatchedInertiaRestriction
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentRealizationCriteria
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentSourceCovariance
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCoherentSourceProjectiveUniqueness

/-!
# Canonical realization of the layer tensor-permutation family

The raw source tensor-permutation operators covary with the intrinsic
irreducible layer restriction.  Projective Schur uniqueness therefore
identifies their projective classes with the pullback of any complete
associated source lift.  The resulting gauge supplies the exact source
intertwining, while the coherent normal-operator calculation supplies the
target association.

This closes the canonical layer realization obligation in the
minimal-counterexample reduction.
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

/-- The canonical tensor-permutation family admits complete realization
data for every exact central restriction and every complete associated
source lift. -/
theorem nonempty_canonicalLayerTensorPermutationRealizationData
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ)) :
    Nonempty
      (CanonicalLayerTensorPermutationRealizationData
        d hcoordinate θ) :=
  nonempty_canonicalRealizationData_of_intrinsicSourceProjectiveCompatibility
    g R
    (canonicalSourceProjectiveCompatibility_of_normalCovariance
      R canonicalSourceProjective_normalCovariance)

/-- A selected canonical realization datum, obtained from source covariance
and projective Schur uniqueness. -/
def canonicalLayerTensorPermutationRealizationData
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ)) :
    CanonicalLayerTensorPermutationRealizationData
      d hcoordinate θ :=
  Classical.choice
    (nonempty_canonicalLayerTensorPermutationRealizationData g R)

end LayerProjectiveRestrictionAssembly

open GroupTheory
open LayerProjectiveRestrictionAssembly

/-- The canonical layer tensor-permutation realization obligation used by
the minimal-counterexample reduction is a theorem. -/
theorem canonicalMinimalLayerTensorPermutationRealizationHypothesis
    {p : ℕ} [Fact p.Prime] :
    CanonicalMinimalLayerTensorPermutationRealizationHypothesis p := by
  intro covers G _ _ P hminimal
  dsimp only
  intro θ
  let d :=
    canonicalComponentOrbitLocalData covers P
  let hcoordinate :=
    ComponentOrbitLocalData.ofQuasisimpleHypothesis_isCoordinateCorrespondenceEquivariant
      (D := canonicalLayerSylowCoordinateData P)
      covers
  let g :=
    d.layerIntermediateInertiaRestrictionGroupData_of_minimalCounterexample
      hcoordinate hminimal θ
  exact
    nonempty_canonicalLayerTensorPermutationRealizationData
      g (canonicalSourceLift θ)

end InductiveMcKay
end McKayConjecture
