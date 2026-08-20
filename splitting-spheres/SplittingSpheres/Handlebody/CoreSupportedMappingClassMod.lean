/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.RelationMappingClassMod
public import SplittingSpheres.Handlebody.CoreExtensionBallSupport

/-!
# Capping on core-supported mapping classes modulo displayed ball support

The source first quotient uses only jointly smooth families whose every slice stays in the fixed
core-supported subgroup.  Its second quotient declares trivial precisely those representatives
supported in a displayed model-coordinate four-ball whose whole coordinate domain lies in the
actual one-handle interior.

Smooth capping preserves both the constrained endpoint relation and this selected support set, so
it descends to the corresponding double quotient.  On the sphere, the generic relation quotient
and selected set are definitionally the existing empty-relative mapping-class quotient modulo
displayed coordinate-four-ball support.

No injectivity claim is made for the descended homomorphism.
-/

@[expose] public section

noncomputable section

open Function Set
open scoped ContDiff Manifold

namespace SplittingSpheres

/-- The constrained core-supported mapping-class group, additionally modulo representatives
supported in displayed model-coordinate balls contained in the actual handle interior. -/
abbrev OneHandleCoreMappingClassMod (rho : ℝ) :=
  RelationMappingClassMod
    (OneHandleCoreSmoothlyDiffeotopic rho)
    (oneHandleCoreSupportedInSomeInteriorModelCoordinateFourBall rho)

/-- Canonical projection from core-supported one-handle diffeomorphisms to the constrained double
quotient. -/
def oneHandleCoreMappingClassModMk (rho : ℝ) :
    OneHandleCoreSupportedRelativeDiff rho →* OneHandleCoreMappingClassMod rho :=
  relationMappingClassModMk
    (OneHandleCoreSmoothlyDiffeotopic rho)
    (oneHandleCoreSupportedInSomeInteriorModelCoordinateFourBall rho)

@[simp]
theorem oneHandleCoreMappingClassModMk_one (rho : ℝ) :
    oneHandleCoreMappingClassModMk rho 1 = 1 :=
  map_one _

/-- Every representative selected by an interior displayed model-coordinate ball is trivial in
the source double quotient. -/
theorem oneHandleCoreMappingClassModMk_eq_one
    {rho : ℝ} {f : OneHandleCoreSupportedRelativeDiff rho}
    (hf : f ∈ oneHandleCoreSupportedInSomeInteriorModelCoordinateFourBall rho) :
    oneHandleCoreMappingClassModMk rho f = 1 :=
  relationMappingClassModMk_eq_one hf

/-- The generic target double quotient is definitionally the existing empty-relative mapping-class
quotient modulo displayed coordinate-four-ball support. -/
theorem sphereRelationMappingClassModCoordinateBall_eq :
    RelationMappingClassMod
        SphereEmptyRelativeSmoothlyDiffeotopic
        (relativeDiffSupportedInSomeCoordinateFourBall (∅ : Set (Sphere 4))) =
      RelativeMappingClassModCoordinateBall (∅ : Set (Sphere 4)) :=
  rfl

/-- The corresponding canonical maps from sphere diffeomorphisms are also definitionally equal. -/
theorem sphereRelationMappingClassModCoordinateBallMk_eq :
    relationMappingClassModMk
        SphereEmptyRelativeSmoothlyDiffeotopic
        (relativeDiffSupportedInSomeCoordinateFourBall (∅ : Set (Sphere 4))) =
      relativeMappingClassModCoordinateBallMk (∅ : Set (Sphere 4)) :=
  rfl

/-- Smooth capping descends through both the constrained diffeotopy quotient and the displayed
coordinate-ball support quotient. -/
def smoothOneHandleCoreMappingClassModExtension
    {rho : ℝ} (hrho : rho < 1) :
    OneHandleCoreMappingClassMod rho →*
      RelativeMappingClassModCoordinateBall (∅ : Set (Sphere 4)) :=
  relationMappingClassModMap
    (smoothOneHandleCoreExtensionRelativeHom hrho)
    (smoothOneHandleCoreExtension_preservesEndpointRelation hrho)
    (oneHandleCoreSupportedInSomeInteriorModelCoordinateFourBall rho)
    (relativeDiffSupportedInSomeCoordinateFourBall (∅ : Set (Sphere 4)))
    (smoothOneHandleCoreExtensionRelativeHom_mapsTo_coordinateBallSupported hrho)

/-- Exact representative formula for the descended double-quotient capping map. -/
@[simp]
theorem smoothOneHandleCoreMappingClassModExtension_mk
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho) :
    smoothOneHandleCoreMappingClassModExtension hrho
        (oneHandleCoreMappingClassModMk rho f) =
      relativeMappingClassModCoordinateBallMk (∅ : Set (Sphere 4))
        (smoothOneHandleCoreExtensionRelativeHom hrho f) :=
  relationMappingClassModMap_apply _ _ _ _ _ f

@[simp]
theorem smoothOneHandleCoreMappingClassModExtension_one
    {rho : ℝ} (hrho : rho < 1) :
    smoothOneHandleCoreMappingClassModExtension hrho 1 = 1 :=
  map_one _

/-- The descended capping map sends every selected source representative to the identity. -/
theorem smoothOneHandleCoreMappingClassModExtension_mk_eq_one
    {rho : ℝ} (hrho : rho < 1)
    {f : OneHandleCoreSupportedRelativeDiff rho}
    (hf : f ∈ oneHandleCoreSupportedInSomeInteriorModelCoordinateFourBall rho) :
    smoothOneHandleCoreMappingClassModExtension hrho
        (oneHandleCoreMappingClassModMk rho f) = 1 := by
  rw [oneHandleCoreMappingClassModMk_eq_one hf, map_one]

/-- Concrete displayed-ball form of the selected-representative identity theorem. -/
theorem smoothOneHandleCoreMappingClassModExtension_mk_eq_one_of_supported
    {rho : ℝ} (hrho : rho < 1)
    (B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece)
    (hB : B.domain ≤ oneHandlePieceInterior)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hf : DiffeomorphSupportedIn f.1.1 B.carrier) :
    smoothOneHandleCoreMappingClassModExtension hrho
        (oneHandleCoreMappingClassModMk rho f) = 1 :=
  smoothOneHandleCoreMappingClassModExtension_mk_eq_one hrho
    ⟨B, hB, hf⟩

end SplittingSpheres
