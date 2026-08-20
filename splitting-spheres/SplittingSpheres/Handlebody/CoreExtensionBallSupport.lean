/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.ModelCoordinateBall
public import SplittingSpheres.Handlebody.CoreSupportedMappingClass
public import SplittingSpheres.Handlebody.OneHandleInteriorDiffeomorph

/-!
# Coordinate-ball support of smooth core extensions

A displayed four-ball in the compact one-handle uses the actual model with corners
`oneHandlePieceModel`.  When its coordinate domain lies in the model interior, the explicit
interior diffeomorphism transports it to a standard displayed coordinate four-ball in the literal
four-sphere.

A one-handle diffeomorphism supported in the source carrier extends to a sphere diffeomorphism
supported in the exact transported carrier.  Inside the open one-handle region this follows by
pulling back through the explicit diffeomorphism.  Outside that region, the core-support outer-band
identity theorem applies.  Consequently the empty-relative extension is trivial in the ordinary
mapping-class quotient modulo displayed coordinate-ball support.
-/

@[expose] public section

noncomputable section

open Function Set
open TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SplittingSpheres

/-- Transport a displayed model-coordinate ball in the compact one-handle interior to a standard
coordinate four-ball in the literal four-sphere. -/
def oneHandleCoreExtensionTransportedBall
    (B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece)
    (hB : B.domain ≤ oneHandlePieceInterior) : CoordinateFourBall (Sphere 4) :=
  (B.openTransport oneHandleInteriorToSphereRegionDiffeomorph hB).toCoordinateFourBall

/-- The open transport map is exactly the direct one-handle coordinate map after forgetting the
source-domain witness. -/
@[simp]
theorem oneHandleCoreExtension_openTransportMap
    (B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece)
    (hB : B.domain ≤ oneHandlePieceInterior) (x : B.domain) :
    ModelCoordinateFourBall.openTransportMap
        oneHandleInteriorToSphereRegionDiffeomorph B hB x =
      oneHandleSphereMap x.1 :=
  oneHandleInteriorToSphereRegionDiffeomorph_apply_coe
    ⟨x.1, hB x.2⟩

/-- The target carrier is the exact image of the source carrier under the direct one-handle
coordinate map, with the source point carrying its displayed-domain witness. -/
theorem carrier_oneHandleCoreExtensionTransportedBall_domainImage
    (B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece)
    (hB : B.domain ≤ oneHandlePieceInterior) :
    (oneHandleCoreExtensionTransportedBall B hB).carrier =
      (fun x : B.domain ↦ oneHandleSphereMap x.1) ''
        (Subtype.val ⁻¹' B.carrier) := by
  rw [oneHandleCoreExtensionTransportedBall,
    ModelCoordinateFourBall.carrier_toCoordinateFourBall,
    ModelCoordinateFourBall.carrier_openTransport]
  apply image_congr
  intro x _
  exact oneHandleCoreExtension_openTransportMap B hB x

/-- Equivalently, after forgetting the displayed-domain witness, the target carrier is exactly
the ambient image of the source carrier under `oneHandleSphereMap`. -/
theorem carrier_oneHandleCoreExtensionTransportedBall
    (B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece)
    (hB : B.domain ≤ oneHandlePieceInterior) :
    (oneHandleCoreExtensionTransportedBall B hB).carrier =
      oneHandleSphereMap '' B.carrier := by
  rw [carrier_oneHandleCoreExtensionTransportedBall_domainImage B hB]
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    let xDomain : B.domain := ⟨x, B.carrier_subset_domain hx⟩
    exact ⟨xDomain, hx, rfl⟩

/-- A core-supported one-handle diffeomorphism supported in a displayed interior ball has smooth
sphere extension supported in the exact transported coordinate-ball carrier. -/
theorem smoothOneHandleCoreExtensionDiffeomorph_supportedIn_transportedBall
    {rho : ℝ} (hrho : rho < 1)
    (B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece)
    (hB : B.domain ≤ oneHandlePieceInterior)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hf : DiffeomorphSupportedIn f.1.1 B.carrier) :
    DiffeomorphSupportedIn
      (smoothOneHandleCoreExtensionDiffeomorph hrho f)
      (oneHandleCoreExtensionTransportedBall B hB).carrier := by
  intro q hq
  by_cases hregion : q ∈ sphereHandleOneRegion
  · let qRegion : SphereHandleOneRegion := ⟨q, hregion⟩
    let xInterior : oneHandlePieceInterior :=
      oneHandleInteriorToSphereRegionDiffeomorph.symm qRegion
    have hq_map : oneHandleSphereMap xInterior.1 = q := by
      calc
        oneHandleSphereMap xInterior.1 =
            (oneHandleInteriorToSphereRegionDiffeomorph xInterior :
              SphereHandleOneRegion).1 :=
          (oneHandleInteriorToSphereRegionDiffeomorph_apply_coe xInterior).symm
        _ = q := by
          rw [show xInterior =
            oneHandleInteriorToSphereRegionDiffeomorph.symm qRegion from rfl,
            oneHandleInteriorToSphereRegionDiffeomorph.apply_symm_apply]
    have hx_not : xInterior.1 ∉ B.carrier := by
      intro hx
      apply hq
      rw [carrier_oneHandleCoreExtensionTransportedBall B hB]
      exact ⟨xInterior.1, hx, hq_map⟩
    rw [← hq_map, smoothOneHandleCoreExtensionDiffeomorph_apply,
      directCappedOneHandleExtensionSphere_oneHandle, hf hx_not]
  · have houter : q ∈ sphereHandleOuterBand rho := by
      have hcover : q ∈
          (sphereHandleInnerBand : Set (Sphere 4)) ∪ sphereHandleOuterBand rho := by
        rw [sphereHandleInnerBand_union_outerBand hrho]
        exact mem_univ q
      rcases hcover with hinner | houter
      · exact (hregion (by
          rw [← sphereHandleInnerBand_eq_oneRegion]
          exact hinner)).elim
      · exact houter
    exact smoothOneHandleCoreExtensionDiffeomorph_eq_on_outerBand
      hrho f ⟨q, houter⟩

/-- The same exact support statement for the extension viewed as an empty-relative
diffeomorphism. -/
theorem smoothOneHandleCoreExtensionRelativeHom_supportedIn_transportedBall
    {rho : ℝ} (hrho : rho < 1)
    (B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece)
    (hB : B.domain ≤ oneHandlePieceInterior)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hf : DiffeomorphSupportedIn f.1.1 B.carrier) :
    DiffeomorphSupportedIn
      (smoothOneHandleCoreExtensionRelativeHom hrho f).1
      (oneHandleCoreExtensionTransportedBall B hB).carrier :=
  smoothOneHandleCoreExtensionDiffeomorph_supportedIn_transportedBall
    hrho B hB f hf

/-- The empty-relative smooth extension belongs to the selected collection of diffeomorphisms
supported in some displayed coordinate four-ball. -/
theorem smoothOneHandleCoreExtensionRelativeHom_mem_coordinateBallSupported
    {rho : ℝ} (hrho : rho < 1)
    (B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece)
    (hB : B.domain ≤ oneHandlePieceInterior)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hf : DiffeomorphSupportedIn f.1.1 B.carrier) :
    smoothOneHandleCoreExtensionRelativeHom hrho f ∈
      relativeDiffSupportedInSomeCoordinateFourBall (∅ : Set (Sphere 4)) :=
  mem_relativeDiffSupportedInSomeCoordinateFourBall
    (oneHandleCoreExtensionTransportedBall B hB)
    (smoothOneHandleCoreExtensionRelativeHom_supportedIn_transportedBall
      hrho B hB f hf)

/-- The empty-relative mapping class of a ball-supported core extension is trivial after quotienting
by displayed coordinate-four-ball support. -/
theorem relativeMappingClassModCoordinateBallMk_smoothOneHandleCoreExtension_eq_one
    {rho : ℝ} (hrho : rho < 1)
    (B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece)
    (hB : B.domain ≤ oneHandlePieceInterior)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hf : DiffeomorphSupportedIn f.1.1 B.carrier) :
    relativeMappingClassModCoordinateBallMk (∅ : Set (Sphere 4))
        (smoothOneHandleCoreExtensionRelativeHom hrho f) = 1 :=
  relativeMappingClassModCoordinateBallMk_eq_one
    (oneHandleCoreExtensionTransportedBall B hB)
    (smoothOneHandleCoreExtensionRelativeHom_supportedIn_transportedBall
      hrho B hB f hf)

/-- Core-supported relative diffeomorphisms whose support is displayed by a model-coordinate ball
contained in the actual handle interior. -/
def oneHandleCoreSupportedInSomeInteriorModelCoordinateFourBall (rho : ℝ) :
    Set (OneHandleCoreSupportedRelativeDiff rho) :=
  {f | ∃ B : ModelCoordinateFourBall oneHandlePieceModel OneHandlePiece,
    B.domain ≤ oneHandlePieceInterior ∧ DiffeomorphSupportedIn f.1.1 B.carrier}

/-- Smooth core extension sends the exact source selected set into the ordinary target selected
set of coordinate-ball-supported empty-relative sphere diffeomorphisms. -/
theorem smoothOneHandleCoreExtensionRelativeHom_mapsTo_coordinateBallSupported
    {rho : ℝ} (hrho : rho < 1) :
    MapsTo (smoothOneHandleCoreExtensionRelativeHom hrho)
      (oneHandleCoreSupportedInSomeInteriorModelCoordinateFourBall rho)
      (relativeDiffSupportedInSomeCoordinateFourBall (∅ : Set (Sphere 4))) := by
  intro f hf
  obtain ⟨B, hB, hfB⟩ := hf
  exact smoothOneHandleCoreExtensionRelativeHom_mem_coordinateBallSupported
    hrho B hB f hfB

end SplittingSpheres
