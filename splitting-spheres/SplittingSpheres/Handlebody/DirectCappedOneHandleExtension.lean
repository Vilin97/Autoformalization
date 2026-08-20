/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CappedOneHandleExtension
public import SplittingSpheres.Handlebody.SphereHandleSmoothness

/-!
# Direct-coordinate extension of a one-handle diffeomorphism to the four-sphere

The direct handle decomposition gives explicit smooth face maps from `S¹ × B³` and
`D² × S²` into the literal unit four-sphere.  Conjugating the topological cap extension by
that direct homeomorphism produces a self-homeomorphism whose action on both coordinate faces is
literal: it applies the original diffeomorphism on the one-handle face and is the identity on the
cap face.

The face parameterizations are smooth, but this file still claims only a topological global
extension.  Smoothness across the common boundary needs an additional collar-fixed hypothesis
and a smooth gluing argument.
-/

@[expose] public section

noncomputable section

open Function Set

namespace SplittingSpheres

/-- Conjugate the capped extension by the direct-coordinate homeomorphism with the literal
four-sphere. -/
def directCappedOneHandleExtensionSphere (f : OneHandleBoundaryRelativeDiff) :
    Sphere 4 ≃ₜ Sphere 4 :=
  (directCappedOneHandleHomeomorphSphere.symm.trans (cappedOneHandleExtension f)).trans
    directCappedOneHandleHomeomorphSphere

/-- Exact action on the directly parameterized one-handle face. -/
@[simp]
theorem directCappedOneHandleExtensionSphere_oneHandle
    (f : OneHandleBoundaryRelativeDiff) (x : OneHandlePiece) :
    directCappedOneHandleExtensionSphere f (oneHandleSphereMap x) =
      oneHandleSphereMap (f.1 x) := by
  rw [← directCappedOneHandleHomeomorphSphere_inl x,
    ← directCappedOneHandleHomeomorphSphere_inl (f.1 x)]
  change directCappedOneHandleHomeomorphSphere
      (cappedOneHandleExtension f
        (directCappedOneHandleHomeomorphSphere.symm
          (directCappedOneHandleHomeomorphSphere (cappedOneHandleInl x)))) = _
  rw [directCappedOneHandleHomeomorphSphere.symm_apply_apply,
    cappedOneHandleExtension_inl,
    directCappedOneHandleHomeomorphSphere_inl]

/-- Exact action on the directly parameterized cap face. -/
@[simp]
theorem directCappedOneHandleExtensionSphere_cap
    (f : OneHandleBoundaryRelativeDiff) (x : CapPiece) :
    directCappedOneHandleExtensionSphere f (sphereHandleCapMap x) = sphereHandleCapMap x := by
  rw [← directCappedOneHandleHomeomorphSphere_inr x]
  change directCappedOneHandleHomeomorphSphere
      (cappedOneHandleExtension f
        (directCappedOneHandleHomeomorphSphere.symm
          (directCappedOneHandleHomeomorphSphere (cappedOneHandleInr x)))) = _
  rw [directCappedOneHandleHomeomorphSphere.symm_apply_apply,
    cappedOneHandleExtension_inr,
    directCappedOneHandleHomeomorphSphere_inr]

/-- The direct-coordinate extension fixes the entire cap-face image. -/
theorem directCappedOneHandleExtensionSphere_eq_of_mem_cap_range
    (f : OneHandleBoundaryRelativeDiff) {q : Sphere 4}
    (hq : q ∈ range sphereHandleCapMap) :
    directCappedOneHandleExtensionSphere f q = q := by
  obtain ⟨x, rfl⟩ := hq
  exact directCappedOneHandleExtensionSphere_cap f x

/-- The direct-coordinate extension of the identity is the identity. -/
@[simp]
theorem directCappedOneHandleExtensionSphere_one :
    directCappedOneHandleExtensionSphere (1 : OneHandleBoundaryRelativeDiff) = 1 := by
  ext q
  simp [directCappedOneHandleExtensionSphere]

/-- Direct-coordinate extension respects the composition convention. -/
@[simp]
theorem directCappedOneHandleExtensionSphere_mul
    (f g : OneHandleBoundaryRelativeDiff) :
    directCappedOneHandleExtensionSphere (f * g) =
      directCappedOneHandleExtensionSphere f * directCappedOneHandleExtensionSphere g := by
  apply Homeomorph.ext
  intro q
  change directCappedOneHandleHomeomorphSphere
      (cappedOneHandleExtension (f * g)
        (directCappedOneHandleHomeomorphSphere.symm q)) =
    directCappedOneHandleHomeomorphSphere
      (cappedOneHandleExtension f
        (directCappedOneHandleHomeomorphSphere.symm
          (directCappedOneHandleHomeomorphSphere
            (cappedOneHandleExtension g
              (directCappedOneHandleHomeomorphSphere.symm q)))))
  rw [directCappedOneHandleHomeomorphSphere.symm_apply_apply,
    cappedOneHandleExtension_mul, Homeomorph.mul_apply]

/-- Direct-coordinate extension as a group homomorphism to homeomorphisms of the literal
four-sphere. -/
def directCappedOneHandleExtensionSphereHom :
    OneHandleBoundaryRelativeDiff →* (Sphere 4 ≃ₜ Sphere 4) where
  toFun := directCappedOneHandleExtensionSphere
  map_one' := directCappedOneHandleExtensionSphere_one
  map_mul' := directCappedOneHandleExtensionSphere_mul

/-- The direct-coordinate extension homomorphism is faithful. -/
theorem directCappedOneHandleExtensionSphereHom_injective :
    Injective directCappedOneHandleExtensionSphereHom := by
  intro f g h
  change directCappedOneHandleExtensionSphere f =
    directCappedOneHandleExtensionSphere g at h
  apply Subtype.ext
  apply Diffeomorph.ext
  intro x
  apply oneHandleSphereMap_injective
  have hx := congrArg (fun e : Sphere 4 ≃ₜ Sphere 4 ↦ e (oneHandleSphereMap x)) h
  simpa only [directCappedOneHandleExtensionSphere_oneHandle] using hx

end SplittingSpheres
