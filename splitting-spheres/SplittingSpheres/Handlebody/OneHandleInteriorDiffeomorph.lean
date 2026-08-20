/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.SmoothCoreExtension

/-!
# The smooth interior of the compact one-handle

The actual model interior of the compact piece `S¹ × B³` is the product of `S¹` with the open
unit three-ball.  This file identifies those two literal open manifolds by a `C∞`
diffeomorphism.  Composing with the direct interior coordinates gives a diffeomorphism from the
compact handle's model interior onto the open one-handle region in the literal four-sphere.

The target below is an open subtype of the existing manifold-with-corners.  No smooth structure
on its boundary subtype, and no boundary-flattening theorem, is asserted.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SplittingSpheres

/-- The genuine model interior of the compact one-handle, bundled as an open subtype. -/
def oneHandlePieceInterior : Opens OneHandlePiece :=
  ⟨oneHandlePieceModel.interior OneHandlePiece,
    oneHandlePieceModel.isOpen_interior (n := ∞) (by simp)⟩

/-- The carrier of the bundled open subtype is literally the model interior. -/
@[simp]
theorem oneHandlePieceInterior_coe :
    (oneHandlePieceInterior : Set OneHandlePiece) =
      oneHandlePieceModel.interior OneHandlePiece :=
  rfl

/-- Exact ambient-coordinate description of the bundled model interior. -/
theorem oneHandlePieceInterior_eq :
    (oneHandlePieceInterior : Set OneHandlePiece) =
      (univ : Set (Sphere 1)) ×ˢ
        (Subtype.val ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  oneHandlePieceModel_interior_eq

/-- Membership in the one-handle interior is exactly strict inequality for the closed-ball
coordinate's ambient norm. -/
@[simp]
theorem mem_oneHandlePieceInterior {x : OneHandlePiece} :
    x ∈ oneHandlePieceInterior ↔ ‖x.2.1‖ < 1 := by
  change x ∈ oneHandlePieceModel.interior OneHandlePiece ↔ _
  rw [oneHandlePieceModel_interior_eq]
  simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage,
    mem_ball_zero_iff]

/-- Include `S¹ ×` the open unit ball into the actual model interior of the compact handle. -/
def oneHandleInteriorForward
    (p : Sphere 1 × SphereHandleOpenUnitBall) : oneHandlePieceInterior :=
  ⟨sphereHandleInteriorProductInclusion p, by
    rw [mem_oneHandlePieceInterior]
    exact mem_ball_zero_iff.mp p.2.2⟩

@[simp]
theorem oneHandleInteriorForward_coe
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    (oneHandleInteriorForward p : OneHandlePiece) =
      sphereHandleInteriorProductInclusion p :=
  rfl

@[simp]
theorem oneHandleInteriorForward_fst
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    (oneHandleInteriorForward p).1.1 = p.1 :=
  rfl

@[simp]
theorem oneHandleInteriorForward_snd_val
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    (oneHandleInteriorForward p).1.2.1 = p.2.1 :=
  rfl

/-- Extract the circle and ambient open-ball coordinates from a point of the model interior. -/
def oneHandleInteriorInverse
    (x : oneHandlePieceInterior) : Sphere 1 × SphereHandleOpenUnitBall :=
  (x.1.1, ⟨x.1.2.1, mem_ball_zero_iff.mpr (mem_oneHandlePieceInterior.mp x.2)⟩)

@[simp]
theorem oneHandleInteriorInverse_fst (x : oneHandlePieceInterior) :
    (oneHandleInteriorInverse x).1 = x.1.1 :=
  rfl

@[simp]
theorem oneHandleInteriorInverse_snd_val (x : oneHandlePieceInterior) :
    (oneHandleInteriorInverse x).2.1 = x.1.2.1 :=
  rfl

/-- Extracting coordinates after inclusion is the identity. -/
theorem oneHandleInteriorInverse_forward
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    oneHandleInteriorInverse (oneHandleInteriorForward p) = p := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

/-- Inclusion after extracting coordinates is the identity on the actual model interior. -/
theorem oneHandleInteriorForward_inverse (x : oneHandlePieceInterior) :
    oneHandleInteriorForward (oneHandleInteriorInverse x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

/-- The exact equivalence underlying the product description of the one-handle interior. -/
def oneHandleInteriorEquiv :
    (Sphere 1 × SphereHandleOpenUnitBall) ≃ oneHandlePieceInterior where
  toFun := oneHandleInteriorForward
  invFun := oneHandleInteriorInverse
  left_inv := oneHandleInteriorInverse_forward
  right_inv := oneHandleInteriorForward_inverse

@[simp]
theorem oneHandleInteriorEquiv_apply
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    oneHandleInteriorEquiv p = oneHandleInteriorForward p :=
  rfl

@[simp]
theorem oneHandleInteriorEquiv_symm_apply (x : oneHandlePieceInterior) :
    oneHandleInteriorEquiv.symm x = oneHandleInteriorInverse x :=
  rfl

/-- Inclusion into the actual model interior is smooth. -/
theorem contMDiff_oneHandleInteriorForward :
    ContMDiff sphereHandleInteriorProductModel oneHandlePieceModel ∞
      oneHandleInteriorForward := by
  apply (ContMDiff.subtypeVal_comp_iff oneHandlePieceInterior
    oneHandleInteriorForward).mp
  exact contMDiff_sphereHandleInteriorProductInclusion

/-- The ambient ball coordinate extracted from the actual one-handle interior is smooth. -/
theorem contMDiff_oneHandleInteriorInverse_ballVal :
    ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun x : oneHandlePieceInterior ↦ x.1.2.1) :=
  (contMDiff_closedUnitBall_inclusion (EuclideanSpace ℝ (Fin 3))).comp
    (contMDiff_snd.comp contMDiff_subtype_val)

/-- Coordinate extraction from the actual model interior is smooth. -/
theorem contMDiff_oneHandleInteriorInverse :
    ContMDiff oneHandlePieceModel sphereHandleInteriorProductModel ∞
      oneHandleInteriorInverse := by
  have hfirst : ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
      (fun x : oneHandlePieceInterior ↦ x.1.1) :=
    contMDiff_fst.comp contMDiff_subtype_val
  have hsecond : ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun x : oneHandlePieceInterior ↦
        (oneHandleInteriorInverse x).2) := by
    apply (ContMDiff.subtypeVal_comp_iff sphereHandleOpenUnitBall _).mp
    exact contMDiff_oneHandleInteriorInverse_ballVal
  exact (hfirst.prodMk hsecond).congr fun _ ↦ rfl

/-- The product of the circle with the open unit three-ball is genuinely `C∞`-diffeomorphic to
the actual model interior of the compact one-handle. -/
def oneHandleInteriorDiffeomorph :
    (Sphere 1 × SphereHandleOpenUnitBall) ≃ₘ^∞⟮
      sphereHandleInteriorProductModel, oneHandlePieceModel⟯ oneHandlePieceInterior where
  toEquiv := oneHandleInteriorEquiv
  contMDiff_toFun := contMDiff_oneHandleInteriorForward
  contMDiff_invFun := contMDiff_oneHandleInteriorInverse

@[simp]
theorem oneHandleInteriorDiffeomorph_apply
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    oneHandleInteriorDiffeomorph p = oneHandleInteriorForward p :=
  rfl

@[simp]
theorem oneHandleInteriorDiffeomorph_apply_coe
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    (oneHandleInteriorDiffeomorph p : OneHandlePiece) =
      sphereHandleInteriorProductInclusion p :=
  rfl

@[simp]
theorem oneHandleInteriorDiffeomorph_symm_apply
    (x : oneHandlePieceInterior) :
    oneHandleInteriorDiffeomorph.symm x = oneHandleInteriorInverse x :=
  rfl

/-- The actual compact-handle interior, in its inherited open-submanifold structure, is
`C∞`-diffeomorphic to the literal open one-handle region in `S⁴`. -/
def oneHandleInteriorToSphereRegionDiffeomorph :
    oneHandlePieceInterior ≃ₘ^∞⟮
      oneHandlePieceModel,
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯ SphereHandleOneRegion :=
  oneHandleInteriorDiffeomorph.symm.trans sphereHandleInteriorDiffeomorph

@[simp]
theorem oneHandleInteriorToSphereRegionDiffeomorph_apply
    (x : oneHandlePieceInterior) :
    oneHandleInteriorToSphereRegionDiffeomorph x =
      sphereHandleInteriorDiffeomorph (oneHandleInteriorInverse x) :=
  rfl

/-- After forgetting both open-subtype witnesses, the interior-to-sphere diffeomorphism is exactly
the direct one-handle coordinate map. -/
@[simp]
theorem oneHandleInteriorToSphereRegionDiffeomorph_apply_coe
    (x : oneHandlePieceInterior) :
    ((oneHandleInteriorToSphereRegionDiffeomorph x : SphereHandleOneRegion) : Sphere 4) =
      oneHandleSphereMap x.1 := by
  rw [oneHandleInteriorToSphereRegionDiffeomorph_apply,
    sphereHandleInteriorDiffeomorph_apply_coe]
  congr 1

/-- The inverse sphere-region coordinates land at the corresponding literal point of the compact
handle interior. -/
@[simp]
theorem oneHandleInteriorToSphereRegionDiffeomorph_symm_apply
    (q : SphereHandleOneRegion) :
    oneHandleInteriorToSphereRegionDiffeomorph.symm q =
      oneHandleInteriorDiffeomorph
        (sphereHandleInteriorDiffeomorph.symm q) :=
  rfl

@[simp]
theorem oneHandleInteriorToSphereRegionDiffeomorph_symm_apply_coe
    (q : SphereHandleOneRegion) :
    (oneHandleInteriorToSphereRegionDiffeomorph.symm q : OneHandlePiece) =
      sphereHandleInteriorProductInclusion
        (sphereHandleInteriorDiffeomorph.symm q) :=
  rfl

/-- In product coordinates, the composite interior-to-sphere diffeomorphism is literally the
previously constructed direct interior diffeomorphism. -/
@[simp]
theorem oneHandleInteriorToSphereRegionDiffeomorph_forward
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    oneHandleInteriorToSphereRegionDiffeomorph
        (oneHandleInteriorDiffeomorph p) =
      sphereHandleInteriorDiffeomorph p := by
  change sphereHandleInteriorDiffeomorph
      (oneHandleInteriorDiffeomorph.symm (oneHandleInteriorDiffeomorph p)) = _
  rw [Diffeomorph.symm_apply_apply]

/-- The inverse composite recovers the actual handle-interior point corresponding to explicit
product coordinates. -/
@[simp]
theorem oneHandleInteriorToSphereRegionDiffeomorph_symm_forward
    (p : Sphere 1 × SphereHandleOpenUnitBall) :
    oneHandleInteriorToSphereRegionDiffeomorph.symm
        (sphereHandleInteriorDiffeomorph p) =
      oneHandleInteriorDiffeomorph p := by
  exact oneHandleInteriorToSphereRegionDiffeomorph.symm_apply_apply
    (oneHandleInteriorDiffeomorph p)

end SplittingSpheres
