/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutCongr
public import SplittingSpheres.Handlebody.BoundaryAttachment

/-!
# Partial sphere spins of spaces with a parametrized outer circle

Given a space `P` and a continuous parametrized circle `outer : S¹ → P`, its partial
`S²`-spin is the adjunction space

`(S¹ × B³) ∪_(S¹ × S²) (P × S²)`.

The boundary point `(u, s)` is attached to `(outer u, s)`.  This is precisely the topological
pushout shape occurring in the explicit cyclic cover of the unlink exterior.  We also prove
functoriality under homeomorphisms preserving the parametrized outer circle.

This definition makes no manifold, connected-sum, or smooth-gluing assertion.  Those are
separate geometric theorems.
-/

@[expose] public section

noncomputable section

open Topology

namespace SplittingSpheres

variable {P Q R : Type}
variable [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace R]

/-- Attach the common `S¹ × S²` boundary to `P × S²` using a parametrized outer circle in
`P`. -/
def partialSphereSpinBoundaryInclusion (outer : C(Sphere 1, P)) :
    C(OneHandleCapBoundary, P × Sphere 2) where
  toFun x := (outer x.1, x.2)
  continuous_toFun := (outer.continuous.comp continuous_fst).prodMk continuous_snd

@[simp]
theorem partialSphereSpinBoundaryInclusion_apply
    (outer : C(Sphere 1, P)) (x : OneHandleCapBoundary) :
    partialSphereSpinBoundaryInclusion outer x = (outer x.1, x.2) :=
  rfl

/-- The partial `S²`-spin of `P` along its parametrized outer circle. -/
abbrev PartialSphereSpin (outer : C(Sphere 1, P)) : Type :=
  TopologicalPushout oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion outer)

/-- The one-handle coprojection into a partial sphere spin. -/
abbrev partialSphereSpinInl (outer : C(Sphere 1, P)) :
    C(OneHandlePiece, PartialSphereSpin outer) :=
  topologicalPushoutInl oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion outer)

/-- The spun planar-piece coprojection into a partial sphere spin. -/
abbrev partialSphereSpinInr (outer : C(Sphere 1, P)) :
    C(P × Sphere 2, PartialSphereSpin outer) :=
  topologicalPushoutInr oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion outer)

theorem partialSphereSpin_condition
    (outer : C(Sphere 1, P)) (x : OneHandleCapBoundary) :
    partialSphereSpinInl outer (oneHandleBoundaryInclusion x) =
      partialSphereSpinInr outer (outer x.1, x.2) :=
  topologicalPushout_condition oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion outer) x

/-- A partial sphere spin of a compact planar factor is compact. -/
instance partialSphereSpinCompactSpace
    (outer : C(Sphere 1, P)) [CompactSpace P] :
    CompactSpace (PartialSphereSpin outer) :=
  topologicalPushoutCompactSpace oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion outer)

/-- A homeomorphism carrying one parametrized outer circle to another induces a homeomorphism
of their partial sphere spins. -/
def partialSphereSpinCongr
    (outer : C(Sphere 1, P)) (outer' : C(Sphere 1, Q))
    (e : P ≃ₜ Q) (he : ∀ u, e (outer u) = outer' u) :
    PartialSphereSpin outer ≃ₜ PartialSphereSpin outer' :=
  topologicalPushoutCongr
    oneHandleBoundaryInclusion (partialSphereSpinBoundaryInclusion outer)
    oneHandleBoundaryInclusion (partialSphereSpinBoundaryInclusion outer')
    (Homeomorph.refl OneHandleCapBoundary) (Homeomorph.refl OneHandlePiece)
    (e.prodCongr (Homeomorph.refl (Sphere 2)))
    (fun _ ↦ rfl) (fun x ↦ Prod.ext (he x.1) rfl)

@[simp]
theorem partialSphereSpinCongr_inl
    (outer : C(Sphere 1, P)) (outer' : C(Sphere 1, Q))
    (e : P ≃ₜ Q) (he : ∀ u, e (outer u) = outer' u) (x : OneHandlePiece) :
    partialSphereSpinCongr outer outer' e he (partialSphereSpinInl outer x) =
      partialSphereSpinInl outer' x :=
  topologicalPushoutCongr_inl
    oneHandleBoundaryInclusion (partialSphereSpinBoundaryInclusion outer)
    oneHandleBoundaryInclusion (partialSphereSpinBoundaryInclusion outer')
    (Homeomorph.refl OneHandleCapBoundary) (Homeomorph.refl OneHandlePiece)
    (e.prodCongr (Homeomorph.refl (Sphere 2)))
    (fun _ ↦ rfl) (fun x ↦ Prod.ext (he x.1) rfl) x

@[simp]
theorem partialSphereSpinCongr_inr
    (outer : C(Sphere 1, P)) (outer' : C(Sphere 1, Q))
    (e : P ≃ₜ Q) (he : ∀ u, e (outer u) = outer' u) (x : P × Sphere 2) :
    partialSphereSpinCongr outer outer' e he (partialSphereSpinInr outer x) =
      partialSphereSpinInr outer' (e x.1, x.2) :=
  topologicalPushoutCongr_inr
    oneHandleBoundaryInclusion (partialSphereSpinBoundaryInclusion outer)
    oneHandleBoundaryInclusion (partialSphereSpinBoundaryInclusion outer')
    (Homeomorph.refl OneHandleCapBoundary) (Homeomorph.refl OneHandlePiece)
    (e.prodCongr (Homeomorph.refl (Sphere 2)))
    (fun _ ↦ rfl) (fun x ↦ Prod.ext (he x.1) rfl) x

/-- Partial-spin congruence is reflexive. -/
theorem partialSphereSpinCongr_refl
    (outer : C(Sphere 1, P)) :
    partialSphereSpinCongr outer outer (Homeomorph.refl P) (fun _ ↦ rfl) =
      Homeomorph.refl (PartialSphereSpin outer) := by
  ext z
  rcases topologicalPushout_jointly_surjective
      oneHandleBoundaryInclusion (partialSphereSpinBoundaryInclusion outer) z with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact partialSphereSpinCongr_inl outer outer (Homeomorph.refl P)
      (fun _ ↦ rfl) x
  · exact partialSphereSpinCongr_inr outer outer (Homeomorph.refl P)
      (fun _ ↦ rfl) y

/-- Successive outer-circle-preserving homeomorphisms induce the successive partial-spin
homeomorphism. -/
theorem partialSphereSpinCongr_trans
    (outer : C(Sphere 1, P)) (outer' : C(Sphere 1, Q)) (outer'' : C(Sphere 1, R))
    (e : P ≃ₜ Q) (f : Q ≃ₜ R)
    (he : ∀ u, e (outer u) = outer' u)
    (hf : ∀ u, f (outer' u) = outer'' u) :
    (partialSphereSpinCongr outer outer' e he).trans
        (partialSphereSpinCongr outer' outer'' f hf) =
      partialSphereSpinCongr outer outer'' (e.trans f)
        (fun u ↦ by rw [Homeomorph.trans_apply, he, hf]) := by
  ext z
  rcases topologicalPushout_jointly_surjective
      oneHandleBoundaryInclusion (partialSphereSpinBoundaryInclusion outer) z with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · simp
  · simp

end SplittingSpheres
