/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.CompactOpen
public import SplittingSpheres.Handlebody.PartialSphereSpin

/-!
# Capping a partial sphere spin

This file proves the point-set associativity behind filling a boundary circle of the planar
factor of a partial `S²`-spin.  If `P` is filled by a space `D` along a parametrized circle,
then spinning the filled planar factor is homeomorphic to first spinning `P` and subsequently
attaching `D × S²` along the spun circle.

The construction is entirely in topological pushouts.  In particular, it asserts no manifold,
smooth-gluing, connected-sum, disk-classification, or cap-classification result.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

variable {A X Y Z : Type}
variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z]

/-! ## Products of topological pushouts -/

/-- Descend compatible maps from `X × S²` and `Y × S²` through
`(X ∪_A Y) × S²`.

Continuity is obtained honestly by currying into the compact-open mapping space, applying the
pushout universal property there, and uncurrying.  The final step uses local compactness of the
literal sphere factor. -/
def partialSphereSpinFillingProdDesc
    (f : C(A, X)) (g : C(A, Y))
    (p : C(X × Sphere 2, Z)) (q : C(Y × Sphere 2, Z))
    (h : ∀ a s, p (f a, s) = q (g a, s)) :
    C(TopologicalPushout f g × Sphere 2, Z) :=
  ContinuousMap.uncurry <|
    topologicalPushoutDesc f g p.curry q.curry (fun a ↦ by
      ext s
      exact h a s)

@[simp]
theorem partialSphereSpinFillingProdDesc_inl
    (f : C(A, X)) (g : C(A, Y))
    (p : C(X × Sphere 2, Z)) (q : C(Y × Sphere 2, Z))
    (h : ∀ a s, p (f a, s) = q (g a, s))
    (x : X) (s : Sphere 2) :
    partialSphereSpinFillingProdDesc f g p q h
        (topologicalPushoutInl f g x, s) = p (x, s) := by
  simp [partialSphereSpinFillingProdDesc]

@[simp]
theorem partialSphereSpinFillingProdDesc_inr
    (f : C(A, X)) (g : C(A, Y))
    (p : C(X × Sphere 2, Z)) (q : C(Y × Sphere 2, Z))
    (h : ∀ a s, p (f a, s) = q (g a, s))
    (y : Y) (s : Sphere 2) :
    partialSphereSpinFillingProdDesc f g p q h
        (topologicalPushoutInr f g y, s) = q (y, s) := by
  simp [partialSphereSpinFillingProdDesc]

/-! ## The two orders of attachment -/

variable {P D : Type}
variable [TopologicalSpace P] [TopologicalSpace D]

/-- Fill `P` by `D` along two parametrized copies of the same circle. -/
abbrev PartialSphereSpinPlanarFilling
    (inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) : Type :=
  TopologicalPushout inner diskBoundary

/-- The old planar piece inside its filling. -/
abbrev partialSphereSpinPlanarFillingInl
    (inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(P, PartialSphereSpinPlanarFilling inner diskBoundary) :=
  topologicalPushoutInl inner diskBoundary

/-- The filling piece inside the filled planar space. -/
abbrev partialSphereSpinPlanarFillingInr
    (inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(D, PartialSphereSpinPlanarFilling inner diskBoundary) :=
  topologicalPushoutInr inner diskBoundary

/-- The outer circle in the filled planar space, retained from the old planar piece. -/
def partialSphereSpinFilledOuter
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(Sphere 1, PartialSphereSpinPlanarFilling inner diskBoundary) :=
  (partialSphereSpinPlanarFillingInl inner diskBoundary).comp outer

@[simp]
theorem partialSphereSpinFilledOuter_apply
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (u : Sphere 1) :
    partialSphereSpinFilledOuter outer inner diskBoundary u =
      partialSphereSpinPlanarFillingInl inner diskBoundary (outer u) :=
  rfl

/-- First fill the planar factor and then form its partial sphere spin. -/
abbrev PartialSphereSpinFilledFirst
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) : Type :=
  PartialSphereSpin (partialSphereSpinFilledOuter outer inner diskBoundary)

/-- The spun inner circle in the partial sphere spin of the unfilled planar factor. -/
def partialSphereSpinInnerBoundaryInclusion
    (outer inner : C(Sphere 1, P)) :
    C(OneHandleCapBoundary, PartialSphereSpin outer) where
  toFun x := partialSphereSpinInr outer (inner x.1, x.2)
  continuous_toFun := (partialSphereSpinInr outer).continuous.comp <|
    (inner.continuous.comp continuous_fst).prodMk continuous_snd

@[simp]
theorem partialSphereSpinInnerBoundaryInclusion_apply
    (outer inner : C(Sphere 1, P)) (x : OneHandleCapBoundary) :
    partialSphereSpinInnerBoundaryInclusion outer inner x =
      partialSphereSpinInr outer (inner x.1, x.2) :=
  rfl

/-- The product of the planar filling-boundary map with the identity of `S²`. -/
def partialSphereSpinDiskBoundaryInclusion
    (diskBoundary : C(Sphere 1, D)) :
    C(OneHandleCapBoundary, D × Sphere 2) where
  toFun x := (diskBoundary x.1, x.2)
  continuous_toFun :=
    (diskBoundary.continuous.comp continuous_fst).prodMk continuous_snd

@[simp]
theorem partialSphereSpinDiskBoundaryInclusion_apply
    (diskBoundary : C(Sphere 1, D)) (x : OneHandleCapBoundary) :
    partialSphereSpinDiskBoundaryInclusion diskBoundary x =
      (diskBoundary x.1, x.2) :=
  rfl

/-- First form the partial spin of `P`, then attach `D × S²` along the spun inner circle. -/
abbrev PartialSphereSpinCappedSecond
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) : Type :=
  TopologicalPushout
    (partialSphereSpinInnerBoundaryInclusion outer inner)
    (partialSphereSpinDiskBoundaryInclusion diskBoundary)

/-- The partial spin of the unfilled piece inside the second-order attachment. -/
abbrev partialSphereSpinCappedSecondInl
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(PartialSphereSpin outer,
      PartialSphereSpinCappedSecond outer inner diskBoundary) :=
  topologicalPushoutInl
    (partialSphereSpinInnerBoundaryInclusion outer inner)
    (partialSphereSpinDiskBoundaryInclusion diskBoundary)

/-- The product filling piece inside the second-order attachment. -/
abbrev partialSphereSpinCappedSecondInr
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(D × Sphere 2,
      PartialSphereSpinCappedSecond outer inner diskBoundary) :=
  topologicalPushoutInr
    (partialSphereSpinInnerBoundaryInclusion outer inner)
    (partialSphereSpinDiskBoundaryInclusion diskBoundary)

/-! ## The forward map -/

/-- Map the one-handle piece to the second-order attachment. -/
def partialSphereSpinFillingForwardOneHandle
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(OneHandlePiece, PartialSphereSpinCappedSecond outer inner diskBoundary) :=
  (partialSphereSpinCappedSecondInl outer inner diskBoundary).comp
    (partialSphereSpinInl outer)

/-- Map the filled planar product to the second-order attachment, descending separately from
`P × S²` and `D × S²`. -/
def partialSphereSpinFillingForwardPlanar
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(PartialSphereSpinPlanarFilling inner diskBoundary × Sphere 2,
      PartialSphereSpinCappedSecond outer inner diskBoundary) :=
  partialSphereSpinFillingProdDesc inner diskBoundary
    ((partialSphereSpinCappedSecondInl outer inner diskBoundary).comp
      (partialSphereSpinInr outer))
    (partialSphereSpinCappedSecondInr outer inner diskBoundary)
    (fun a s ↦ topologicalPushout_condition
      (partialSphereSpinInnerBoundaryInclusion outer inner)
      (partialSphereSpinDiskBoundaryInclusion diskBoundary) (a, s))

@[simp]
theorem partialSphereSpinFillingForwardPlanar_inl
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinFillingForwardPlanar outer inner diskBoundary
        (partialSphereSpinPlanarFillingInl inner diskBoundary p, s) =
      partialSphereSpinCappedSecondInl outer inner diskBoundary
        (partialSphereSpinInr outer (p, s)) := by
  unfold partialSphereSpinFillingForwardPlanar
  apply partialSphereSpinFillingProdDesc_inl

@[simp]
theorem partialSphereSpinFillingForwardPlanar_inr
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinFillingForwardPlanar outer inner diskBoundary
        (partialSphereSpinPlanarFillingInr inner diskBoundary d, s) =
      partialSphereSpinCappedSecondInr outer inner diskBoundary (d, s) := by
  unfold partialSphereSpinFillingForwardPlanar
  apply partialSphereSpinFillingProdDesc_inr

theorem partialSphereSpinFillingForward_compatibility
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (x : OneHandleCapBoundary) :
    partialSphereSpinFillingForwardOneHandle outer inner diskBoundary
        (oneHandleBoundaryInclusion x) =
      partialSphereSpinFillingForwardPlanar outer inner diskBoundary
        (partialSphereSpinBoundaryInclusion
          (partialSphereSpinFilledOuter outer inner diskBoundary) x) := by
  change partialSphereSpinCappedSecondInl outer inner diskBoundary
      (partialSphereSpinInl outer (oneHandleBoundaryInclusion x)) = _
  rw [partialSphereSpin_condition]
  simp [partialSphereSpinBoundaryInclusion_apply]

/-- The continuous comparison from “fill, then spin” to “spin, then cap.” -/
def partialSphereSpinFillingForward
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(PartialSphereSpinFilledFirst outer inner diskBoundary,
      PartialSphereSpinCappedSecond outer inner diskBoundary) :=
  topologicalPushoutDesc oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion
      (partialSphereSpinFilledOuter outer inner diskBoundary))
    (partialSphereSpinFillingForwardOneHandle outer inner diskBoundary)
    (partialSphereSpinFillingForwardPlanar outer inner diskBoundary)
    (partialSphereSpinFillingForward_compatibility outer inner diskBoundary)

@[simp]
theorem partialSphereSpinFillingForward_oneHandle
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (x : OneHandlePiece) :
    partialSphereSpinFillingForward outer inner diskBoundary
        (partialSphereSpinInl
          (partialSphereSpinFilledOuter outer inner diskBoundary) x) =
      partialSphereSpinCappedSecondInl outer inner diskBoundary
        (partialSphereSpinInl outer x) := by
  simp [partialSphereSpinFillingForward,
    partialSphereSpinFillingForwardOneHandle]

@[simp]
theorem partialSphereSpinFillingForward_planar
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinFillingForward outer inner diskBoundary
        (partialSphereSpinInr
          (partialSphereSpinFilledOuter outer inner diskBoundary)
          (partialSphereSpinPlanarFillingInl inner diskBoundary p, s)) =
      partialSphereSpinCappedSecondInl outer inner diskBoundary
        (partialSphereSpinInr outer (p, s)) := by
  simp [partialSphereSpinFillingForward]

@[simp]
theorem partialSphereSpinFillingForward_filling
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinFillingForward outer inner diskBoundary
        (partialSphereSpinInr
          (partialSphereSpinFilledOuter outer inner diskBoundary)
          (partialSphereSpinPlanarFillingInr inner diskBoundary d, s)) =
      partialSphereSpinCappedSecondInr outer inner diskBoundary (d, s) := by
  simp [partialSphereSpinFillingForward]

/-! ## The inverse map -/

/-- Include the unfilled partial spin into the partial spin of the filled planar factor. -/
def partialSphereSpinFillingInverseSpun
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(PartialSphereSpin outer,
      PartialSphereSpinFilledFirst outer inner diskBoundary) :=
  topologicalPushoutDesc oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion outer)
    (partialSphereSpinInl
      (partialSphereSpinFilledOuter outer inner diskBoundary))
    ⟨fun x ↦ partialSphereSpinInr
        (partialSphereSpinFilledOuter outer inner diskBoundary)
        (partialSphereSpinPlanarFillingInl inner diskBoundary x.1, x.2),
      ((partialSphereSpinInr
        (partialSphereSpinFilledOuter outer inner diskBoundary)).continuous.comp <|
        (((partialSphereSpinPlanarFillingInl inner diskBoundary).continuous.comp
          continuous_fst).prodMk continuous_snd))⟩
    (fun x ↦ by
      change partialSphereSpinInl
          (partialSphereSpinFilledOuter outer inner diskBoundary)
          (oneHandleBoundaryInclusion x) =
        partialSphereSpinInr
          (partialSphereSpinFilledOuter outer inner diskBoundary)
          (partialSphereSpinFilledOuter outer inner diskBoundary x.1, x.2)
      exact partialSphereSpin_condition
        (partialSphereSpinFilledOuter outer inner diskBoundary) x)

@[simp]
theorem partialSphereSpinFillingInverseSpun_oneHandle
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (x : OneHandlePiece) :
    partialSphereSpinFillingInverseSpun outer inner diskBoundary
        (partialSphereSpinInl outer x) =
      partialSphereSpinInl
        (partialSphereSpinFilledOuter outer inner diskBoundary) x := by
  simp [partialSphereSpinFillingInverseSpun]

@[simp]
theorem partialSphereSpinFillingInverseSpun_planar
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinFillingInverseSpun outer inner diskBoundary
        (partialSphereSpinInr outer (p, s)) =
      partialSphereSpinInr
        (partialSphereSpinFilledOuter outer inner diskBoundary)
        (partialSphereSpinPlanarFillingInl inner diskBoundary p, s) := by
  simp [partialSphereSpinFillingInverseSpun]

/-- Include the product filling piece into the partial spin of the filled planar factor. -/
def partialSphereSpinFillingInverseCap
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(D × Sphere 2, PartialSphereSpinFilledFirst outer inner diskBoundary) where
  toFun x := partialSphereSpinInr
    (partialSphereSpinFilledOuter outer inner diskBoundary)
    (partialSphereSpinPlanarFillingInr inner diskBoundary x.1, x.2)
  continuous_toFun :=
    (partialSphereSpinInr
      (partialSphereSpinFilledOuter outer inner diskBoundary)).continuous.comp <|
      (((partialSphereSpinPlanarFillingInr inner diskBoundary).continuous.comp
        continuous_fst).prodMk continuous_snd)

@[simp]
theorem partialSphereSpinFillingInverseCap_apply
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinFillingInverseCap outer inner diskBoundary (d, s) =
      partialSphereSpinInr
        (partialSphereSpinFilledOuter outer inner diskBoundary)
        (partialSphereSpinPlanarFillingInr inner diskBoundary d, s) :=
  rfl

theorem partialSphereSpinFillingInverse_compatibility
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (x : OneHandleCapBoundary) :
    partialSphereSpinFillingInverseSpun outer inner diskBoundary
        (partialSphereSpinInnerBoundaryInclusion outer inner x) =
      partialSphereSpinFillingInverseCap outer inner diskBoundary
        (partialSphereSpinDiskBoundaryInclusion diskBoundary x) := by
  simp only [partialSphereSpinInnerBoundaryInclusion_apply,
    partialSphereSpinFillingInverseSpun_planar,
    partialSphereSpinDiskBoundaryInclusion_apply,
    partialSphereSpinFillingInverseCap_apply]
  apply congrArg (partialSphereSpinInr
    (partialSphereSpinFilledOuter outer inner diskBoundary))
  apply Prod.ext
  · exact topologicalPushout_condition inner diskBoundary x.1
  · rfl

/-- The continuous comparison from “spin, then cap” back to “fill, then spin.” -/
def partialSphereSpinFillingInverse
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    C(PartialSphereSpinCappedSecond outer inner diskBoundary,
      PartialSphereSpinFilledFirst outer inner diskBoundary) :=
  topologicalPushoutDesc
    (partialSphereSpinInnerBoundaryInclusion outer inner)
    (partialSphereSpinDiskBoundaryInclusion diskBoundary)
    (partialSphereSpinFillingInverseSpun outer inner diskBoundary)
    (partialSphereSpinFillingInverseCap outer inner diskBoundary)
    (partialSphereSpinFillingInverse_compatibility outer inner diskBoundary)

@[simp]
theorem partialSphereSpinFillingInverse_oneHandle
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (x : OneHandlePiece) :
    partialSphereSpinFillingInverse outer inner diskBoundary
        (partialSphereSpinCappedSecondInl outer inner diskBoundary
          (partialSphereSpinInl outer x)) =
      partialSphereSpinInl
        (partialSphereSpinFilledOuter outer inner diskBoundary) x := by
  simp [partialSphereSpinFillingInverse]

@[simp]
theorem partialSphereSpinFillingInverse_planar
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinFillingInverse outer inner diskBoundary
        (partialSphereSpinCappedSecondInl outer inner diskBoundary
          (partialSphereSpinInr outer (p, s))) =
      partialSphereSpinInr
        (partialSphereSpinFilledOuter outer inner diskBoundary)
        (partialSphereSpinPlanarFillingInl inner diskBoundary p, s) := by
  simp [partialSphereSpinFillingInverse]

@[simp]
theorem partialSphereSpinFillingInverse_filling
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinFillingInverse outer inner diskBoundary
        (partialSphereSpinCappedSecondInr outer inner diskBoundary (d, s)) =
      partialSphereSpinInr
        (partialSphereSpinFilledOuter outer inner diskBoundary)
        (partialSphereSpinPlanarFillingInr inner diskBoundary d, s) := by
  simp [partialSphereSpinFillingInverse]

/-! ## Pushout associativity -/

theorem partialSphereSpinFillingInverse_leftInverse
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    LeftInverse
      (partialSphereSpinFillingInverse outer inner diskBoundary)
      (partialSphereSpinFillingForward outer inner diskBoundary) := by
  intro z
  rcases topologicalPushout_jointly_surjective oneHandleBoundaryInclusion
      (partialSphereSpinBoundaryInclusion
        (partialSphereSpinFilledOuter outer inner diskBoundary)) z with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · simp
  · rcases y with ⟨q, s⟩
    rcases topologicalPushout_jointly_surjective inner diskBoundary q with
      ⟨p, hp⟩ | ⟨d, hd⟩
    · rw [← hp]
      simp
    · rw [← hd]
      simp

theorem partialSphereSpinFillingInverse_rightInverse
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    RightInverse
      (partialSphereSpinFillingInverse outer inner diskBoundary)
      (partialSphereSpinFillingForward outer inner diskBoundary) := by
  intro z
  rcases topologicalPushout_jointly_surjective
      (partialSphereSpinInnerBoundaryInclusion outer inner)
      (partialSphereSpinDiskBoundaryInclusion diskBoundary) z with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rcases topologicalPushout_jointly_surjective oneHandleBoundaryInclusion
        (partialSphereSpinBoundaryInclusion outer) x with
      ⟨h, rfl⟩ | ⟨p, rfl⟩
    · simp
    · rcases p with ⟨p, s⟩
      simp
  · rcases y with ⟨d, s⟩
    simp

/-- Filling the planar factor before taking its partial sphere spin is homeomorphic to first
taking the partial spin and then attaching the product filling piece `D × S²` along the spun
inner boundary. -/
def partialSphereSpinFillingHomeomorph
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D)) :
    PartialSphereSpinFilledFirst outer inner diskBoundary ≃ₜ
      PartialSphereSpinCappedSecond outer inner diskBoundary where
  toFun := partialSphereSpinFillingForward outer inner diskBoundary
  invFun := partialSphereSpinFillingInverse outer inner diskBoundary
  left_inv := partialSphereSpinFillingInverse_leftInverse outer inner diskBoundary
  right_inv := partialSphereSpinFillingInverse_rightInverse outer inner diskBoundary
  continuous_toFun :=
    (partialSphereSpinFillingForward outer inner diskBoundary).continuous
  continuous_invFun :=
    (partialSphereSpinFillingInverse outer inner diskBoundary).continuous

@[simp]
theorem partialSphereSpinFillingHomeomorph_oneHandle
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (x : OneHandlePiece) :
    partialSphereSpinFillingHomeomorph outer inner diskBoundary
        (partialSphereSpinInl
          (partialSphereSpinFilledOuter outer inner diskBoundary) x) =
      partialSphereSpinCappedSecondInl outer inner diskBoundary
        (partialSphereSpinInl outer x) :=
  partialSphereSpinFillingForward_oneHandle outer inner diskBoundary x

@[simp]
theorem partialSphereSpinFillingHomeomorph_planar
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinFillingHomeomorph outer inner diskBoundary
        (partialSphereSpinInr
          (partialSphereSpinFilledOuter outer inner diskBoundary)
          (partialSphereSpinPlanarFillingInl inner diskBoundary p, s)) =
      partialSphereSpinCappedSecondInl outer inner diskBoundary
        (partialSphereSpinInr outer (p, s)) :=
  partialSphereSpinFillingForward_planar outer inner diskBoundary p s

@[simp]
theorem partialSphereSpinFillingHomeomorph_filling
    (outer inner : C(Sphere 1, P)) (diskBoundary : C(Sphere 1, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinFillingHomeomorph outer inner diskBoundary
        (partialSphereSpinInr
          (partialSphereSpinFilledOuter outer inner diskBoundary)
          (partialSphereSpinPlanarFillingInr inner diskBoundary d, s)) =
      partialSphereSpinCappedSecondInr outer inner diskBoundary (d, s) :=
  partialSphereSpinFillingForward_filling outer inner diskBoundary d s

/-! ## The literal `D² × S²` specialization -/

/-- The standard inclusion of the unit circle into the Euclidean closed two-disk. -/
def partialSphereSpinStandardDiskBoundary :
    C(Sphere 1, EuclideanClosedBall 2) where
  toFun u := ⟨u.1, sphere_subset_closedBall u.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem partialSphereSpinStandardDiskBoundary_coe (u : Sphere 1) :
    (partialSphereSpinStandardDiskBoundary u : EuclideanSpace ℝ (Fin 2)) = u.1 :=
  rfl

/-- Its product with the identity of `S²` is exactly the cap-boundary inclusion already used by
the project, as a continuous map. -/
theorem partialSphereSpinStandardDiskBoundary_product_eq_capBoundaryInclusion :
    partialSphereSpinDiskBoundaryInclusion partialSphereSpinStandardDiskBoundary =
      capBoundaryInclusion := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- The generic associativity homeomorphism specialized to the literal closed disk and hence to
the literal cap piece `D² × S²`. -/
def partialSphereSpinStandardDiskFillingHomeomorph
    (outer inner : C(Sphere 1, P)) :
    PartialSphereSpinFilledFirst outer inner partialSphereSpinStandardDiskBoundary ≃ₜ
      PartialSphereSpinCappedSecond outer inner partialSphereSpinStandardDiskBoundary :=
  partialSphereSpinFillingHomeomorph outer inner partialSphereSpinStandardDiskBoundary

@[simp]
theorem partialSphereSpinStandardDiskFillingHomeomorph_oneHandle
    (outer inner : C(Sphere 1, P)) (x : OneHandlePiece) :
    partialSphereSpinStandardDiskFillingHomeomorph outer inner
        (partialSphereSpinInl
          (partialSphereSpinFilledOuter outer inner
            partialSphereSpinStandardDiskBoundary) x) =
      partialSphereSpinCappedSecondInl outer inner
        partialSphereSpinStandardDiskBoundary (partialSphereSpinInl outer x) :=
  partialSphereSpinFillingHomeomorph_oneHandle outer inner
    partialSphereSpinStandardDiskBoundary x

@[simp]
theorem partialSphereSpinStandardDiskFillingHomeomorph_planar
    (outer inner : C(Sphere 1, P)) (p : P) (s : Sphere 2) :
    partialSphereSpinStandardDiskFillingHomeomorph outer inner
        (partialSphereSpinInr
          (partialSphereSpinFilledOuter outer inner
            partialSphereSpinStandardDiskBoundary)
          (partialSphereSpinPlanarFillingInl inner
            partialSphereSpinStandardDiskBoundary p, s)) =
      partialSphereSpinCappedSecondInl outer inner
        partialSphereSpinStandardDiskBoundary
        (partialSphereSpinInr outer (p, s)) :=
  partialSphereSpinFillingHomeomorph_planar outer inner
    partialSphereSpinStandardDiskBoundary p s

@[simp]
theorem partialSphereSpinStandardDiskFillingHomeomorph_cap
    (outer inner : C(Sphere 1, P)) (x : CapPiece) :
    partialSphereSpinStandardDiskFillingHomeomorph outer inner
        (partialSphereSpinInr
          (partialSphereSpinFilledOuter outer inner
            partialSphereSpinStandardDiskBoundary)
          (partialSphereSpinPlanarFillingInr inner
            partialSphereSpinStandardDiskBoundary x.1, x.2)) =
      partialSphereSpinCappedSecondInr outer inner
        partialSphereSpinStandardDiskBoundary x :=
  partialSphereSpinFillingHomeomorph_filling outer inner
    partialSphereSpinStandardDiskBoundary x.1 x.2

/-! ## Simultaneous filling along an arbitrary attaching space -/

/-- Fill `P` by `D` along maps from an arbitrary topological attaching space `A`.  This includes
a disjointly indexed family of boundary circles by taking `A = I × Sphere 1`. -/
abbrev PartialSphereSpinSimultaneousPlanarFilling
    (inner : C(A, P)) (fillBoundary : C(A, D)) : Type :=
  TopologicalPushout inner fillBoundary

/-- The old planar piece inside the simultaneous planar filling. -/
abbrev partialSphereSpinSimultaneousPlanarFillingInl
    (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(P, PartialSphereSpinSimultaneousPlanarFilling inner fillBoundary) :=
  topologicalPushoutInl inner fillBoundary

/-- The simultaneous filling piece inside the planar filling. -/
abbrev partialSphereSpinSimultaneousPlanarFillingInr
    (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(D, PartialSphereSpinSimultaneousPlanarFilling inner fillBoundary) :=
  topologicalPushoutInr inner fillBoundary

/-- The retained outer circle, mapped through the old planar piece of the simultaneous filling. -/
def partialSphereSpinSimultaneousFilledOuter
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(Sphere 1, PartialSphereSpinSimultaneousPlanarFilling inner fillBoundary) :=
  (partialSphereSpinSimultaneousPlanarFillingInl inner fillBoundary).comp outer

@[simp]
theorem partialSphereSpinSimultaneousFilledOuter_apply
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (u : Sphere 1) :
    partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary u =
      partialSphereSpinSimultaneousPlanarFillingInl inner fillBoundary (outer u) :=
  rfl

/-- First perform the simultaneous planar filling and then take the partial sphere spin. -/
abbrev PartialSphereSpinSimultaneousFilledFirst
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) : Type :=
  PartialSphereSpin
    (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)

/-- The product of the arbitrary inner attaching map with `id : S² → S²`, included into the
partial sphere spin of the unfilled planar piece. -/
def partialSphereSpinSimultaneousInnerBoundaryInclusion
    (outer : C(Sphere 1, P)) (inner : C(A, P)) :
    C(A × Sphere 2, PartialSphereSpin outer) where
  toFun x := partialSphereSpinInr outer (inner x.1, x.2)
  continuous_toFun := (partialSphereSpinInr outer).continuous.comp <|
    (inner.continuous.comp continuous_fst).prodMk continuous_snd

@[simp]
theorem partialSphereSpinSimultaneousInnerBoundaryInclusion_apply
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (x : A × Sphere 2) :
    partialSphereSpinSimultaneousInnerBoundaryInclusion outer inner x =
      partialSphereSpinInr outer (inner x.1, x.2) :=
  rfl

/-- Injectivity of an inner attaching map is preserved after taking its product with `S²` and
including it in the partial sphere spin. -/
theorem injective_partialSphereSpinSimultaneousInnerBoundaryInclusion
    (outer : C(Sphere 1, P)) (inner : C(A, P))
    (hinner : Function.Injective inner) :
    Function.Injective
      (partialSphereSpinSimultaneousInnerBoundaryInclusion outer inner) := by
  intro x y hxy
  have hprod : (inner x.1, x.2) = (inner y.1, y.2) :=
    topologicalPushoutInr_injective oneHandleBoundaryInclusion
      (partialSphereSpinBoundaryInclusion outer)
      oneHandleBoundaryInclusion_injective hxy
  exact Prod.ext
    (hinner (congrArg (fun z : P × Sphere 2 ↦ z.1) hprod))
    (congrArg (fun z : P × Sphere 2 ↦ z.2) hprod)

/-- The product of the arbitrary filling-boundary map with `id : S² → S²`. -/
def partialSphereSpinSimultaneousFillBoundaryInclusion
    (fillBoundary : C(A, D)) : C(A × Sphere 2, D × Sphere 2) where
  toFun x := (fillBoundary x.1, x.2)
  continuous_toFun :=
    (fillBoundary.continuous.comp continuous_fst).prodMk continuous_snd

@[simp]
theorem partialSphereSpinSimultaneousFillBoundaryInclusion_apply
    (fillBoundary : C(A, D)) (x : A × Sphere 2) :
    partialSphereSpinSimultaneousFillBoundaryInclusion fillBoundary x =
      (fillBoundary x.1, x.2) :=
  rfl

/-- Injectivity of a filling-boundary map is preserved after taking its product with `S²`. -/
theorem injective_partialSphereSpinSimultaneousFillBoundaryInclusion
    (fillBoundary : C(A, D)) (hfill : Function.Injective fillBoundary) :
    Function.Injective
      (partialSphereSpinSimultaneousFillBoundaryInclusion fillBoundary) := by
  intro x y hxy
  have hprod : (fillBoundary x.1, x.2) = (fillBoundary y.1, y.2) := hxy
  exact Prod.ext
    (hfill (congrArg (fun z : D × Sphere 2 ↦ z.1) hprod))
    (congrArg (fun z : D × Sphere 2 ↦ z.2) hprod)

/-- First spin `P`, then attach `D × S²` simultaneously along `A × S²`. -/
abbrev PartialSphereSpinSimultaneousCappedSecond
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) : Type :=
  TopologicalPushout
    (partialSphereSpinSimultaneousInnerBoundaryInclusion outer inner)
    (partialSphereSpinSimultaneousFillBoundaryInclusion fillBoundary)

/-- The partial spin of `P` inside the simultaneous second-order attachment. -/
abbrev partialSphereSpinSimultaneousCappedSecondInl
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(PartialSphereSpin outer,
      PartialSphereSpinSimultaneousCappedSecond outer inner fillBoundary) :=
  topologicalPushoutInl
    (partialSphereSpinSimultaneousInnerBoundaryInclusion outer inner)
    (partialSphereSpinSimultaneousFillBoundaryInclusion fillBoundary)

/-- The product filling piece inside the simultaneous second-order attachment. -/
abbrev partialSphereSpinSimultaneousCappedSecondInr
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(D × Sphere 2,
      PartialSphereSpinSimultaneousCappedSecond outer inner fillBoundary) :=
  topologicalPushoutInr
    (partialSphereSpinSimultaneousInnerBoundaryInclusion outer inner)
    (partialSphereSpinSimultaneousFillBoundaryInclusion fillBoundary)

/-! ### Forward comparison -/

def partialSphereSpinSimultaneousFillingForwardOneHandle
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(OneHandlePiece,
      PartialSphereSpinSimultaneousCappedSecond outer inner fillBoundary) :=
  (partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary).comp
    (partialSphereSpinInl outer)

def partialSphereSpinSimultaneousFillingForwardPlanar
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(PartialSphereSpinSimultaneousPlanarFilling inner fillBoundary × Sphere 2,
      PartialSphereSpinSimultaneousCappedSecond outer inner fillBoundary) :=
  partialSphereSpinFillingProdDesc inner fillBoundary
    ((partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary).comp
      (partialSphereSpinInr outer))
    (partialSphereSpinSimultaneousCappedSecondInr outer inner fillBoundary)
    (fun a s ↦ topologicalPushout_condition
      (partialSphereSpinSimultaneousInnerBoundaryInclusion outer inner)
      (partialSphereSpinSimultaneousFillBoundaryInclusion fillBoundary) (a, s))

@[simp]
theorem partialSphereSpinSimultaneousFillingForwardPlanar_inl
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingForwardPlanar outer inner fillBoundary
        (partialSphereSpinSimultaneousPlanarFillingInl inner fillBoundary p, s) =
      partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary
        (partialSphereSpinInr outer (p, s)) := by
  unfold partialSphereSpinSimultaneousFillingForwardPlanar
  apply partialSphereSpinFillingProdDesc_inl

@[simp]
theorem partialSphereSpinSimultaneousFillingForwardPlanar_inr
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingForwardPlanar outer inner fillBoundary
        (partialSphereSpinSimultaneousPlanarFillingInr inner fillBoundary d, s) =
      partialSphereSpinSimultaneousCappedSecondInr outer inner fillBoundary (d, s) := by
  unfold partialSphereSpinSimultaneousFillingForwardPlanar
  apply partialSphereSpinFillingProdDesc_inr

theorem partialSphereSpinSimultaneousFillingForward_compatibility
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (x : OneHandleCapBoundary) :
    partialSphereSpinSimultaneousFillingForwardOneHandle outer inner fillBoundary
        (oneHandleBoundaryInclusion x) =
      partialSphereSpinSimultaneousFillingForwardPlanar outer inner fillBoundary
        (partialSphereSpinBoundaryInclusion
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary) x) := by
  change partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary
      (partialSphereSpinInl outer (oneHandleBoundaryInclusion x)) = _
  rw [partialSphereSpin_condition]
  simp [partialSphereSpinBoundaryInclusion_apply]

/-- The continuous map from simultaneous “fill, then spin” to “spin, then attach.” -/
def partialSphereSpinSimultaneousFillingForward
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(PartialSphereSpinSimultaneousFilledFirst outer inner fillBoundary,
      PartialSphereSpinSimultaneousCappedSecond outer inner fillBoundary) :=
  topologicalPushoutDesc oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion
      (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary))
    (partialSphereSpinSimultaneousFillingForwardOneHandle outer inner fillBoundary)
    (partialSphereSpinSimultaneousFillingForwardPlanar outer inner fillBoundary)
    (partialSphereSpinSimultaneousFillingForward_compatibility outer inner fillBoundary)

@[simp]
theorem partialSphereSpinSimultaneousFillingForward_oneHandle
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (x : OneHandlePiece) :
    partialSphereSpinSimultaneousFillingForward outer inner fillBoundary
        (partialSphereSpinInl
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary) x) =
      partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary
        (partialSphereSpinInl outer x) := by
  simp [partialSphereSpinSimultaneousFillingForward,
    partialSphereSpinSimultaneousFillingForwardOneHandle]

@[simp]
theorem partialSphereSpinSimultaneousFillingForward_planar
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingForward outer inner fillBoundary
        (partialSphereSpinInr
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
          (partialSphereSpinSimultaneousPlanarFillingInl inner fillBoundary p, s)) =
      partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary
        (partialSphereSpinInr outer (p, s)) := by
  simp [partialSphereSpinSimultaneousFillingForward]

@[simp]
theorem partialSphereSpinSimultaneousFillingForward_filling
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingForward outer inner fillBoundary
        (partialSphereSpinInr
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
          (partialSphereSpinSimultaneousPlanarFillingInr inner fillBoundary d, s)) =
      partialSphereSpinSimultaneousCappedSecondInr outer inner fillBoundary (d, s) := by
  simp [partialSphereSpinSimultaneousFillingForward]

/-! ### Inverse comparison -/

def partialSphereSpinSimultaneousFillingInverseSpun
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(PartialSphereSpin outer,
      PartialSphereSpinSimultaneousFilledFirst outer inner fillBoundary) :=
  topologicalPushoutDesc oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion outer)
    (partialSphereSpinInl
      (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary))
    ⟨fun x ↦ partialSphereSpinInr
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
        (partialSphereSpinSimultaneousPlanarFillingInl inner fillBoundary x.1, x.2),
      ((partialSphereSpinInr
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)).continuous.comp <|
        (((partialSphereSpinSimultaneousPlanarFillingInl inner fillBoundary).continuous.comp
          continuous_fst).prodMk continuous_snd))⟩
    (fun x ↦ by
      change partialSphereSpinInl
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
          (oneHandleBoundaryInclusion x) =
        partialSphereSpinInr
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary x.1, x.2)
      exact partialSphereSpin_condition
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary) x)

@[simp]
theorem partialSphereSpinSimultaneousFillingInverseSpun_oneHandle
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (x : OneHandlePiece) :
    partialSphereSpinSimultaneousFillingInverseSpun outer inner fillBoundary
        (partialSphereSpinInl outer x) =
      partialSphereSpinInl
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary) x := by
  simp [partialSphereSpinSimultaneousFillingInverseSpun]

@[simp]
theorem partialSphereSpinSimultaneousFillingInverseSpun_planar
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingInverseSpun outer inner fillBoundary
        (partialSphereSpinInr outer (p, s)) =
      partialSphereSpinInr
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
        (partialSphereSpinSimultaneousPlanarFillingInl inner fillBoundary p, s) := by
  simp [partialSphereSpinSimultaneousFillingInverseSpun]

def partialSphereSpinSimultaneousFillingInverseCap
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(D × Sphere 2,
      PartialSphereSpinSimultaneousFilledFirst outer inner fillBoundary) where
  toFun x := partialSphereSpinInr
    (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
    (partialSphereSpinSimultaneousPlanarFillingInr inner fillBoundary x.1, x.2)
  continuous_toFun :=
    (partialSphereSpinInr
      (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)).continuous.comp <|
      (((partialSphereSpinSimultaneousPlanarFillingInr inner fillBoundary).continuous.comp
        continuous_fst).prodMk continuous_snd)

@[simp]
theorem partialSphereSpinSimultaneousFillingInverseCap_apply
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingInverseCap outer inner fillBoundary (d, s) =
      partialSphereSpinInr
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
        (partialSphereSpinSimultaneousPlanarFillingInr inner fillBoundary d, s) :=
  rfl

theorem partialSphereSpinSimultaneousFillingInverse_compatibility
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (x : A × Sphere 2) :
    partialSphereSpinSimultaneousFillingInverseSpun outer inner fillBoundary
        (partialSphereSpinSimultaneousInnerBoundaryInclusion outer inner x) =
      partialSphereSpinSimultaneousFillingInverseCap outer inner fillBoundary
        (partialSphereSpinSimultaneousFillBoundaryInclusion fillBoundary x) := by
  simp only [partialSphereSpinSimultaneousInnerBoundaryInclusion_apply,
    partialSphereSpinSimultaneousFillingInverseSpun_planar,
    partialSphereSpinSimultaneousFillBoundaryInclusion_apply,
    partialSphereSpinSimultaneousFillingInverseCap_apply]
  apply congrArg (partialSphereSpinInr
    (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary))
  apply Prod.ext
  · exact topologicalPushout_condition inner fillBoundary x.1
  · rfl

/-- The continuous inverse comparison for simultaneous filling. -/
def partialSphereSpinSimultaneousFillingInverse
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    C(PartialSphereSpinSimultaneousCappedSecond outer inner fillBoundary,
      PartialSphereSpinSimultaneousFilledFirst outer inner fillBoundary) :=
  topologicalPushoutDesc
    (partialSphereSpinSimultaneousInnerBoundaryInclusion outer inner)
    (partialSphereSpinSimultaneousFillBoundaryInclusion fillBoundary)
    (partialSphereSpinSimultaneousFillingInverseSpun outer inner fillBoundary)
    (partialSphereSpinSimultaneousFillingInverseCap outer inner fillBoundary)
    (partialSphereSpinSimultaneousFillingInverse_compatibility outer inner fillBoundary)

@[simp]
theorem partialSphereSpinSimultaneousFillingInverse_oneHandle
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (x : OneHandlePiece) :
    partialSphereSpinSimultaneousFillingInverse outer inner fillBoundary
        (partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary
          (partialSphereSpinInl outer x)) =
      partialSphereSpinInl
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary) x := by
  simp [partialSphereSpinSimultaneousFillingInverse]

@[simp]
theorem partialSphereSpinSimultaneousFillingInverse_planar
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingInverse outer inner fillBoundary
        (partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary
          (partialSphereSpinInr outer (p, s))) =
      partialSphereSpinInr
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
        (partialSphereSpinSimultaneousPlanarFillingInl inner fillBoundary p, s) := by
  simp [partialSphereSpinSimultaneousFillingInverse]

@[simp]
theorem partialSphereSpinSimultaneousFillingInverse_filling
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingInverse outer inner fillBoundary
        (partialSphereSpinSimultaneousCappedSecondInr outer inner fillBoundary (d, s)) =
      partialSphereSpinInr
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
        (partialSphereSpinSimultaneousPlanarFillingInr inner fillBoundary d, s) := by
  simp [partialSphereSpinSimultaneousFillingInverse]

/-! ### Simultaneous pushout associativity -/

theorem partialSphereSpinSimultaneousFillingInverse_leftInverse
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    LeftInverse
      (partialSphereSpinSimultaneousFillingInverse outer inner fillBoundary)
      (partialSphereSpinSimultaneousFillingForward outer inner fillBoundary) := by
  intro z
  rcases topologicalPushout_jointly_surjective oneHandleBoundaryInclusion
      (partialSphereSpinBoundaryInclusion
        (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)) z with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · simp
  · rcases y with ⟨q, s⟩
    rcases topologicalPushout_jointly_surjective inner fillBoundary q with
      ⟨p, hp⟩ | ⟨d, hd⟩
    · rw [← hp]
      simp
    · rw [← hd]
      simp

theorem partialSphereSpinSimultaneousFillingInverse_rightInverse
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    RightInverse
      (partialSphereSpinSimultaneousFillingInverse outer inner fillBoundary)
      (partialSphereSpinSimultaneousFillingForward outer inner fillBoundary) := by
  intro z
  rcases topologicalPushout_jointly_surjective
      (partialSphereSpinSimultaneousInnerBoundaryInclusion outer inner)
      (partialSphereSpinSimultaneousFillBoundaryInclusion fillBoundary) z with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rcases topologicalPushout_jointly_surjective oneHandleBoundaryInclusion
        (partialSphereSpinBoundaryInclusion outer) x with
      ⟨h, rfl⟩ | ⟨p, rfl⟩
    · simp
    · rcases p with ⟨p, s⟩
      simp
  · rcases y with ⟨d, s⟩
    simp

/-- Simultaneous filling commutes with the partial `S²`-spin: filling `P` along any topological
attaching space `A` before spinning is homeomorphic to attaching `D × S²` along `A × S²` after
spinning. -/
def partialSphereSpinSimultaneousFillingHomeomorph
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D)) :
    PartialSphereSpinSimultaneousFilledFirst outer inner fillBoundary ≃ₜ
      PartialSphereSpinSimultaneousCappedSecond outer inner fillBoundary where
  toFun := partialSphereSpinSimultaneousFillingForward outer inner fillBoundary
  invFun := partialSphereSpinSimultaneousFillingInverse outer inner fillBoundary
  left_inv :=
    partialSphereSpinSimultaneousFillingInverse_leftInverse outer inner fillBoundary
  right_inv :=
    partialSphereSpinSimultaneousFillingInverse_rightInverse outer inner fillBoundary
  continuous_toFun :=
    (partialSphereSpinSimultaneousFillingForward outer inner fillBoundary).continuous
  continuous_invFun :=
    (partialSphereSpinSimultaneousFillingInverse outer inner fillBoundary).continuous

@[simp]
theorem partialSphereSpinSimultaneousFillingHomeomorph_oneHandle
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (x : OneHandlePiece) :
    partialSphereSpinSimultaneousFillingHomeomorph outer inner fillBoundary
        (partialSphereSpinInl
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary) x) =
      partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary
        (partialSphereSpinInl outer x) :=
  partialSphereSpinSimultaneousFillingForward_oneHandle outer inner fillBoundary x

@[simp]
theorem partialSphereSpinSimultaneousFillingHomeomorph_planar
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (p : P) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingHomeomorph outer inner fillBoundary
        (partialSphereSpinInr
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
          (partialSphereSpinSimultaneousPlanarFillingInl inner fillBoundary p, s)) =
      partialSphereSpinSimultaneousCappedSecondInl outer inner fillBoundary
        (partialSphereSpinInr outer (p, s)) :=
  partialSphereSpinSimultaneousFillingForward_planar outer inner fillBoundary p s

@[simp]
theorem partialSphereSpinSimultaneousFillingHomeomorph_filling
    (outer : C(Sphere 1, P)) (inner : C(A, P)) (fillBoundary : C(A, D))
    (d : D) (s : Sphere 2) :
    partialSphereSpinSimultaneousFillingHomeomorph outer inner fillBoundary
        (partialSphereSpinInr
          (partialSphereSpinSimultaneousFilledOuter outer inner fillBoundary)
          (partialSphereSpinSimultaneousPlanarFillingInr inner fillBoundary d, s)) =
      partialSphereSpinSimultaneousCappedSecondInr outer inner fillBoundary (d, s) :=
  partialSphereSpinSimultaneousFillingForward_filling outer inner fillBoundary d s

end SplittingSpheres
