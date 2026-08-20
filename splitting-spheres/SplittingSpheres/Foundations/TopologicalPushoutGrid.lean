/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushout

/-!
# Interchanging the two directions in a grid of topological pushouts

This file considers the commuting grid

```text
HL  ←  E  →  HR
↑      ↑       ↑
BL  ←  C  →  BR
↓      ↓       ↓
FL  ←  A  →  FR.
```

Taking the three horizontal pushouts and then the resulting vertical pushout gives the same
space as taking the three vertical pushouts and then the resulting horizontal pushout.  The
homeomorphism is constructed directly from the topological pushout recursors.  Consequently no
embedding, compactness, separation, or manifold hypotheses are needed.
-/

@[expose] public section

noncomputable section

open Topology

universe u

namespace SplittingSpheres

/-- A commuting `3 × 3` grid whose four outer squares have the common corner `C`.

The field names record the orientation of every arrow.  For example, `centerToTop : C → E`
and `topToTopLeft : E → HL`; `commTopLeft` says that the two paths from `C` to `HL` agree. -/
structure TopologicalPushoutGridDiagram
    (C E A BL BR HL HR FL FR : Type u)
    [TopologicalSpace C] [TopologicalSpace E] [TopologicalSpace A]
    [TopologicalSpace BL] [TopologicalSpace BR]
    [TopologicalSpace HL] [TopologicalSpace HR]
    [TopologicalSpace FL] [TopologicalSpace FR] where
  centerToTop : C(C, E)
  centerToBottom : C(C, A)
  centerToLeft : C(C, BL)
  centerToRight : C(C, BR)
  topToTopLeft : C(E, HL)
  topToTopRight : C(E, HR)
  bottomToBottomLeft : C(A, FL)
  bottomToBottomRight : C(A, FR)
  leftToTopLeft : C(BL, HL)
  leftToBottomLeft : C(BL, FL)
  rightToTopRight : C(BR, HR)
  rightToBottomRight : C(BR, FR)
  commTopLeft : ∀ c, topToTopLeft (centerToTop c) = leftToTopLeft (centerToLeft c)
  commTopRight : ∀ c, topToTopRight (centerToTop c) = rightToTopRight (centerToRight c)
  commBottomLeft :
    ∀ c, bottomToBottomLeft (centerToBottom c) = leftToBottomLeft (centerToLeft c)
  commBottomRight :
    ∀ c, bottomToBottomRight (centerToBottom c) = rightToBottomRight (centerToRight c)

namespace TopologicalPushoutGridDiagram

variable {C E A BL BR HL HR FL FR : Type u}
variable [TopologicalSpace C] [TopologicalSpace E] [TopologicalSpace A]
variable [TopologicalSpace BL] [TopologicalSpace BR]
variable [TopologicalSpace HL] [TopologicalSpace HR]
variable [TopologicalSpace FL] [TopologicalSpace FR]
variable (D : TopologicalPushoutGridDiagram C E A BL BR HL HR FL FR)

/-! ## The six intermediate pushouts -/

/-- The middle horizontal pushout `BL ∪_C BR`. -/
abbrev horizontalMiddle : Type u :=
  TopologicalPushout D.centerToLeft D.centerToRight

/-- The top horizontal pushout `HL ∪_E HR`. -/
abbrev horizontalTop : Type u :=
  TopologicalPushout D.topToTopLeft D.topToTopRight

/-- The bottom horizontal pushout `FL ∪_A FR`. -/
abbrev horizontalBottom : Type u :=
  TopologicalPushout D.bottomToBottomLeft D.bottomToBottomRight

/-- The central vertical pushout `E ∪_C A`. -/
abbrev verticalCenter : Type u :=
  TopologicalPushout D.centerToTop D.centerToBottom

/-- The left vertical pushout `HL ∪_BL FL`. -/
abbrev verticalLeft : Type u :=
  TopologicalPushout D.leftToTopLeft D.leftToBottomLeft

/-- The right vertical pushout `HR ∪_BR FR`. -/
abbrev verticalRight : Type u :=
  TopologicalPushout D.rightToTopRight D.rightToBottomRight

/-! ## Induced maps between the intermediate pushouts -/

/-- The map `BL ∪_C BR → HL ∪_E HR` induced by the top two squares. -/
def horizontalMiddleToTop : C(D.horizontalMiddle, D.horizontalTop) :=
  topologicalPushoutDesc D.centerToLeft D.centerToRight
    ((topologicalPushoutInl D.topToTopLeft D.topToTopRight).comp D.leftToTopLeft)
    ((topologicalPushoutInr D.topToTopLeft D.topToTopRight).comp D.rightToTopRight)
    (fun c ↦ by
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, ← D.commTopLeft c,
        ← D.commTopRight c]
      exact topologicalPushout_condition D.topToTopLeft D.topToTopRight (D.centerToTop c))

@[simp]
theorem horizontalMiddleToTop_inl (x : BL) :
    D.horizontalMiddleToTop
        (topologicalPushoutInl D.centerToLeft D.centerToRight x) =
      topologicalPushoutInl D.topToTopLeft D.topToTopRight (D.leftToTopLeft x) :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem horizontalMiddleToTop_inr (x : BR) :
    D.horizontalMiddleToTop
        (topologicalPushoutInr D.centerToLeft D.centerToRight x) =
      topologicalPushoutInr D.topToTopLeft D.topToTopRight (D.rightToTopRight x) :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

/-- The map `BL ∪_C BR → FL ∪_A FR` induced by the bottom two squares. -/
def horizontalMiddleToBottom : C(D.horizontalMiddle, D.horizontalBottom) :=
  topologicalPushoutDesc D.centerToLeft D.centerToRight
    ((topologicalPushoutInl D.bottomToBottomLeft D.bottomToBottomRight).comp
      D.leftToBottomLeft)
    ((topologicalPushoutInr D.bottomToBottomLeft D.bottomToBottomRight).comp
      D.rightToBottomRight)
    (fun c ↦ by
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, ← D.commBottomLeft c,
        ← D.commBottomRight c]
      exact topologicalPushout_condition D.bottomToBottomLeft D.bottomToBottomRight
        (D.centerToBottom c))

@[simp]
theorem horizontalMiddleToBottom_inl (x : BL) :
    D.horizontalMiddleToBottom
        (topologicalPushoutInl D.centerToLeft D.centerToRight x) =
      topologicalPushoutInl D.bottomToBottomLeft D.bottomToBottomRight
        (D.leftToBottomLeft x) :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem horizontalMiddleToBottom_inr (x : BR) :
    D.horizontalMiddleToBottom
        (topologicalPushoutInr D.centerToLeft D.centerToRight x) =
      topologicalPushoutInr D.bottomToBottomLeft D.bottomToBottomRight
        (D.rightToBottomRight x) :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

/-- The map `E ∪_C A → HL ∪_BL FL` induced by the two left squares. -/
def verticalCenterToLeft : C(D.verticalCenter, D.verticalLeft) :=
  topologicalPushoutDesc D.centerToTop D.centerToBottom
    ((topologicalPushoutInl D.leftToTopLeft D.leftToBottomLeft).comp D.topToTopLeft)
    ((topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft).comp
      D.bottomToBottomLeft)
    (fun c ↦ by
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, D.commTopLeft c,
        D.commBottomLeft c]
      exact topologicalPushout_condition D.leftToTopLeft D.leftToBottomLeft
        (D.centerToLeft c))

@[simp]
theorem verticalCenterToLeft_inl (x : E) :
    D.verticalCenterToLeft
        (topologicalPushoutInl D.centerToTop D.centerToBottom x) =
      topologicalPushoutInl D.leftToTopLeft D.leftToBottomLeft (D.topToTopLeft x) :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem verticalCenterToLeft_inr (x : A) :
    D.verticalCenterToLeft
        (topologicalPushoutInr D.centerToTop D.centerToBottom x) =
      topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft
        (D.bottomToBottomLeft x) :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

/-- The map `E ∪_C A → HR ∪_BR FR` induced by the two right squares. -/
def verticalCenterToRight : C(D.verticalCenter, D.verticalRight) :=
  topologicalPushoutDesc D.centerToTop D.centerToBottom
    ((topologicalPushoutInl D.rightToTopRight D.rightToBottomRight).comp D.topToTopRight)
    ((topologicalPushoutInr D.rightToTopRight D.rightToBottomRight).comp
      D.bottomToBottomRight)
    (fun c ↦ by
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, D.commTopRight c,
        D.commBottomRight c]
      exact topologicalPushout_condition D.rightToTopRight D.rightToBottomRight
        (D.centerToRight c))

@[simp]
theorem verticalCenterToRight_inl (x : E) :
    D.verticalCenterToRight
        (topologicalPushoutInl D.centerToTop D.centerToBottom x) =
      topologicalPushoutInl D.rightToTopRight D.rightToBottomRight (D.topToTopRight x) :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem verticalCenterToRight_inr (x : A) :
    D.verticalCenterToRight
        (topologicalPushoutInr D.centerToTop D.centerToBottom x) =
      topologicalPushoutInr D.rightToTopRight D.rightToBottomRight
        (D.bottomToBottomRight x) :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

/-! ## The two iterated pushouts -/

/-- First take all three horizontal pushouts, then take the resulting vertical pushout. -/
abbrev rowFirst : Type u :=
  TopologicalPushout D.horizontalMiddleToTop D.horizontalMiddleToBottom

/-- First take all three vertical pushouts, then take the resulting horizontal pushout. -/
abbrev columnFirst : Type u :=
  TopologicalPushout D.verticalCenterToLeft D.verticalCenterToRight

/-! ## The four terminal-piece maps -/

/-- The canonical copy of `HL` in the row-first iterated pushout. -/
def rowFirstTopLeft : C(HL, D.rowFirst) :=
  (topologicalPushoutInl D.horizontalMiddleToTop D.horizontalMiddleToBottom).comp
    (topologicalPushoutInl D.topToTopLeft D.topToTopRight)

/-- The canonical copy of `HR` in the row-first iterated pushout. -/
def rowFirstTopRight : C(HR, D.rowFirst) :=
  (topologicalPushoutInl D.horizontalMiddleToTop D.horizontalMiddleToBottom).comp
    (topologicalPushoutInr D.topToTopLeft D.topToTopRight)

/-- The canonical copy of `FL` in the row-first iterated pushout. -/
def rowFirstBottomLeft : C(FL, D.rowFirst) :=
  (topologicalPushoutInr D.horizontalMiddleToTop D.horizontalMiddleToBottom).comp
    (topologicalPushoutInl D.bottomToBottomLeft D.bottomToBottomRight)

/-- The canonical copy of `FR` in the row-first iterated pushout. -/
def rowFirstBottomRight : C(FR, D.rowFirst) :=
  (topologicalPushoutInr D.horizontalMiddleToTop D.horizontalMiddleToBottom).comp
    (topologicalPushoutInr D.bottomToBottomLeft D.bottomToBottomRight)

/-- The canonical copy of `HL` in the column-first iterated pushout. -/
def columnFirstTopLeft : C(HL, D.columnFirst) :=
  (topologicalPushoutInl D.verticalCenterToLeft D.verticalCenterToRight).comp
    (topologicalPushoutInl D.leftToTopLeft D.leftToBottomLeft)

/-- The canonical copy of `HR` in the column-first iterated pushout. -/
def columnFirstTopRight : C(HR, D.columnFirst) :=
  (topologicalPushoutInr D.verticalCenterToLeft D.verticalCenterToRight).comp
    (topologicalPushoutInl D.rightToTopRight D.rightToBottomRight)

/-- The canonical copy of `FL` in the column-first iterated pushout. -/
def columnFirstBottomLeft : C(FL, D.columnFirst) :=
  (topologicalPushoutInl D.verticalCenterToLeft D.verticalCenterToRight).comp
    (topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft)

/-- The canonical copy of `FR` in the column-first iterated pushout. -/
def columnFirstBottomRight : C(FR, D.columnFirst) :=
  (topologicalPushoutInr D.verticalCenterToLeft D.verticalCenterToRight).comp
    (topologicalPushoutInr D.rightToTopRight D.rightToBottomRight)

/-! ## The row-first to column-first map -/

/-- Map the top horizontal pushout into the column-first iterated pushout. -/
def horizontalTopToColumnFirst : C(D.horizontalTop, D.columnFirst) :=
  topologicalPushoutDesc D.topToTopLeft D.topToTopRight
    D.columnFirstTopLeft D.columnFirstTopRight
    (fun e ↦ by
      unfold columnFirstTopLeft columnFirstTopRight
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
      rw [← D.verticalCenterToLeft_inl e, ← D.verticalCenterToRight_inl e]
      exact topologicalPushout_condition D.verticalCenterToLeft D.verticalCenterToRight
        (topologicalPushoutInl D.centerToTop D.centerToBottom e))

@[simp]
theorem horizontalTopToColumnFirst_inl (x : HL) :
    D.horizontalTopToColumnFirst
        (topologicalPushoutInl D.topToTopLeft D.topToTopRight x) =
      D.columnFirstTopLeft x :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem horizontalTopToColumnFirst_inr (x : HR) :
    D.horizontalTopToColumnFirst
        (topologicalPushoutInr D.topToTopLeft D.topToTopRight x) =
      D.columnFirstTopRight x :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

/-- Map the bottom horizontal pushout into the column-first iterated pushout. -/
def horizontalBottomToColumnFirst : C(D.horizontalBottom, D.columnFirst) :=
  topologicalPushoutDesc D.bottomToBottomLeft D.bottomToBottomRight
    D.columnFirstBottomLeft D.columnFirstBottomRight
    (fun a ↦ by
      unfold columnFirstBottomLeft columnFirstBottomRight
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
      rw [← D.verticalCenterToLeft_inr a, ← D.verticalCenterToRight_inr a]
      exact topologicalPushout_condition D.verticalCenterToLeft D.verticalCenterToRight
        (topologicalPushoutInr D.centerToTop D.centerToBottom a))

@[simp]
theorem horizontalBottomToColumnFirst_inl (x : FL) :
    D.horizontalBottomToColumnFirst
        (topologicalPushoutInl D.bottomToBottomLeft D.bottomToBottomRight x) =
      D.columnFirstBottomLeft x :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem horizontalBottomToColumnFirst_inr (x : FR) :
    D.horizontalBottomToColumnFirst
        (topologicalPushoutInr D.bottomToBottomLeft D.bottomToBottomRight x) =
      D.columnFirstBottomRight x :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

/-- The canonical continuous map from the row-first to the column-first iterated pushout. -/
def rowFirstToColumnFirst : C(D.rowFirst, D.columnFirst) :=
  topologicalPushoutDesc D.horizontalMiddleToTop D.horizontalMiddleToBottom
    D.horizontalTopToColumnFirst D.horizontalBottomToColumnFirst
    (fun b ↦ by
      rcases topologicalPushout_jointly_surjective D.centerToLeft D.centerToRight b with
        ⟨bl, rfl⟩ | ⟨br, rfl⟩
      · rw [D.horizontalMiddleToTop_inl, D.horizontalMiddleToBottom_inl,
          D.horizontalTopToColumnFirst_inl, D.horizontalBottomToColumnFirst_inl]
        unfold columnFirstTopLeft columnFirstBottomLeft
        rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
        exact congrArg
          (topologicalPushoutInl D.verticalCenterToLeft D.verticalCenterToRight)
          (topologicalPushout_condition D.leftToTopLeft D.leftToBottomLeft bl)
      · rw [D.horizontalMiddleToTop_inr, D.horizontalMiddleToBottom_inr,
          D.horizontalTopToColumnFirst_inr, D.horizontalBottomToColumnFirst_inr]
        unfold columnFirstTopRight columnFirstBottomRight
        rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
        exact congrArg
          (topologicalPushoutInr D.verticalCenterToLeft D.verticalCenterToRight)
          (topologicalPushout_condition D.rightToTopRight D.rightToBottomRight br))

@[simp]
theorem rowFirstToColumnFirst_topLeft (x : HL) :
    D.rowFirstToColumnFirst (D.rowFirstTopLeft x) = D.columnFirstTopLeft x := by
  unfold rowFirstTopLeft rowFirstToColumnFirst
  rw [ContinuousMap.comp_apply, topologicalPushoutDesc_inl,
    horizontalTopToColumnFirst_inl]

@[simp]
theorem rowFirstToColumnFirst_topRight (x : HR) :
    D.rowFirstToColumnFirst (D.rowFirstTopRight x) = D.columnFirstTopRight x := by
  unfold rowFirstTopRight rowFirstToColumnFirst
  rw [ContinuousMap.comp_apply, topologicalPushoutDesc_inl,
    horizontalTopToColumnFirst_inr]

@[simp]
theorem rowFirstToColumnFirst_bottomLeft (x : FL) :
    D.rowFirstToColumnFirst (D.rowFirstBottomLeft x) = D.columnFirstBottomLeft x := by
  unfold rowFirstBottomLeft rowFirstToColumnFirst
  rw [ContinuousMap.comp_apply, topologicalPushoutDesc_inr,
    horizontalBottomToColumnFirst_inl]

@[simp]
theorem rowFirstToColumnFirst_bottomRight (x : FR) :
    D.rowFirstToColumnFirst (D.rowFirstBottomRight x) = D.columnFirstBottomRight x := by
  unfold rowFirstBottomRight rowFirstToColumnFirst
  rw [ContinuousMap.comp_apply, topologicalPushoutDesc_inr,
    horizontalBottomToColumnFirst_inr]

/-! ## The column-first to row-first map -/

/-- Map the left vertical pushout into the row-first iterated pushout. -/
def verticalLeftToRowFirst : C(D.verticalLeft, D.rowFirst) :=
  topologicalPushoutDesc D.leftToTopLeft D.leftToBottomLeft
    D.rowFirstTopLeft D.rowFirstBottomLeft
    (fun bl ↦ by
      unfold rowFirstTopLeft rowFirstBottomLeft
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply,
        ← D.horizontalMiddleToTop_inl bl, ← D.horizontalMiddleToBottom_inl bl]
      exact topologicalPushout_condition D.horizontalMiddleToTop
        D.horizontalMiddleToBottom
        (topologicalPushoutInl D.centerToLeft D.centerToRight bl))

@[simp]
theorem verticalLeftToRowFirst_inl (x : HL) :
    D.verticalLeftToRowFirst
        (topologicalPushoutInl D.leftToTopLeft D.leftToBottomLeft x) =
      D.rowFirstTopLeft x :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem verticalLeftToRowFirst_inr (x : FL) :
    D.verticalLeftToRowFirst
        (topologicalPushoutInr D.leftToTopLeft D.leftToBottomLeft x) =
      D.rowFirstBottomLeft x :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

/-- Map the right vertical pushout into the row-first iterated pushout. -/
def verticalRightToRowFirst : C(D.verticalRight, D.rowFirst) :=
  topologicalPushoutDesc D.rightToTopRight D.rightToBottomRight
    D.rowFirstTopRight D.rowFirstBottomRight
    (fun br ↦ by
      unfold rowFirstTopRight rowFirstBottomRight
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply,
        ← D.horizontalMiddleToTop_inr br, ← D.horizontalMiddleToBottom_inr br]
      exact topologicalPushout_condition D.horizontalMiddleToTop
        D.horizontalMiddleToBottom
        (topologicalPushoutInr D.centerToLeft D.centerToRight br))

@[simp]
theorem verticalRightToRowFirst_inl (x : HR) :
    D.verticalRightToRowFirst
        (topologicalPushoutInl D.rightToTopRight D.rightToBottomRight x) =
      D.rowFirstTopRight x :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem verticalRightToRowFirst_inr (x : FR) :
    D.verticalRightToRowFirst
        (topologicalPushoutInr D.rightToTopRight D.rightToBottomRight x) =
      D.rowFirstBottomRight x :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

/-- The canonical continuous map from the column-first to the row-first iterated pushout. -/
def columnFirstToRowFirst : C(D.columnFirst, D.rowFirst) :=
  topologicalPushoutDesc D.verticalCenterToLeft D.verticalCenterToRight
    D.verticalLeftToRowFirst D.verticalRightToRowFirst
    (fun n ↦ by
      rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom n with
        ⟨e, rfl⟩ | ⟨a, rfl⟩
      · rw [D.verticalCenterToLeft_inl, D.verticalCenterToRight_inl,
          D.verticalLeftToRowFirst_inl, D.verticalRightToRowFirst_inl]
        unfold rowFirstTopLeft rowFirstTopRight
        rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
        exact congrArg
          (topologicalPushoutInl D.horizontalMiddleToTop D.horizontalMiddleToBottom)
          (topologicalPushout_condition D.topToTopLeft D.topToTopRight e)
      · rw [D.verticalCenterToLeft_inr, D.verticalCenterToRight_inr,
          D.verticalLeftToRowFirst_inr, D.verticalRightToRowFirst_inr]
        unfold rowFirstBottomLeft rowFirstBottomRight
        rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
        exact congrArg
          (topologicalPushoutInr D.horizontalMiddleToTop D.horizontalMiddleToBottom)
          (topologicalPushout_condition D.bottomToBottomLeft D.bottomToBottomRight a))

@[simp]
theorem columnFirstToRowFirst_topLeft (x : HL) :
    D.columnFirstToRowFirst (D.columnFirstTopLeft x) = D.rowFirstTopLeft x := by
  unfold columnFirstTopLeft columnFirstToRowFirst
  rw [ContinuousMap.comp_apply, topologicalPushoutDesc_inl,
    verticalLeftToRowFirst_inl]

@[simp]
theorem columnFirstToRowFirst_topRight (x : HR) :
    D.columnFirstToRowFirst (D.columnFirstTopRight x) = D.rowFirstTopRight x := by
  unfold columnFirstTopRight columnFirstToRowFirst
  rw [ContinuousMap.comp_apply, topologicalPushoutDesc_inr,
    verticalRightToRowFirst_inl]

@[simp]
theorem columnFirstToRowFirst_bottomLeft (x : FL) :
    D.columnFirstToRowFirst (D.columnFirstBottomLeft x) = D.rowFirstBottomLeft x := by
  unfold columnFirstBottomLeft columnFirstToRowFirst
  rw [ContinuousMap.comp_apply, topologicalPushoutDesc_inl,
    verticalLeftToRowFirst_inr]

@[simp]
theorem columnFirstToRowFirst_bottomRight (x : FR) :
    D.columnFirstToRowFirst (D.columnFirstBottomRight x) = D.rowFirstBottomRight x := by
  unfold columnFirstBottomRight columnFirstToRowFirst
  rw [ContinuousMap.comp_apply, topologicalPushoutDesc_inr,
    verticalRightToRowFirst_inr]

/-! ## Fubini interchange -/

/-- Canonical interchange of the two orders of taking pushouts in a commuting `3 × 3` grid. -/
def topologicalPushoutGridHomeomorph : D.rowFirst ≃ₜ D.columnFirst where
  toFun := D.rowFirstToColumnFirst
  invFun := D.columnFirstToRowFirst
  left_inv z := by
    rcases topologicalPushout_jointly_surjective D.horizontalMiddleToTop
        D.horizontalMiddleToBottom z with ⟨h, rfl⟩ | ⟨f, rfl⟩
    · rcases topologicalPushout_jointly_surjective D.topToTopLeft D.topToTopRight h with
        ⟨hl, rfl⟩ | ⟨hr, rfl⟩
      · change D.columnFirstToRowFirst
          (D.rowFirstToColumnFirst (D.rowFirstTopLeft hl)) = D.rowFirstTopLeft hl
        rw [D.rowFirstToColumnFirst_topLeft, D.columnFirstToRowFirst_topLeft]
      · change D.columnFirstToRowFirst
          (D.rowFirstToColumnFirst (D.rowFirstTopRight hr)) = D.rowFirstTopRight hr
        rw [D.rowFirstToColumnFirst_topRight, D.columnFirstToRowFirst_topRight]
    · rcases topologicalPushout_jointly_surjective D.bottomToBottomLeft
        D.bottomToBottomRight f with ⟨fl, rfl⟩ | ⟨fr, rfl⟩
      · change D.columnFirstToRowFirst
          (D.rowFirstToColumnFirst (D.rowFirstBottomLeft fl)) = D.rowFirstBottomLeft fl
        rw [D.rowFirstToColumnFirst_bottomLeft, D.columnFirstToRowFirst_bottomLeft]
      · change D.columnFirstToRowFirst
          (D.rowFirstToColumnFirst (D.rowFirstBottomRight fr)) = D.rowFirstBottomRight fr
        rw [D.rowFirstToColumnFirst_bottomRight, D.columnFirstToRowFirst_bottomRight]
  right_inv z := by
    rcases topologicalPushout_jointly_surjective D.verticalCenterToLeft
        D.verticalCenterToRight z with ⟨l, rfl⟩ | ⟨r, rfl⟩
    · rcases topologicalPushout_jointly_surjective D.leftToTopLeft D.leftToBottomLeft l with
        ⟨hl, rfl⟩ | ⟨fl, rfl⟩
      · change D.rowFirstToColumnFirst
          (D.columnFirstToRowFirst (D.columnFirstTopLeft hl)) = D.columnFirstTopLeft hl
        rw [D.columnFirstToRowFirst_topLeft, D.rowFirstToColumnFirst_topLeft]
      · change D.rowFirstToColumnFirst
          (D.columnFirstToRowFirst (D.columnFirstBottomLeft fl)) = D.columnFirstBottomLeft fl
        rw [D.columnFirstToRowFirst_bottomLeft, D.rowFirstToColumnFirst_bottomLeft]
    · rcases topologicalPushout_jointly_surjective D.rightToTopRight
        D.rightToBottomRight r with ⟨hr, rfl⟩ | ⟨fr, rfl⟩
      · change D.rowFirstToColumnFirst
          (D.columnFirstToRowFirst (D.columnFirstTopRight hr)) = D.columnFirstTopRight hr
        rw [D.columnFirstToRowFirst_topRight, D.rowFirstToColumnFirst_topRight]
      · change D.rowFirstToColumnFirst
          (D.columnFirstToRowFirst (D.columnFirstBottomRight fr)) =
            D.columnFirstBottomRight fr
        rw [D.columnFirstToRowFirst_bottomRight, D.rowFirstToColumnFirst_bottomRight]
  continuous_toFun := D.rowFirstToColumnFirst.continuous
  continuous_invFun := D.columnFirstToRowFirst.continuous

/-! The next eight laws give the exact action in both directions on every terminal piece. -/

@[simp]
theorem topologicalPushoutGridHomeomorph_apply_topLeft (x : HL) :
    D.topologicalPushoutGridHomeomorph (D.rowFirstTopLeft x) =
      D.columnFirstTopLeft x :=
  D.rowFirstToColumnFirst_topLeft x

@[simp]
theorem topologicalPushoutGridHomeomorph_apply_topRight (x : HR) :
    D.topologicalPushoutGridHomeomorph (D.rowFirstTopRight x) =
      D.columnFirstTopRight x :=
  D.rowFirstToColumnFirst_topRight x

@[simp]
theorem topologicalPushoutGridHomeomorph_apply_bottomLeft (x : FL) :
    D.topologicalPushoutGridHomeomorph (D.rowFirstBottomLeft x) =
      D.columnFirstBottomLeft x :=
  D.rowFirstToColumnFirst_bottomLeft x

@[simp]
theorem topologicalPushoutGridHomeomorph_apply_bottomRight (x : FR) :
    D.topologicalPushoutGridHomeomorph (D.rowFirstBottomRight x) =
      D.columnFirstBottomRight x :=
  D.rowFirstToColumnFirst_bottomRight x

@[simp]
theorem topologicalPushoutGridHomeomorph_symm_apply_topLeft (x : HL) :
    D.topologicalPushoutGridHomeomorph.symm (D.columnFirstTopLeft x) =
      D.rowFirstTopLeft x :=
  D.columnFirstToRowFirst_topLeft x

@[simp]
theorem topologicalPushoutGridHomeomorph_symm_apply_topRight (x : HR) :
    D.topologicalPushoutGridHomeomorph.symm (D.columnFirstTopRight x) =
      D.rowFirstTopRight x :=
  D.columnFirstToRowFirst_topRight x

@[simp]
theorem topologicalPushoutGridHomeomorph_symm_apply_bottomLeft (x : FL) :
    D.topologicalPushoutGridHomeomorph.symm (D.columnFirstBottomLeft x) =
      D.rowFirstBottomLeft x :=
  D.columnFirstToRowFirst_bottomLeft x

@[simp]
theorem topologicalPushoutGridHomeomorph_symm_apply_bottomRight (x : FR) :
    D.topologicalPushoutGridHomeomorph.symm (D.columnFirstBottomRight x) =
      D.rowFirstBottomRight x :=
  D.columnFirstToRowFirst_bottomRight x

end TopologicalPushoutGridDiagram

end SplittingSpheres
