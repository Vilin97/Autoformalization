/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarCapComplement

/-!
# Labels for the strict cap interiors

The complete planar capping has one right cap and one left cap for every element of `ZMod m`.
This file records that literal indexing, identifies each source interior by its strict metric
inequality, and proves that the resulting subsets are pairwise disjoint and exhaust the cap
interior set already defined in `CoordinateExteriorPlanarCapComplement`.

These are point-set statements about the nested pushout.  In particular, no openness,
tubular-neighborhood, or standard-unlink identification is asserted here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## Strict source inequalities -/

/-- A cap label is either a labelled left cap or the unique right cap. -/
abbrev CapLabel (m : ℕ) : Type := ZMod m ⊕ PUnit

/-- A point of the right product cap is off its attaching boundary exactly when its complex
coordinate has norm strictly smaller than the filling radius. -/
@[simp]
theorem mem_coordinateUnlinkExteriorPlanarRightCapInteriorSource_iff
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarRightFillingDisk m × Sphere 2) :
    z ∈ coordinateUnlinkExteriorPlanarRightCapInteriorSource m ↔
      ‖z.1.1‖ < coordinateUnlinkExteriorPlanarRightFillingRadius m := by
  change z ∉ range (partialSphereSpinSimultaneousFillBoundaryInclusion
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)) ↔ _
  constructor
  · intro hz
    have hle : ‖z.1.1‖ ≤ coordinateUnlinkExteriorPlanarRightFillingRadius m :=
      mem_closedBall_zero_iff.mp z.1.2
    exact lt_of_le_of_ne hle fun heq ↦ hz ⟨
      (⟨z.1.1, mem_sphere_zero_iff_norm.mpr heq⟩, z.2), by
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl⟩
  · intro hlt
    rintro ⟨⟨w, s⟩, hws⟩
    have hval : w.1 = z.1.1 :=
      congrArg
        (fun q : CoordinateUnlinkExteriorPlanarRightFillingDisk m × Sphere 2 ↦ q.1.1)
        hws
    have hw : ‖w.1‖ = coordinateUnlinkExteriorPlanarRightFillingRadius m :=
      mem_sphere_zero_iff_norm.mp w.2
    rw [← hval] at hlt
    exact hw.not_lt hlt

/-- A point of the family of left product caps is off its attaching boundary exactly when its
disk coordinate has distance strictly smaller than `1/8` from `-1`. -/
@[simp]
theorem mem_coordinateUnlinkExteriorPlanarLeftCapsInteriorSource_iff
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarLeftFillingDisks m × Sphere 2) :
    z ∈ coordinateUnlinkExteriorPlanarLeftCapsInteriorSource m ↔
      dist z.1.2.1 (-1 : ℂ) < (1 / 8 : ℝ) := by
  change z ∉ range (partialSphereSpinSimultaneousFillBoundaryInclusion
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)) ↔ _
  constructor
  · intro hz
    have hle : dist z.1.2.1 (-1 : ℂ) ≤ (1 / 8 : ℝ) := by
      simpa only [mem_closedBall] using z.1.2.2
    exact lt_of_le_of_ne hle fun heq ↦ hz ⟨
      ((z.1.1, ⟨z.1.2.1, by simpa only [mem_sphere] using heq⟩), z.2), by
        apply Prod.ext
        · apply Prod.ext
          · rfl
          · apply Subtype.ext
            rfl
        · rfl⟩
  · intro hlt
    rintro ⟨⟨⟨a, w⟩, s⟩, hws⟩
    have hval : w.1 = z.1.2.1 :=
      congrArg
        (fun q : CoordinateUnlinkExteriorPlanarLeftFillingDisks m × Sphere 2 ↦ q.1.2.1)
        hws
    have hw : dist w.1 (-1 : ℂ) = (1 / 8 : ℝ) := by
      simpa only [mem_sphere] using w.2
    rw [← hval] at hlt
    exact hw.not_lt hlt

/-! ## The individually labelled cap interiors -/

/-- The strict source interior of the left cap with label `a`. -/
def coordinateUnlinkExteriorPlanarLeftCapInteriorSource
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorPlanarLeftFillingDisks m × Sphere 2) :=
  {z | z.1.1 = a ∧ dist z.1.2.1 (-1 : ℂ) < (1 / 8 : ℝ)}

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarLeftCapInteriorSource_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (z : CoordinateUnlinkExteriorPlanarLeftFillingDisks m × Sphere 2) :
    z ∈ coordinateUnlinkExteriorPlanarLeftCapInteriorSource m a ↔
      z.1.1 = a ∧ dist z.1.2.1 (-1 : ℂ) < (1 / 8 : ℝ) :=
  Iff.rfl

/-- The strict interior of the left cap labelled by `a`, in the complete capping. -/
def coordinateUnlinkExteriorPlanarLeftCapInterior
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorPlanarCompleteCapping m) :=
  coordinateUnlinkExteriorPlanarCompleteCappingInr m ''
    coordinateUnlinkExteriorPlanarLeftCapInteriorSource m a

/-- The strict cap interior selected by a unified cap label. -/
def coordinateUnlinkExteriorPlanarCapInterior
    (m : ℕ) [NeZero m] :
    CapLabel m → Set (CoordinateUnlinkExteriorPlanarCompleteCapping m)
  | Sum.inl a => coordinateUnlinkExteriorPlanarLeftCapInterior m a
  | Sum.inr _ => coordinateUnlinkExteriorPlanarRightCapInterior m

@[simp]
theorem coordinateUnlinkExteriorPlanarCapInterior_inl
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarCapInterior m (Sum.inl a) =
      coordinateUnlinkExteriorPlanarLeftCapInterior m a :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarCapInterior_inr
    (m : ℕ) [NeZero m] (u : PUnit) :
    coordinateUnlinkExteriorPlanarCapInterior m (Sum.inr u) =
      coordinateUnlinkExteriorPlanarRightCapInterior m :=
  rfl

theorem coordinateUnlinkExteriorPlanarLeftCapInteriorSource_subset
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarLeftCapInteriorSource m a ⊆
      coordinateUnlinkExteriorPlanarLeftCapsInteriorSource m := by
  intro z hz
  exact (mem_coordinateUnlinkExteriorPlanarLeftCapsInteriorSource_iff m z).2 hz.2

theorem coordinateUnlinkExteriorPlanarLeftCapInterior_subset
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarLeftCapInterior m a ⊆
      coordinateUnlinkExteriorPlanarLeftCapsInterior m :=
  image_mono (coordinateUnlinkExteriorPlanarLeftCapInteriorSource_subset m a)

theorem coordinateUnlinkExteriorPlanarCapInterior_subset
    (m : ℕ) [NeZero m] (label : CapLabel m) :
    coordinateUnlinkExteriorPlanarCapInterior m label ⊆
      coordinateUnlinkExteriorPlanarCapInteriors m := by
  rcases label with a | u
  · exact (coordinateUnlinkExteriorPlanarLeftCapInterior_subset m a).trans subset_union_right
  · exact subset_union_left

/-! ## Disjointness and exhaustion -/

theorem injective_coordinateUnlinkExteriorPlanarCompleteCappingInr
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarCompleteCappingInr m) :=
  topologicalPushoutInr_injective _ _
    (injective_coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin m)

theorem disjoint_coordinateUnlinkExteriorPlanarLeftCapInterior
    (m : ℕ) [NeZero m] {a b : ZMod m} (hab : a ≠ b) :
    Disjoint (coordinateUnlinkExteriorPlanarLeftCapInterior m a)
      (coordinateUnlinkExteriorPlanarLeftCapInterior m b) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have hsource : x = y :=
    injective_coordinateUnlinkExteriorPlanarCompleteCappingInr m hxy.symm
  apply hab
  calc
    a = x.1.1 := hx.1.symm
    _ = y.1.1 := congrArg
      (fun q : CoordinateUnlinkExteriorPlanarLeftFillingDisks m × Sphere 2 ↦ q.1.1)
      hsource
    _ = b := hy.1

theorem disjoint_coordinateUnlinkExteriorPlanarRightCapInterior_leftCapInterior
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Disjoint (coordinateUnlinkExteriorPlanarRightCapInterior m)
      (coordinateUnlinkExteriorPlanarLeftCapInterior m a) := by
  rw [Set.disjoint_left]
  intro z hzright hzleft
  have hzrange : z ∈ range (coordinateUnlinkExteriorPlanarCompleteCappingInl m) := by
    rcases hzright with ⟨y, hy, rfl⟩
    exact ⟨y, rfl⟩
  rw [range_coordinateUnlinkExteriorPlanarCompleteCappingInl m] at hzrange
  exact hzrange (coordinateUnlinkExteriorPlanarLeftCapInterior_subset m a hzleft)

/-- Distinct cap labels select disjoint strict cap interiors. -/
theorem pairwise_disjoint_coordinateUnlinkExteriorPlanarCapInterior
    (m : ℕ) [NeZero m] :
    Pairwise (Disjoint on coordinateUnlinkExteriorPlanarCapInterior m) := by
  rintro (a | u) (b | v) hne
  · exact disjoint_coordinateUnlinkExteriorPlanarLeftCapInterior m fun hab ↦
      hne (congrArg Sum.inl hab)
  · exact disjoint_coordinateUnlinkExteriorPlanarRightCapInterior_leftCapInterior m a |>.symm
  · exact disjoint_coordinateUnlinkExteriorPlanarRightCapInterior_leftCapInterior m b
  · cases u
    cases v
    exact (hne rfl).elim

/-- The labelled strict cap interiors exhaust exactly the previously defined total cap-interior
set. -/
theorem iUnion_coordinateUnlinkExteriorPlanarCapInterior
    (m : ℕ) [NeZero m] :
    (⋃ label : CapLabel m, coordinateUnlinkExteriorPlanarCapInterior m label) =
      coordinateUnlinkExteriorPlanarCapInteriors m := by
  apply Set.Subset.antisymm
  · intro z hz
    rw [mem_iUnion] at hz
    obtain ⟨label, hz⟩ := hz
    exact coordinateUnlinkExteriorPlanarCapInterior_subset m label hz
  · rintro z (hzright | hzleft)
    · exact mem_iUnion.2 ⟨Sum.inr PUnit.unit, hzright⟩
    · rcases hzleft with ⟨x, hx, rfl⟩
      have hxstrict :=
        (mem_coordinateUnlinkExteriorPlanarLeftCapsInteriorSource_iff m x).1 hx
      exact mem_iUnion.2 ⟨Sum.inl x.1.1, ⟨x, ⟨rfl, hxstrict⟩, rfl⟩⟩

/-- Every labelled cap interior is disjoint from the retained outer (flower-spin) piece. -/
theorem disjoint_range_coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping_capInterior
    (m : ℕ) [NeZero m] (label : CapLabel m) :
    Disjoint (range (coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping m))
      (coordinateUnlinkExteriorPlanarCapInterior m label) := by
  rw [range_coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping]
  exact disjoint_compl_left.mono_right
    (coordinateUnlinkExteriorPlanarCapInterior_subset m label)

/-! ## Number of cap labels -/

/-- There are `m` left labels and one right label. -/
@[simp]
theorem natCard_capLabel (m : ℕ) [NeZero m] : Nat.card (CapLabel m) = m + 1 := by
  rw [Nat.card_sum, Nat.card_zmod, Nat.card_unique]

end SplittingSpheres
