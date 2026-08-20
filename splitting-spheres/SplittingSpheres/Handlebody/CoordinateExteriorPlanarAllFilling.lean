/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Instances.ZMod
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarLeftLobes
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterRadial

/-!
# Filling every inner hole of the planar power flower

After filling the connected right hole, the remaining missing set is the disjoint union of the
`m` closed left lobes.  Attaching all those disks simultaneously gives exactly the polynomial
outer disk.  This file packages that assertion as an honest topological pushout homeomorphism.
Together with the radial straightening of the outer disk, this is a direct point-set replacement
for an appeal to compact-surface classification.

No smooth structure, boundary orientation, or four-dimensional handle assertion is made here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## The two pieces inside the outer polynomial disk -/

/-- The old piece after its connected right hole has been filled. -/
def coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk
    (m : ℕ) :
    C(CoordinateUnlinkExteriorPlanarRightFilledFlower m,
      ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m)) where
  toFun z := ⟨z.1, z.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk_coe
    (m : ℕ) (z : CoordinateUnlinkExteriorPlanarRightFilledFlower m) :
    (coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m z : ℂ) = z.1 :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk
    (m : ℕ) :
    Injective (coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m) := by
  intro z w h
  apply Subtype.ext
  exact congrArg
    (fun q : ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m) ↦ q.1) h

/-- All left filling disks, with their deck labels retained. -/
abbrev CoordinateUnlinkExteriorPlanarLeftFillingDisks (m : ℕ) : Type :=
  ZMod m × CoordinateUnlinkExteriorPlanarLeftCharacterDisk

/-- All left attaching circles, with their deck labels retained. -/
abbrev CoordinateUnlinkExteriorPlanarLeftFillingBoundaries (m : ℕ) : Type :=
  ZMod m × CoordinateUnlinkExteriorPlanarLeftCharacterBoundary

theorem norm_add_half_coordinateUnlinkExteriorPlanarLeftCharacterDisk_le
    (w : CoordinateUnlinkExteriorPlanarLeftCharacterDisk) :
    ‖w.1 + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius := by
  have hw : ‖w.1 + 1‖ ≤ (1 / 8 : ℝ) := by
    have hdist : dist w.1 (-1 : ℂ) ≤ 1 / 8 := by
      simpa only [mem_closedBall] using w.2
    simpa [Complex.dist_eq] using hdist
  calc
    ‖w.1 + (1 / 2 : ℂ)‖ = ‖(w.1 + 1) + (-1 / 2 : ℂ)‖ := by
      congr 1
      ring
    _ ≤ ‖w.1 + 1‖ + ‖(-1 / 2 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 / 8 + 1 / 2 :=
      add_le_add hw (by norm_num)
    _ = 5 / 8 := by norm_num
    _ ≤ sphereHandleRadius := fiveEighth_lt_sphereHandleRadius.le

/-- Include every labelled left lobe disk in the outer polynomial disk. -/
def coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarLeftFillingDisks m,
      ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m)) where
  toFun x := ⟨coordinateUnlinkExteriorPlanarLeftLobeMap m x.1 x.2, by
    change ‖coordinateUnlinkExteriorPlanarLeftLobeMap m x.1 x.2 ^ m +
      (1 / 2 : ℂ)‖ ≤ sphereHandleRadius
    rw [coordinateUnlinkExteriorPlanarLeftLobeMap_pow]
    exact norm_add_half_coordinateUnlinkExteriorPlanarLeftCharacterDisk_le x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hindex : Continuous (fun a : ZMod m ↦
        (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ)) :=
      continuous_of_discreteTopology
    exact (hindex.comp continuous_fst).mul <|
      (continuous_coordinateUnlinkExteriorPlanarLeftRootDiskMap m).comp continuous_snd

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk_coe
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarLeftFillingDisks m) :
    (coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m x : ℂ) =
      coordinateUnlinkExteriorPlanarLeftLobeMap m x.1 x.2 :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m) := by
  rintro ⟨a, w⟩ ⟨b, v⟩ h
  have hval : coordinateUnlinkExteriorPlanarLeftLobeMap m a w =
      coordinateUnlinkExteriorPlanarLeftLobeMap m b v :=
    congrArg (fun q : ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m) ↦ q.1) h
  have hab : a = b := by
    by_contra hab
    have hdis := disjoint_range_coordinateUnlinkExteriorPlanarLeftLobeMap m hab
    rw [Set.disjoint_left] at hdis
    exact hdis ⟨w, rfl⟩ ⟨v, hval.symm⟩
  subst b
  have hwv := injective_coordinateUnlinkExteriorPlanarLeftLobeMap m a hval
  exact Prod.ext rfl hwv

/-! ## The simultaneous attaching boundary -/

/-- Include every labelled character circle in its corresponding labelled disk. -/
def coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks
    (m : ℕ) :
    C(CoordinateUnlinkExteriorPlanarLeftFillingBoundaries m,
      CoordinateUnlinkExteriorPlanarLeftFillingDisks m) where
  toFun x := (x.1,
    coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk x.2)
  continuous_toFun := continuous_fst.prodMk <|
    coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk.continuous.comp continuous_snd

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks_apply
    (m : ℕ)
    (x : CoordinateUnlinkExteriorPlanarLeftFillingBoundaries m) :
    coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m x =
      (x.1, coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk x.2) :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks
    (m : ℕ) :
    Injective (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) := by
  rintro ⟨a, w⟩ ⟨b, v⟩ h
  have hab : a = b := congrArg Prod.fst h
  have hwv :
      coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk w =
        coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk v :=
    congrArg Prod.snd h
  apply Prod.ext hab
  apply Subtype.ext
  exact congrArg
    (fun q : CoordinateUnlinkExteriorPlanarLeftCharacterDisk ↦ q.1) hwv

/-- Include every labelled lobe boundary in the right-filled old piece. -/
def coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarLeftFillingBoundaries m,
      CoordinateUnlinkExteriorPlanarRightFilledFlower m) where
  toFun x := ⟨coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m x.1 x.2,
    by
      constructor
      · change ‖coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m x.1 x.2 ^ m +
          (1 / 2 : ℂ)‖ ≤ sphereHandleRadius
        rw [coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap_pow]
        exact norm_add_half_coordinateUnlinkExteriorPlanarLeftCharacterBoundary_le x.2
      · change (1 / 8 : ℝ) ≤
          ‖coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m x.1 x.2 ^ m + 1‖
        rw [coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap_pow,
          norm_add_one_coordinateUnlinkExteriorPlanarLeftCharacterBoundary]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hindex : Continuous (fun a : ZMod m ↦
        (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ)) :=
      continuous_of_discreteTopology
    exact (hindex.comp continuous_fst).mul <|
      (continuous_coordinateUnlinkExteriorPlanarLeftRootDiskMap m).comp <|
        coordinateUnlinkExteriorPlanarLeftCharacterBoundaryToDisk.continuous.comp continuous_snd

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower_coe
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarLeftFillingBoundaries m) :
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m x : ℂ) =
      coordinateUnlinkExteriorPlanarLeftLobeBoundaryMap m x.1 x.2 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarAllFilling_compatibility
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarLeftFillingBoundaries m) :
    coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m x) =
      coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m x) := by
  apply Subtype.ext
  rfl

theorem injective_coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower
    (m : ℕ) [NeZero m] :
    Injective
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m) := by
  intro x y h
  apply injective_coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m
  apply injective_coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m
  rw [← coordinateUnlinkExteriorPlanarAllFilling_compatibility,
    ← coordinateUnlinkExteriorPlanarAllFilling_compatibility, h]

/-! ## Exact overlap and coverage -/

/-- A cross-piece equality occurs at the uniquely labelled lobe boundary. -/
theorem coordinateUnlinkExteriorPlanarAllFilling_cross
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightFilledFlower m)
    (y : CoordinateUnlinkExteriorPlanarLeftFillingDisks m)
    (hxy : coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m x =
      coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m y) :
    ∃ a : CoordinateUnlinkExteriorPlanarLeftFillingBoundaries m,
      coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m a = x ∧
        coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m a = y := by
  rcases y with ⟨i, w⟩
  have hval : x.1 = coordinateUnlinkExteriorPlanarLeftLobeMap m i w :=
    congrArg (fun q : ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m) ↦ q.1) hxy
  have hupper : ‖w.1 + 1‖ ≤ (1 / 8 : ℝ) := by
    have hw : dist w.1 (-1 : ℂ) ≤ 1 / 8 := by
      simpa only [mem_closedBall] using w.2
    simpa [Complex.dist_eq] using hw
  have hlower : (1 / 8 : ℝ) ≤ ‖w.1 + 1‖ := by
    have hx := x.2.2
    change (1 / 8 : ℝ) ≤ ‖x.1 ^ m + 1‖ at hx
    rw [hval, coordinateUnlinkExteriorPlanarLeftLobeMap_pow] at hx
    exact hx
  let b : CoordinateUnlinkExteriorPlanarLeftCharacterBoundary :=
    ⟨w.1, by
      rw [mem_sphere, Complex.dist_eq]
      have hadd : w.1 - (-1 : ℂ) = w.1 + 1 := by ring
      rw [hadd]
      exact le_antisymm hupper hlower⟩
  refine ⟨(i, b), ?_, ?_⟩
  · apply Subtype.ext
    exact hval.symm
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

/-- The right-filled old piece and all labelled left disks cover the whole outer polynomial
disk. -/
theorem range_coordinateUnlinkExteriorPlanarAllFilling_union
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m) ∪
        range (coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m) = univ := by
  rw [eq_univ_iff_forall]
  intro z
  rcases le_total (1 / 8 : ℝ) ‖z.1 ^ m + 1‖ with hlower | hupper
  · left
    exact ⟨⟨z.1, z.2, hlower⟩, by apply Subtype.ext; rfl⟩
  · right
    have hzlobes : z.1 ∈ coordinateUnlinkExteriorPlanarLeftLobesSet m := hupper
    rw [← iUnion_range_coordinateUnlinkExteriorPlanarLeftLobeMap m] at hzlobes
    simp only [Set.mem_iUnion, Set.mem_range] at hzlobes
    obtain ⟨a, w, hw⟩ := hzlobes
    exact ⟨(a, w), by
      apply Subtype.ext
      exact hw⟩

/-! ## Pushout recognition -/

/-- Attach all left lobe disks simultaneously to the right-filled flower. -/
abbrev CoordinateUnlinkExteriorPlanarAllFilledPushout
    (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)

/-- Filling the connected right hole and all `m` left holes gives exactly the outer polynomial
disk. -/
def coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarAllFilledPushout m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m) := by
  let _ : CompactSpace (CoordinateUnlinkExteriorPlanarRightFilledFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarRightFilledFlower m
  exact topologicalPushoutHomeomorph
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)
    (coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m)
    (coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m)
    (coordinateUnlinkExteriorPlanarAllFilling_compatibility m)
    (injective_coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
    (injective_coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m)
    (injective_coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m)
    (coordinateUnlinkExteriorPlanarAllFilling_cross m)
    (range_coordinateUnlinkExteriorPlanarAllFilling_union m)

@[simp]
theorem coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightFilledFlower m) :
    coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) x) =
      coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m x := by
  let _ : CompactSpace (CoordinateUnlinkExteriorPlanarRightFilledFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarRightFilledFlower m
  simp [coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph]

@[simp]
theorem coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (y : CoordinateUnlinkExteriorPlanarLeftFillingDisks m) :
    coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) y) =
      coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m y := by
  let _ : CompactSpace (CoordinateUnlinkExteriorPlanarRightFilledFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarRightFilledFlower m
  simp [coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph]

end SplittingSpheres
