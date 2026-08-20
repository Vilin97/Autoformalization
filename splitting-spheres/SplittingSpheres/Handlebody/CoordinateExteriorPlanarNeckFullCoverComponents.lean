/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckFullCoverSeparation

/-!
# Components detected by a lifted equator in the full unlink power cover

The selected lifted equator has two open, disjoint, nonempty displayed sides.  This file records
the strongest connected-component consequences which need no connectedness assertion for those
sides: opposite-side points lie in distinct relative connected components, every relative
component stays in its displayed side, and the connected components of the complement split as
the sigma of the connected components of the two restricted sides.

If either displayed side is separately proved preconnected, its relative connected component is
identified conditionally.  No assertion that a side is connected, that there are exactly two
components, or that a displayed side is a whole compact neck-star piece is made.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open Set.Notation

namespace SplittingSpheres

/-! ## Restricted sides -/

/-- The selected left side, regarded inside the complement of the selected equator lift. -/
def coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideRestrict
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (↑((range (equatorUnlinkPowerLift m a))ᶜ)) :=
  (range (equatorUnlinkPowerLift m a))ᶜ ↓∩
    coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a

/-- The remainder side, regarded inside the complement of the selected equator lift. -/
def coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideRestrict
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (↑((range (equatorUnlinkPowerLift m a))ᶜ)) :=
  (range (equatorUnlinkPowerLift m a))ᶜ ↓∩
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a

/-- The remainder side is also clopen inside the selected-lift complement. -/
theorem isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_restrict
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsClopen
      (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideRestrict m a) := by
  let C := (range (equatorUnlinkPowerLift m a))ᶜ
  let L := coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a
  let R := coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a
  have heq : (C ↓∩ R : Set (↑C)) = (C ↓∩ L : Set (↑C))ᶜ := by
    ext z
    have hzcover := congrArg
      (fun s : Set (StandardUnlinkPowerPullback m) ↦ z.1 ∈ s)
      (union_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a)
    have hzdisjoint := Set.disjoint_left.1
      (disjoint_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a)
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hzcover ⊢
    constructor
    · intro hzR hzL
      exact hzdisjoint hzL hzR
    · intro hzL
      rcases hzcover.mpr z.2 with hzL' | hzR
      · exact False.elim (hzL hzL')
      · exact hzR
  change IsClopen (C ↓∩ R)
  rw [heq]
  exact
    (isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_restrict m a).compl

theorem coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_subset_complement
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a ⊆
      (range (equatorUnlinkPowerLift m a))ᶜ := by
  intro x hx
  rw [← union_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a]
  exact Or.inl hx

theorem coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_subset_complement
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a ⊆
      (range (equatorUnlinkPowerLift m a))ᶜ := by
  intro x hx
  rw [← union_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a]
  exact Or.inr hx

/-! ## Relative connected components -/

/-- A relative connected component meeting the selected left side stays in that side. -/
theorem connectedComponentIn_subset_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : StandardUnlinkPowerPullback m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a) :
    connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ x ⊆
      coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a := by
  let C := (range (equatorUnlinkPowerLift m a))ᶜ
  let L := coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a
  have hxC : x ∈ C :=
    coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_subset_complement m a hx
  let xs : ↑C := ⟨x, hxC⟩
  intro y hy
  rw [connectedComponentIn_eq_image hxC] at hy
  obtain ⟨ys, hys, rfl⟩ := hy
  have hxs : xs ∈ C ↓∩ L := hx
  exact
    (isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_restrict m a)
      |>.connectedComponent_subset hxs hys

/-- A relative connected component meeting the remainder side stays in that side. -/
theorem connectedComponentIn_subset_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : StandardUnlinkPowerPullback m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) :
    connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ x ⊆
      coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a := by
  let C := (range (equatorUnlinkPowerLift m a))ᶜ
  let R := coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a
  have hxC : x ∈ C :=
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_subset_complement m a hx
  let xs : ↑C := ⟨x, hxC⟩
  intro y hy
  rw [connectedComponentIn_eq_image hxC] at hy
  obtain ⟨ys, hys, rfl⟩ := hy
  have hxs : xs ∈ C ↓∩ R := hx
  exact
    (isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_restrict m a)
      |>.connectedComponent_subset hxs hys

/-- Points on the two displayed sides lie in distinct relative connected components. -/
theorem connectedComponentIn_ne_of_mem_coordinateUnlinkExteriorPlanarFullCoverEquatorSides
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x y : StandardUnlinkPowerPullback m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)
    (hy : y ∈ coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) :
    connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ x ≠
      connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ y := by
  intro hxy
  have hyC : y ∈ (range (equatorUnlinkPowerLift m a))ᶜ :=
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_subset_complement m a hy
  have hyComponent :
      y ∈ connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ y :=
    mem_connectedComponentIn hyC
  have hyLeft : y ∈ coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a :=
    connectedComponentIn_subset_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
      m a x hx (hxy.symm ▸ hyComponent)
  exact Set.disjoint_left.1
    (disjoint_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a) hyLeft hy

/-! ## Conditional component identifications -/

/-- If the selected left side is preconnected, it is the entire relative component of each of
its points. -/
theorem
    connectedComponentIn_eq_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_of_isPreconnected
    (m : ℕ) [NeZero m] (a : ZMod m)
    (hleft : IsPreconnected
      (coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a))
    (x : StandardUnlinkPowerPullback m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a) :
    connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ x =
      coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a := by
  apply Subset.antisymm
  · exact
      connectedComponentIn_subset_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
        m a x hx
  · exact hleft.subset_connectedComponentIn hx
      (coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_subset_complement m a)

/-- If the remainder side is preconnected, it is the entire relative component of each of its
points. -/
theorem
    connectedComponentIn_eq_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_of_isPreconnected
    (m : ℕ) [NeZero m] (a : ZMod m)
    (hrest : IsPreconnected
      (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a))
    (x : StandardUnlinkPowerPullback m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) :
    connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ x =
      coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a := by
  apply Subset.antisymm
  · exact
      connectedComponentIn_subset_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
        m a x hx
  · exact hrest.subset_connectedComponentIn hx
      (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_subset_complement m a)

/-! ## The exact component partition -/

/-- Index the two restricted sides by `Fin 2`: index `0` is the selected left side and index `1`
is the remainder side. -/
def coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide
    (m : ℕ) [NeZero m] (a : ZMod m) (i : Fin 2) :
    Set (↑((range (equatorUnlinkPowerLift m a))ᶜ)) :=
  if i = 0 then
    coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideRestrict m a
  else
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideRestrict m a

@[simp]
theorem coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide_zero
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide m a 0 =
      coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideRestrict m a := by
  simp [coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide]

@[simp]
theorem coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide_one
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide m a 1 =
      coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideRestrict m a := by
  simp [coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide]

/-- The selected-lift complement has at least two connected components.  This deliberately
states only `Nontrivial`, not an exact component count. -/
theorem nontrivial_connectedComponents_coordinateUnlinkExteriorPlanarFullCoverEquatorComplement
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Nontrivial
      (ConnectedComponents
        (↑((range (equatorUnlinkPowerLift m a))ᶜ))) := by
  obtain ⟨x, hx⟩ :=
    coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_nonempty m a
  obtain ⟨y, hy⟩ :=
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_nonempty m a
  have hxC : x ∈ (range (equatorUnlinkPowerLift m a))ᶜ :=
    coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_subset_complement m a hx
  have hyC : y ∈ (range (equatorUnlinkPowerLift m a))ᶜ :=
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_subset_complement m a hy
  let xs : ↑((range (equatorUnlinkPowerLift m a))ᶜ) := ⟨x, hxC⟩
  let ys : ↑((range (equatorUnlinkPowerLift m a))ᶜ) := ⟨y, hyC⟩
  refine ⟨⟨ConnectedComponents.mk xs, ConnectedComponents.mk ys, ?_⟩⟩
  rw [ConnectedComponents.coe_ne_coe]
  intro hcomponents
  have himage :
      ((fun z : ↑((range (equatorUnlinkPowerLift m a))ᶜ) ↦ z.1) ''
          connectedComponent xs) =
        ((fun z : ↑((range (equatorUnlinkPowerLift m a))ᶜ) ↦ z.1) ''
          connectedComponent ys) := congrArg _ hcomponents
  have hrelative :
      connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ x =
        connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ y := by
    simpa [connectedComponentIn_eq_image hxC,
      connectedComponentIn_eq_image hyC, xs, ys] using himage
  exact
    connectedComponentIn_ne_of_mem_coordinateUnlinkExteriorPlanarFullCoverEquatorSides
      m a x y hx hy hrelative

/-- The components of the selected-lift complement are exactly partitioned by the two displayed
sides.  Each sigma fiber is still the possibly nontrivial component space of that side. -/
noncomputable def
    coordinateUnlinkExteriorPlanarFullCoverEquatorConnectedComponentsEquivRestrictedSides
    (m : ℕ) [NeZero m] (a : ZMod m) :
    ConnectedComponents (↑((range (equatorUnlinkPowerLift m a))ᶜ)) ≃
      Σ i : Fin 2,
        ConnectedComponents
          (coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide m a i) := by
  classical
  apply ConnectedComponents.equivOfIsClopen
  · intro i
    fin_cases i
    · simpa [coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideRestrict] using
        isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_restrict m a
    · simpa using
        isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_restrict m a
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint
        ((range (equatorUnlinkPowerLift m a))ᶜ ↓∩
          coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)
        ((range (equatorUnlinkPowerLift m a))ᶜ ↓∩
          coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a)
      exact
        (disjoint_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a).preimage
          (Subtype.val :
            ↑((range (equatorUnlinkPowerLift m a))ᶜ) →
              StandardUnlinkPowerPullback m)
    · change Disjoint
        ((range (equatorUnlinkPowerLift m a))ᶜ ↓∩
          coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a)
        ((range (equatorUnlinkPowerLift m a))ᶜ ↓∩
          coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)
      exact
        ((disjoint_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a).preimage
          (Subtype.val :
            ↑((range (equatorUnlinkPowerLift m a))ᶜ) →
              StandardUnlinkPowerPullback m)).symm
    · exact (hij rfl).elim
  · ext z
    constructor
    · exact fun _ ↦ mem_univ z
    · intro _
      have hzcover := congrArg
        (fun s : Set (StandardUnlinkPowerPullback m) ↦ z.1 ∈ s)
        (union_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a)
      rcases hzcover.mpr z.2 with hzLeft | hzRest
      · exact mem_iUnion.mpr ⟨0, by
          simpa [coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideRestrict] using hzLeft⟩
      · exact mem_iUnion.mpr ⟨1, by
          simpa [coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideRestrict] using hzRest⟩

end SplittingSpheres
