/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStrictCoreRestPaths
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckFullCoverComponents

/-!
# Exact components of a lifted-equator complement in the full unlink power cover

This file proves that the two displayed sides of the complement of one lifted equator are
path connected.  The restricted full-cover maps identify them with the exact intersections
of the planar neck-star strict core with, respectively, the selected left leaf and its
remainder.  The corresponding strict-core path-connectedness theorems therefore transport
back through the two side homeomorphisms.

It follows that each displayed side is one whole relative connected component and that the
connected-component space of the actual full-cover equator complement is equivalent to
`Fin 2`.  All statements remain confined to this strict full-cover complement.  No
ambient-isotopy invariance, assertion about an entire compact neck-star piece, or smooth
component classification is made.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open Set.Notation

namespace SplittingSpheres

/-! ## Path connectedness of the two actual full-cover sides -/

/-- The selected displayed left side of the full-cover equator complement is path connected. -/
theorem isPathConnected_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsPathConnected
      (coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  let E := coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideHomeomorph m a
  have htarget : IsPathConnected
      (coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage m a) := by
    rw [
      coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage_eq_strictCore_inter]
    exact
      isPathConnected_coordinateUnlinkExteriorPlanarNeckStarStrictLeftSide
        m (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
  let _ : PathConnectedSpace
      (↑(coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorLeftSideImage m a)) :=
    isPathConnected_iff_pathConnectedSpace.mp htarget
  exact E.symm.surjective.pathConnectedSpace E.symm.continuous

/-- The displayed remainder side of the full-cover equator complement is path connected. -/
theorem isPathConnected_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsPathConnected
      (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  let E := coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideHomeomorph m a
  have htarget : IsPathConnected
      (coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage m a) := by
    rw [
      coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage_eq_strictCore_inter]
    exact
      isPathConnected_coordinateUnlinkExteriorPlanarNeckStarStrictFiberRest
        m (a + coordinateUnlinkExteriorPlanarSmoothNeckShift m)
  let _ : PathConnectedSpace
      (↑(coordinateUnlinkExteriorPlanarFullCoverNeckStarEquatorRestSideImage m a)) :=
    isPathConnected_iff_pathConnectedSpace.mp htarget
  exact E.symm.surjective.pathConnectedSpace E.symm.continuous

/-- The selected displayed left side is preconnected. -/
theorem isPreconnected_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsPreconnected
      (coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a) :=
  (isPathConnected_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
    m a).isConnected.isPreconnected

/-- The displayed remainder side is preconnected. -/
theorem isPreconnected_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsPreconnected
      (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) :=
  (isPathConnected_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
    m a).isConnected.isPreconnected

/-! ## Unconditional relative-component identifications -/

/-- The relative component of any point on the selected left side is exactly that side. -/
theorem connectedComponentIn_eq_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : StandardUnlinkPowerPullback m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a) :
    connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ x =
      coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a :=
  connectedComponentIn_eq_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_of_isPreconnected
    m a
      (isPreconnected_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)
      x hx

/-- The relative component of any point on the remainder side is exactly that side. -/
theorem connectedComponentIn_eq_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : StandardUnlinkPowerPullback m)
    (hx : x ∈ coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a) :
    connectedComponentIn (range (equatorUnlinkPowerLift m a))ᶜ x =
      coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a :=
  connectedComponentIn_eq_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_of_isPreconnected
    m a
      (isPreconnected_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a)
      x hx

/-! ## The exact two-component space -/

/-- The connected components of the actual selected-lift complement are indexed exactly by
the selected left side and the remainder side. -/
noncomputable def
    coordinateUnlinkExteriorPlanarFullCoverEquatorConnectedComponentsEquivFinTwo
    (m : ℕ) [NeZero m] (a : ZMod m) :
    ConnectedComponents
        (↑((range (equatorUnlinkPowerLift m a))ᶜ)) ≃ Fin 2 := by
  let C := (range (equatorUnlinkPowerLift m a))ᶜ
  let U : Fin 2 → Set (↑C) :=
    coordinateUnlinkExteriorPlanarFullCoverEquatorRestrictedSide m a
  have hcl : ∀ i, IsClopen (U i) := by
    intro i
    fin_cases i
    · simpa [U,
        coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideRestrict] using
        isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_restrict m a
    · simpa [U] using
        isClopen_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_restrict m a
  have hdisj : Pairwise (Disjoint on U) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint
        (C ↓∩ coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)
        (C ↓∩ coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a)
      exact
        (disjoint_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a).preimage
          (Subtype.val : (↑C) → StandardUnlinkPowerPullback m)
    · change Disjoint
        (C ↓∩ coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide m a)
        (C ↓∩ coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide m a)
      exact
        ((disjoint_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a).preimage
          (Subtype.val : (↑C) → StandardUnlinkPowerPullback m)).symm
    · exact (hij rfl).elim
  have hunion : ⋃ i, U i = Set.univ := by
    ext z
    constructor
    · exact fun _ => mem_univ z
    · intro _
      have hzcover := congrArg
        (fun s : Set (StandardUnlinkPowerPullback m) => z.1 ∈ s)
        (union_coordinateUnlinkExteriorPlanarFullCoverEquatorSides m a)
      rcases hzcover.mpr z.2 with hzLeft | hzRest
      · exact mem_iUnion.mpr ⟨0, by
          simpa [U,
            coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideRestrict] using
              hzLeft⟩
      · exact mem_iUnion.mpr ⟨1, by
          simpa [U,
            coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideRestrict] using
              hzRest⟩
  have hconn : ∀ i, IsConnected (U i) := by
    intro i
    fin_cases i
    · simpa [U,
        coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSideRestrict] using
        ((isPathConnected_coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide
          m a).preimage_coe
            (coordinateUnlinkExteriorPlanarFullCoverEquatorLeftSide_subset_complement
              m a)).isConnected
    · simpa [U,
        coordinateUnlinkExteriorPlanarFullCoverEquatorRestSideRestrict] using
        ((isPathConnected_coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide
          m a).preimage_coe
            (coordinateUnlinkExteriorPlanarFullCoverEquatorRestSide_subset_complement
              m a)).isConnected
  exact ConnectedComponents.equivOfIsClopenOfIsConnected hcl hdisj hunion hconn

/-- The selected lifted equator has exactly two connected components in its actual
full-cover complement. -/
theorem natCard_connectedComponents_coordinateUnlinkExteriorPlanarFullCoverEquatorComplement
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Nat.card
        (ConnectedComponents
          (↑((range (equatorUnlinkPowerLift m a))ᶜ))) = 2 := by
  rw [Nat.card_congr
    (coordinateUnlinkExteriorPlanarFullCoverEquatorConnectedComponentsEquivFinTwo
      m a)]
  exact Nat.card_fin 2

end SplittingSpheres
