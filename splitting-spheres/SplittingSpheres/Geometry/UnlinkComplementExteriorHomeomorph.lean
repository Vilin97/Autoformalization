/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkComplement
public import SplittingSpheres.Geometry.UnlinkExteriorCollar
public import SplittingSpheres.Foundations.RadialDiffeomorph

/-!
# The open unlink complement and the interior of a tubular exterior

This file constructs an explicit homeomorphism from the complement of the frozen coordinate
unlink to the complement of the two closed coordinate tubes of radius `1 / 8`.  In each of the
two disjoint product tubes it preserves the `S²` coordinate and changes only the normal radius.
The radius change identifies `(0, 3/8)` with `(1/8, 3/8)` and is literally the identity from
radius `1/4` outwards, so the two local maps glue to the ambient identity.

Only a homeomorphism is asserted.  The concrete scalar change is piecewise linear at radius
`1/4`, so no smoothness claim is intended.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open TopologicalSpace

namespace SplittingSpheres

/-! ## A concrete homeomorphism of positive radius intervals -/

/-- Push a positive radius away from zero.  It is affine below `1/4` and the identity above it. -/
def unlinkEighthRadiusForward (t : ℝ) : ℝ :=
  max t ((1 / 8 : ℝ) + t / 2)

/-- The inverse radius change. -/
def unlinkEighthRadiusInverse (t : ℝ) : ℝ :=
  min t (2 * (t - (1 / 8 : ℝ)))

theorem unlinkEighthRadiusForward_of_le {t : ℝ} (ht : t ≤ 1 / 4) :
    unlinkEighthRadiusForward t = (1 / 8 : ℝ) + t / 2 := by
  rw [unlinkEighthRadiusForward, max_eq_right]
  linarith

theorem unlinkEighthRadiusForward_of_ge {t : ℝ} (ht : 1 / 4 ≤ t) :
    unlinkEighthRadiusForward t = t := by
  rw [unlinkEighthRadiusForward, max_eq_left]
  linarith

theorem unlinkEighthRadiusInverse_of_le {t : ℝ} (ht : t ≤ 1 / 4) :
    unlinkEighthRadiusInverse t = 2 * (t - (1 / 8 : ℝ)) := by
  rw [unlinkEighthRadiusInverse, min_eq_right]
  linarith

theorem unlinkEighthRadiusInverse_of_ge {t : ℝ} (ht : 1 / 4 ≤ t) :
    unlinkEighthRadiusInverse t = t := by
  rw [unlinkEighthRadiusInverse, min_eq_left]
  linarith

theorem continuous_unlinkEighthRadiusForward : Continuous unlinkEighthRadiusForward := by
  unfold unlinkEighthRadiusForward
  fun_prop

theorem continuous_unlinkEighthRadiusInverse : Continuous unlinkEighthRadiusInverse := by
  unfold unlinkEighthRadiusInverse
  fun_prop

theorem unlinkEighthRadiusForward_gt_eighth {t : ℝ} (ht : 0 < t) :
    1 / 8 < unlinkEighthRadiusForward t := by
  apply lt_of_lt_of_le (show (1 / 8 : ℝ) < 1 / 8 + t / 2 by linarith)
  exact le_max_right _ _

theorem unlinkEighthRadiusInverse_pos {t : ℝ} (ht : 1 / 8 < t) :
    0 < unlinkEighthRadiusInverse t := by
  rw [unlinkEighthRadiusInverse]
  exact lt_min (by linarith) (by linarith)

theorem unlinkEighthRadiusInverse_forward {t : ℝ} (_ht : 0 < t) :
    unlinkEighthRadiusInverse (unlinkEighthRadiusForward t) = t := by
  by_cases htc : t ≤ 1 / 4
  · rw [unlinkEighthRadiusForward_of_le htc,
      unlinkEighthRadiusInverse_of_le (by linarith)]
    ring
  · have hct : 1 / 4 ≤ t := le_of_not_ge htc
    rw [unlinkEighthRadiusForward_of_ge hct,
      unlinkEighthRadiusInverse_of_ge hct]

theorem unlinkEighthRadiusForward_inverse {t : ℝ} (_ht : 1 / 8 < t) :
    unlinkEighthRadiusForward (unlinkEighthRadiusInverse t) = t := by
  by_cases htc : t ≤ 1 / 4
  · rw [unlinkEighthRadiusInverse_of_le htc,
      unlinkEighthRadiusForward_of_le (by linarith)]
    ring
  · have hct : 1 / 4 ≤ t := le_of_not_ge htc
    rw [unlinkEighthRadiusInverse_of_ge hct,
      unlinkEighthRadiusForward_of_ge hct]

theorem unlinkEighthRadiusForward_lt_threeEighth_iff {t : ℝ} :
    unlinkEighthRadiusForward t < 3 / 8 ↔ t < 3 / 8 := by
  rw [unlinkEighthRadiusForward, max_lt_iff]
  constructor
  · exact fun h ↦ h.1
  · intro ht
    exact ⟨ht, by linarith⟩

theorem unlinkEighthRadiusInverse_lt_threeEighth_iff {t : ℝ} (_ht : 1 / 8 < t) :
    unlinkEighthRadiusInverse t < 3 / 8 ↔ t < 3 / 8 := by
  by_cases htc : t ≤ 1 / 4
  · rw [unlinkEighthRadiusInverse_of_le htc]
    constructor <;> intro <;> linarith
  · have hct : 1 / 4 ≤ t := le_of_not_ge htc
    rw [unlinkEighthRadiusInverse_of_ge hct]

/-- The concrete positive-radius homeomorphism used in both normal disks. -/
def unlinkEighthRadiusHomeomorph : Ioi (0 : ℝ) ≃ₜ Ioi (1 / 8 : ℝ) where
  toFun t := ⟨unlinkEighthRadiusForward t.1,
    unlinkEighthRadiusForward_gt_eighth t.2⟩
  invFun t := ⟨unlinkEighthRadiusInverse t.1,
    unlinkEighthRadiusInverse_pos t.2⟩
  left_inv t := Subtype.ext (unlinkEighthRadiusInverse_forward t.2)
  right_inv t := Subtype.ext (unlinkEighthRadiusForward_inverse t.2)
  continuous_toFun :=
    continuous_unlinkEighthRadiusForward.comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun :=
    continuous_unlinkEighthRadiusInverse.comp continuous_subtype_val |>.subtype_mk _

@[simp]
theorem unlinkEighthRadiusHomeomorph_coe (t : Ioi (0 : ℝ)) :
    (unlinkEighthRadiusHomeomorph t : ℝ) = unlinkEighthRadiusForward t.1 :=
  rfl

@[simp]
theorem unlinkEighthRadiusHomeomorph_symm_coe (t : Ioi (1 / 8 : ℝ)) :
    (unlinkEighthRadiusHomeomorph.symm t : ℝ) = unlinkEighthRadiusInverse t.1 :=
  rfl

/-! ## Radialization in the normal plane -/

/-- The part of the normal plane strictly outside the closed radius-`1/8` disk. -/
def unlinkNormalExteriorEighthOpens (i : Fin 2) : Opens UnlinkNormalPlane :=
  ⟨{v | 1 / 8 < ‖v - standardUnlinkNormalCenter i‖}, by
    exact isOpen_lt continuous_const
      (continuous_norm.comp (continuous_id.sub continuous_const))⟩

abbrev UnlinkNormalExteriorEighth (i : Fin 2) :=
  unlinkNormalExteriorEighthOpens i

@[simp]
theorem mem_unlinkNormalExteriorEighthOpens (i : Fin 2) (v : UnlinkNormalPlane) :
    v ∈ unlinkNormalExteriorEighthOpens i ↔
      1 / 8 < ‖v - standardUnlinkNormalCenter i‖ :=
  Iff.rfl

def unlinkNormalEighthForward (i : Fin 2) (v : UnlinkPuncturedNormalPlane i) :
    UnlinkNormalExteriorEighth i := by
  refine ⟨centeredRadialMap unlinkEighthRadiusForward
    (standardUnlinkNormalCenter i) v.1, ?_⟩
  rw [mem_unlinkNormalExteriorEighthOpens,
    norm_centeredRadialMap_sub_center unlinkEighthRadiusForward
      (standardUnlinkNormalCenter i)
      (unlinkPuncturedNormalPlane_coe_ne_center i v)
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 8)
        (unlinkEighthRadiusForward_gt_eighth
          (show 0 < ‖v.1 - standardUnlinkNormalCenter i‖ by
            exact norm_pos_iff.mpr (sub_ne_zero.mpr
              (unlinkPuncturedNormalPlane_coe_ne_center i v)))))]
  exact unlinkEighthRadiusForward_gt_eighth
    (norm_pos_iff.mpr (sub_ne_zero.mpr
      (unlinkPuncturedNormalPlane_coe_ne_center i v)))

theorem unlinkNormalExteriorEighth_ne_center (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i) :
    v.1 ≠ standardUnlinkNormalCenter i := by
  intro h
  have hv := (mem_unlinkNormalExteriorEighthOpens i v.1).mp v.2
  rw [h, sub_self, norm_zero] at hv
  norm_num at hv

def unlinkNormalEighthInverse (i : Fin 2) (v : UnlinkNormalExteriorEighth i) :
    UnlinkPuncturedNormalPlane i := by
  have hvne : v.1 ≠ standardUnlinkNormalCenter i :=
    unlinkNormalExteriorEighth_ne_center i v
  have hpos : 0 < unlinkEighthRadiusInverse
      ‖v.1 - standardUnlinkNormalCenter i‖ :=
    unlinkEighthRadiusInverse_pos
      ((mem_unlinkNormalExteriorEighthOpens i v.1).mp v.2)
  refine ⟨centeredRadialMap unlinkEighthRadiusInverse
    (standardUnlinkNormalCenter i) v.1, ?_⟩
  intro hy
  have hnorm := norm_centeredRadialMap_sub_center unlinkEighthRadiusInverse
    (standardUnlinkNormalCenter i) hvne hpos
  have hy' : centeredRadialMap unlinkEighthRadiusInverse
      (standardUnlinkNormalCenter i) v.1 = standardUnlinkNormalCenter i := by
    simpa only [mem_singleton_iff] using hy
  rw [hy', sub_self, norm_zero] at hnorm
  linarith

@[simp]
theorem unlinkNormalEighthForward_coe (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i) :
    (unlinkNormalEighthForward i v : UnlinkNormalPlane) =
      centeredRadialMap unlinkEighthRadiusForward
        (standardUnlinkNormalCenter i) v.1 :=
  rfl

@[simp]
theorem unlinkNormalEighthInverse_coe (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i) :
    (unlinkNormalEighthInverse i v : UnlinkNormalPlane) =
      centeredRadialMap unlinkEighthRadiusInverse
        (standardUnlinkNormalCenter i) v.1 :=
  rfl

theorem norm_unlinkNormalEighthForward_sub_center (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i) :
    ‖(unlinkNormalEighthForward i v : UnlinkNormalPlane) -
        standardUnlinkNormalCenter i‖ =
      unlinkEighthRadiusForward ‖v.1 - standardUnlinkNormalCenter i‖ := by
  rw [unlinkNormalEighthForward_coe]
  exact norm_centeredRadialMap_sub_center unlinkEighthRadiusForward
    (standardUnlinkNormalCenter i)
    (unlinkPuncturedNormalPlane_coe_ne_center i v)
    (lt_trans (by norm_num : (0 : ℝ) < 1 / 8)
      (unlinkEighthRadiusForward_gt_eighth
        (norm_pos_iff.mpr (sub_ne_zero.mpr
          (unlinkPuncturedNormalPlane_coe_ne_center i v)))))

theorem norm_unlinkNormalEighthInverse_sub_center (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i) :
    ‖(unlinkNormalEighthInverse i v : UnlinkNormalPlane) -
        standardUnlinkNormalCenter i‖ =
      unlinkEighthRadiusInverse ‖v.1 - standardUnlinkNormalCenter i‖ := by
  rw [unlinkNormalEighthInverse_coe]
  exact norm_centeredRadialMap_sub_center unlinkEighthRadiusInverse
    (standardUnlinkNormalCenter i)
    (unlinkNormalExteriorEighth_ne_center i v)
    (unlinkEighthRadiusInverse_pos
      ((mem_unlinkNormalExteriorEighthOpens i v.1).mp v.2))

private theorem centeredRadialMap_comp_of_inverse
    (f g : ℝ → ℝ) (center x : UnlinkNormalPlane) (hx : x ≠ center)
    (hfpos : 0 < f ‖x - center‖) (hgf : g (f ‖x - center‖) = ‖x - center‖) :
    centeredRadialMap g center (centeredRadialMap f center x) = x := by
  have hnorm : ‖centeredRadialMap f center x - center‖ = f ‖x - center‖ :=
    norm_centeredRadialMap_sub_center f center hx hfpos
  have hne : centeredRadialMap f center x ≠ center := by
    intro h
    rw [h, sub_self, norm_zero] at hnorm
    linarith
  rw [centeredRadialMap_of_ne g center hne, hnorm, hgf,
    centeredRadialMap_sub_center f center hx, smul_smul]
  have hrne : ‖x - center‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hfne : f ‖x - center‖ ≠ 0 := hfpos.ne'
  field_simp
  simp

theorem unlinkNormalEighthInverse_forward (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i) :
    unlinkNormalEighthInverse i (unlinkNormalEighthForward i v) = v := by
  apply Subtype.ext
  rw [unlinkNormalEighthInverse_coe, unlinkNormalEighthForward_coe]
  apply centeredRadialMap_comp_of_inverse
  · exact unlinkPuncturedNormalPlane_coe_ne_center i v
  · exact lt_trans (by norm_num : (0 : ℝ) < 1 / 8)
      (unlinkEighthRadiusForward_gt_eighth
        (norm_pos_iff.mpr (sub_ne_zero.mpr
          (unlinkPuncturedNormalPlane_coe_ne_center i v))))
  · exact unlinkEighthRadiusInverse_forward
      (norm_pos_iff.mpr (sub_ne_zero.mpr
        (unlinkPuncturedNormalPlane_coe_ne_center i v)))

theorem unlinkNormalEighthForward_inverse (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i) :
    unlinkNormalEighthForward i (unlinkNormalEighthInverse i v) = v := by
  apply Subtype.ext
  rw [unlinkNormalEighthForward_coe, unlinkNormalEighthInverse_coe]
  apply centeredRadialMap_comp_of_inverse
  · exact unlinkNormalExteriorEighth_ne_center i v
  · exact unlinkEighthRadiusInverse_pos
      ((mem_unlinkNormalExteriorEighthOpens i v.1).mp v.2)
  · exact unlinkEighthRadiusForward_inverse
      ((mem_unlinkNormalExteriorEighthOpens i v.1).mp v.2)

theorem continuous_unlinkNormalEighthForward (i : Fin 2) :
    Continuous (unlinkNormalEighthForward i) := by
  apply Continuous.subtype_mk
  have hd : Continuous (fun v : UnlinkPuncturedNormalPlane i ↦
      v.1 - standardUnlinkNormalCenter i) := by fun_prop
  have hn : Continuous (fun v : UnlinkPuncturedNormalPlane i ↦
      ‖v.1 - standardUnlinkNormalCenter i‖) := continuous_norm.comp hd
  have hnne : ∀ v : UnlinkPuncturedNormalPlane i,
      ‖v.1 - standardUnlinkNormalCenter i‖ ≠ 0 := fun v ↦
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr
      (unlinkPuncturedNormalPlane_coe_ne_center i v))
  have hnum : Continuous (fun v : UnlinkPuncturedNormalPlane i ↦
      unlinkEighthRadiusForward ‖v.1 - standardUnlinkNormalCenter i‖) :=
    continuous_unlinkEighthRadiusForward.comp hn
  have hformula : (fun v : UnlinkPuncturedNormalPlane i ↦
      centeredRadialMap unlinkEighthRadiusForward
        (standardUnlinkNormalCenter i) v.1) =
      fun v ↦ standardUnlinkNormalCenter i +
        (unlinkEighthRadiusForward ‖v.1 - standardUnlinkNormalCenter i‖ /
          ‖v.1 - standardUnlinkNormalCenter i‖) •
            (v.1 - standardUnlinkNormalCenter i) := by
    funext v
    exact centeredRadialMap_of_ne _ _
      (unlinkPuncturedNormalPlane_coe_ne_center i v)
  change Continuous (fun v : UnlinkPuncturedNormalPlane i ↦
    centeredRadialMap unlinkEighthRadiusForward
      (standardUnlinkNormalCenter i) v.1)
  rw [hformula]
  exact continuous_const.add ((hnum.div hn hnne).smul hd)

theorem continuous_unlinkNormalEighthInverse (i : Fin 2) :
    Continuous (unlinkNormalEighthInverse i) := by
  apply Continuous.subtype_mk
  have hd : Continuous (fun v : UnlinkNormalExteriorEighth i ↦
      v.1 - standardUnlinkNormalCenter i) := by fun_prop
  have hn : Continuous (fun v : UnlinkNormalExteriorEighth i ↦
      ‖v.1 - standardUnlinkNormalCenter i‖) := continuous_norm.comp hd
  have hnne : ∀ v : UnlinkNormalExteriorEighth i,
      ‖v.1 - standardUnlinkNormalCenter i‖ ≠ 0 := fun v ↦
    ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1 / 8)
      ((mem_unlinkNormalExteriorEighthOpens i v.1).mp v.2))
  have hnum : Continuous (fun v : UnlinkNormalExteriorEighth i ↦
      unlinkEighthRadiusInverse ‖v.1 - standardUnlinkNormalCenter i‖) :=
    continuous_unlinkEighthRadiusInverse.comp hn
  have hformula : (fun v : UnlinkNormalExteriorEighth i ↦
      centeredRadialMap unlinkEighthRadiusInverse
        (standardUnlinkNormalCenter i) v.1) =
      fun v ↦ standardUnlinkNormalCenter i +
        (unlinkEighthRadiusInverse ‖v.1 - standardUnlinkNormalCenter i‖ /
          ‖v.1 - standardUnlinkNormalCenter i‖) •
            (v.1 - standardUnlinkNormalCenter i) := by
    funext v
    exact centeredRadialMap_of_ne _ _
      (unlinkNormalExteriorEighth_ne_center i v)
  change Continuous (fun v : UnlinkNormalExteriorEighth i ↦
    centeredRadialMap unlinkEighthRadiusInverse
      (standardUnlinkNormalCenter i) v.1)
  rw [hformula]
  exact continuous_const.add ((hnum.div hn hnne).smul hd)

/-- Radial homeomorphism from the punctured normal plane to the exterior of its closed
radius-`1/8` disk. -/
def unlinkNormalEighthHomeomorph (i : Fin 2) :
    UnlinkPuncturedNormalPlane i ≃ₜ UnlinkNormalExteriorEighth i where
  toFun := unlinkNormalEighthForward i
  invFun := unlinkNormalEighthInverse i
  left_inv := unlinkNormalEighthInverse_forward i
  right_inv := unlinkNormalEighthForward_inverse i
  continuous_toFun := continuous_unlinkNormalEighthForward i
  continuous_invFun := continuous_unlinkNormalEighthInverse i

/-! ## Restriction to the concrete normal disks -/

/-- The punctured radius-`3/8` normal disk. -/
def unlinkPuncturedNormalThreeEighthDiskOpens (i : Fin 2) :
    Opens (UnlinkNormalDisk i (3 / 8 : ℝ)) :=
  ⟨{v | v.1 ≠ standardUnlinkNormalCenter i}, by
    change IsOpen ((fun v : UnlinkNormalDisk i (3 / 8 : ℝ) ↦ v.1) ⁻¹'
      {standardUnlinkNormalCenter i}ᶜ)
    exact isOpen_compl_singleton.preimage continuous_subtype_val⟩

abbrev UnlinkPuncturedNormalThreeEighthDisk (i : Fin 2) :=
  unlinkPuncturedNormalThreeEighthDiskOpens i

/-- The radius-`3/8` normal disk with its closed radius-`1/8` core removed. -/
def unlinkExteriorEighthNormalThreeEighthDiskOpens (i : Fin 2) :
    Opens (UnlinkNormalDisk i (3 / 8 : ℝ)) :=
  ⟨{v | 1 / 8 < ‖v.1 - standardUnlinkNormalCenter i‖}, by
    exact isOpen_lt continuous_const
      (continuous_norm.comp (continuous_subtype_val.sub continuous_const))⟩

abbrev UnlinkExteriorEighthNormalThreeEighthDisk (i : Fin 2) :=
  unlinkExteriorEighthNormalThreeEighthDiskOpens i

def puncturedNormalThreeEighthDiskToPlane (i : Fin 2)
    (v : UnlinkPuncturedNormalThreeEighthDisk i) :
    UnlinkPuncturedNormalPlane i :=
  ⟨v.1.1, v.2⟩

def exteriorEighthNormalThreeEighthDiskToPlane (i : Fin 2)
    (v : UnlinkExteriorEighthNormalThreeEighthDisk i) :
    UnlinkNormalExteriorEighth i :=
  ⟨v.1.1, v.2⟩

theorem continuous_puncturedNormalThreeEighthDiskToPlane (i : Fin 2) :
    Continuous (puncturedNormalThreeEighthDiskToPlane i) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem continuous_exteriorEighthNormalThreeEighthDiskToPlane (i : Fin 2) :
    Continuous (exteriorEighthNormalThreeEighthDiskToPlane i) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The radial normal-plane homeomorphism restricted to the concrete product-tube disk. -/
def unlinkNormalEighthDiskHomeomorph (i : Fin 2) :
    UnlinkPuncturedNormalThreeEighthDisk i ≃ₜ
      UnlinkExteriorEighthNormalThreeEighthDisk i where
  toFun v := by
    let u := puncturedNormalThreeEighthDiskToPlane i v
    let w := unlinkNormalEighthForward i u
    have hvR : ‖v.1.1 - standardUnlinkNormalCenter i‖ < 3 / 8 := by
      have h := v.1.2
      change dist v.1.1 (standardUnlinkNormalCenter i) < 3 / 8 at h
      simpa only [dist_eq_norm] using h
    have hwR : ‖(w : UnlinkNormalPlane) - standardUnlinkNormalCenter i‖ < 3 / 8 := by
      change ‖(unlinkNormalEighthForward i u : UnlinkNormalPlane) -
        standardUnlinkNormalCenter i‖ < 3 / 8
      rw [norm_unlinkNormalEighthForward_sub_center]
      exact unlinkEighthRadiusForward_lt_threeEighth_iff.mpr hvR
    exact ⟨⟨w.1, by
      change dist w.1 (standardUnlinkNormalCenter i) < 3 / 8
      simpa only [dist_eq_norm] using hwR⟩, w.2⟩
  invFun v := by
    let u := exteriorEighthNormalThreeEighthDiskToPlane i v
    let w := unlinkNormalEighthInverse i u
    have hvR : ‖v.1.1 - standardUnlinkNormalCenter i‖ < 3 / 8 := by
      have h := v.1.2
      change dist v.1.1 (standardUnlinkNormalCenter i) < 3 / 8 at h
      simpa only [dist_eq_norm] using h
    have hvEight : 1 / 8 < ‖v.1.1 - standardUnlinkNormalCenter i‖ := v.2
    have hwR : ‖(w : UnlinkNormalPlane) - standardUnlinkNormalCenter i‖ < 3 / 8 := by
      change ‖(unlinkNormalEighthInverse i u : UnlinkNormalPlane) -
        standardUnlinkNormalCenter i‖ < 3 / 8
      rw [norm_unlinkNormalEighthInverse_sub_center]
      exact (unlinkEighthRadiusInverse_lt_threeEighth_iff hvEight).mpr hvR
    exact ⟨⟨w.1, by
      change dist w.1 (standardUnlinkNormalCenter i) < 3 / 8
      simpa only [dist_eq_norm] using hwR⟩, w.2⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change (unlinkNormalEighthInverse i
      (unlinkNormalEighthForward i
        (puncturedNormalThreeEighthDiskToPlane i v)) : UnlinkNormalPlane) = v.1.1
    exact congrArg Subtype.val
      (unlinkNormalEighthInverse_forward i
        (puncturedNormalThreeEighthDiskToPlane i v))
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change (unlinkNormalEighthForward i
      (unlinkNormalEighthInverse i
        (exteriorEighthNormalThreeEighthDiskToPlane i v)) : UnlinkNormalPlane) = v.1.1
    exact congrArg Subtype.val
      (unlinkNormalEighthForward_inverse i
        (exteriorEighthNormalThreeEighthDiskToPlane i v))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      ((continuous_unlinkNormalEighthForward i).comp
        (continuous_puncturedNormalThreeEighthDiskToPlane i))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      ((continuous_unlinkNormalEighthInverse i).comp
        (continuous_exteriorEighthNormalThreeEighthDiskToPlane i))

@[simp]
theorem unlinkNormalEighthDiskHomeomorph_coe (i : Fin 2)
    (v : UnlinkPuncturedNormalThreeEighthDisk i) :
    ((unlinkNormalEighthDiskHomeomorph i v).1.1 : UnlinkNormalPlane) =
      unlinkNormalEighthForward i (puncturedNormalThreeEighthDiskToPlane i v) :=
  rfl

@[simp]
theorem unlinkNormalEighthDiskHomeomorph_symm_coe (i : Fin 2)
    (v : UnlinkExteriorEighthNormalThreeEighthDisk i) :
    (((unlinkNormalEighthDiskHomeomorph i).symm v).1.1 : UnlinkNormalPlane) =
      unlinkNormalEighthInverse i
        (exteriorEighthNormalThreeEighthDiskToPlane i v) :=
  rfl

theorem unlinkNormalEighthForward_eq_self_of_quarter_le (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i)
    (hv : 1 / 4 ≤ ‖v.1 - standardUnlinkNormalCenter i‖) :
    (unlinkNormalEighthForward i v : UnlinkNormalPlane) = v.1 := by
  rw [unlinkNormalEighthForward_coe]
  apply centeredRadialMap_eq_self_of_radius_eq
  exact unlinkEighthRadiusForward_of_ge hv

theorem unlinkNormalEighthInverse_eq_self_of_quarter_le (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i)
    (hv : 1 / 4 ≤ ‖v.1 - standardUnlinkNormalCenter i‖) :
    (unlinkNormalEighthInverse i v : UnlinkNormalPlane) = v.1 := by
  rw [unlinkNormalEighthInverse_coe]
  apply centeredRadialMap_eq_self_of_radius_eq
  exact unlinkEighthRadiusInverse_of_ge hv

theorem unlinkNormalEighthDiskHomeomorph_eq_self_of_quarter_le (i : Fin 2)
    (v : UnlinkPuncturedNormalThreeEighthDisk i)
    (hv : 1 / 4 ≤ ‖v.1.1 - standardUnlinkNormalCenter i‖) :
    (unlinkNormalEighthDiskHomeomorph i v).1 = v.1 := by
  apply Subtype.ext
  rw [unlinkNormalEighthDiskHomeomorph_coe]
  exact unlinkNormalEighthForward_eq_self_of_quarter_le i _ hv

theorem unlinkNormalEighthDiskHomeomorph_symm_eq_self_of_quarter_le (i : Fin 2)
    (v : UnlinkExteriorEighthNormalThreeEighthDisk i)
    (hv : 1 / 4 ≤ ‖v.1.1 - standardUnlinkNormalCenter i‖) :
    ((unlinkNormalEighthDiskHomeomorph i).symm v).1 = v.1 := by
  apply Subtype.ext
  rw [unlinkNormalEighthDiskHomeomorph_symm_coe]
  exact unlinkNormalEighthInverse_eq_self_of_quarter_le i _ hv

/-! ## Product-tube homeomorphisms -/

/-- The part of the radius-`3/8` tube strictly outside the closed radius-`1/8` tube. -/
def standardUnlinkExteriorEighthTubeOpens (i : Fin 2) :
    Opens (StandardUnlinkOpenTubeSpace i (3 / 8 : ℝ)) :=
  ⟨{q | 1 / 8 <
      ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter i‖}, by
    exact isOpen_lt continuous_const
      (continuous_norm.comp
        ((continuous_standardUnlinkNormalProjection.comp continuous_subtype_val).sub
          continuous_const))⟩

abbrev StandardUnlinkExteriorEighthTube (i : Fin 2) :=
  standardUnlinkExteriorEighthTubeOpens i

/-- Product coordinates on the punctured radius-`3/8` tube. -/
def standardUnlinkPuncturedTubeProductHomeomorph (i : Fin 2) :
    StandardUnlinkPuncturedTube i (3 / 8 : ℝ) ≃ₜ
      Sphere 2 × UnlinkPuncturedNormalThreeEighthDisk i where
  toFun q := by
    let p := (standardUnlinkOpenTubeHomeomorph i (by norm_num : (3 / 8 : ℝ) < 1 / 2)).symm q.1
    exact (p.1, ⟨p.2, by
      change p.2.1 ≠ standardUnlinkNormalCenter i
      rw [standardUnlinkOpenTubeHomeomorph_symm_snd_coe]
      exact q.2⟩)
  invFun p := by
    let q := standardUnlinkOpenTubeHomeomorph i
      (by norm_num : (3 / 8 : ℝ) < 1 / 2) (p.1, p.2.1)
    exact ⟨q, by
      change standardUnlinkNormalProjection q.1 ≠ standardUnlinkNormalCenter i
      rw [standardUnlinkNormalProjection_openTubeHomeomorph]
      exact p.2.2⟩
  left_inv q := by
    apply Subtype.ext
    exact (standardUnlinkOpenTubeHomeomorph i
      (by norm_num : (3 / 8 : ℝ) < 1 / 2)).apply_symm_apply q.1
  right_inv p := by
    dsimp only
    have h := (standardUnlinkOpenTubeHomeomorph i
      (by norm_num : (3 / 8 : ℝ) < 1 / 2)).symm_apply_apply (p.1, p.2.1)
    have hfst := congrArg
      (fun z : Sphere 2 × UnlinkNormalDisk i (3 / 8 : ℝ) ↦ z.1) h
    have hsnd := congrArg
      (fun z : Sphere 2 × UnlinkNormalDisk i (3 / 8 : ℝ) ↦ z.2) h
    apply Prod.ext
    · exact hfst
    · exact Subtype.ext hsnd
  continuous_toFun := by
    have hp : Continuous (fun q : StandardUnlinkPuncturedTube i (3 / 8 : ℝ) ↦
        (standardUnlinkOpenTubeHomeomorph i
          (by norm_num : (3 / 8 : ℝ) < 1 / 2)).symm q.1) :=
      (standardUnlinkOpenTubeHomeomorph i (by norm_num)).symm.continuous.comp
        continuous_subtype_val
    exact (continuous_fst.comp hp).prodMk ((continuous_snd.comp hp).subtype_mk _)
  continuous_invFun := by
    have hp : Continuous (fun p : Sphere 2 × UnlinkPuncturedNormalThreeEighthDisk i ↦
        ((p.1, p.2.1) : Sphere 2 × UnlinkNormalDisk i (3 / 8 : ℝ))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    apply Continuous.subtype_mk
    change Continuous (fun p : Sphere 2 × UnlinkPuncturedNormalThreeEighthDisk i ↦
      standardUnlinkOpenTubeHomeomorph i (by norm_num) (p.1, p.2.1))
    exact (standardUnlinkOpenTubeHomeomorph i (by norm_num)).continuous.comp hp

/-- Product coordinates on the radius-`3/8` tube outside the closed radius-`1/8` core. -/
def standardUnlinkExteriorEighthTubeProductHomeomorph (i : Fin 2) :
    StandardUnlinkExteriorEighthTube i ≃ₜ
      Sphere 2 × UnlinkExteriorEighthNormalThreeEighthDisk i where
  toFun q := by
    let p := (standardUnlinkOpenTubeHomeomorph i (by norm_num : (3 / 8 : ℝ) < 1 / 2)).symm q.1
    exact (p.1, ⟨p.2, by
      change 1 / 8 < ‖p.2.1 - standardUnlinkNormalCenter i‖
      rw [standardUnlinkOpenTubeHomeomorph_symm_snd_coe]
      exact q.2⟩)
  invFun p := by
    let q := standardUnlinkOpenTubeHomeomorph i
      (by norm_num : (3 / 8 : ℝ) < 1 / 2) (p.1, p.2.1)
    exact ⟨q, by
      change 1 / 8 < ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter i‖
      rw [standardUnlinkNormalProjection_openTubeHomeomorph]
      exact p.2.2⟩
  left_inv q := by
    apply Subtype.ext
    exact (standardUnlinkOpenTubeHomeomorph i
      (by norm_num : (3 / 8 : ℝ) < 1 / 2)).apply_symm_apply q.1
  right_inv p := by
    dsimp only
    have h := (standardUnlinkOpenTubeHomeomorph i
      (by norm_num : (3 / 8 : ℝ) < 1 / 2)).symm_apply_apply (p.1, p.2.1)
    have hfst := congrArg
      (fun z : Sphere 2 × UnlinkNormalDisk i (3 / 8 : ℝ) ↦ z.1) h
    have hsnd := congrArg
      (fun z : Sphere 2 × UnlinkNormalDisk i (3 / 8 : ℝ) ↦ z.2) h
    apply Prod.ext
    · exact hfst
    · exact Subtype.ext hsnd
  continuous_toFun := by
    have hp : Continuous (fun q : StandardUnlinkExteriorEighthTube i ↦
        (standardUnlinkOpenTubeHomeomorph i
          (by norm_num : (3 / 8 : ℝ) < 1 / 2)).symm q.1) :=
      (standardUnlinkOpenTubeHomeomorph i (by norm_num)).symm.continuous.comp
        continuous_subtype_val
    exact (continuous_fst.comp hp).prodMk ((continuous_snd.comp hp).subtype_mk _)
  continuous_invFun := by
    have hp : Continuous
        (fun p : Sphere 2 × UnlinkExteriorEighthNormalThreeEighthDisk i ↦
          ((p.1, p.2.1) : Sphere 2 × UnlinkNormalDisk i (3 / 8 : ℝ))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    apply Continuous.subtype_mk
    change Continuous
      (fun p : Sphere 2 × UnlinkExteriorEighthNormalThreeEighthDisk i ↦
        standardUnlinkOpenTubeHomeomorph i (by norm_num) (p.1, p.2.1))
    exact (standardUnlinkOpenTubeHomeomorph i (by norm_num)).continuous.comp hp

/-- The local tube homeomorphism which pushes the deleted center section out to radius `1/8`. -/
def standardUnlinkPuncturedToExteriorEighthTubeHomeomorph (i : Fin 2) :
    StandardUnlinkPuncturedTube i (3 / 8 : ℝ) ≃ₜ
      StandardUnlinkExteriorEighthTube i :=
  (standardUnlinkPuncturedTubeProductHomeomorph i).trans
    ((Homeomorph.refl (Sphere 2)).prodCongr (unlinkNormalEighthDiskHomeomorph i) |>.trans
      (standardUnlinkExteriorEighthTubeProductHomeomorph i).symm)

theorem standardUnlinkPuncturedToExteriorEighthTubeHomeomorph_coe
    (i : Fin 2) (q : StandardUnlinkPuncturedTube i (3 / 8 : ℝ)) :
    ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph i q).1.1 : Sphere 4) =
      (standardUnlinkOpenTubeHomeomorph i (by norm_num : (3 / 8 : ℝ) < 1 / 2)
        ((standardUnlinkOpenTubeHomeomorph i (by norm_num)).symm q.1 |>.1,
          (unlinkNormalEighthDiskHomeomorph i
            (standardUnlinkPuncturedTubeProductHomeomorph i q |>.2)).1)).1 :=
  rfl

theorem standardUnlinkPuncturedToExteriorEighthTubeHomeomorph_symm_coe
    (i : Fin 2) (q : StandardUnlinkExteriorEighthTube i) :
    (((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph i).symm q).1.1 : Sphere 4) =
      (standardUnlinkOpenTubeHomeomorph i (by norm_num : (3 / 8 : ℝ) < 1 / 2)
        ((standardUnlinkOpenTubeHomeomorph i (by norm_num)).symm q.1 |>.1,
          ((unlinkNormalEighthDiskHomeomorph i).symm
            (standardUnlinkExteriorEighthTubeProductHomeomorph i q |>.2)).1)).1 :=
  rfl

theorem standardUnlinkPuncturedToExteriorEighthTubeHomeomorph_eq_self_of_quarter_le
    (i : Fin 2) (q : StandardUnlinkPuncturedTube i (3 / 8 : ℝ))
    (hq : 1 / 4 ≤
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖) :
    ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph i q).1.1 : Sphere 4) = q.1.1 := by
  rw [standardUnlinkPuncturedToExteriorEighthTubeHomeomorph_coe]
  let p := standardUnlinkPuncturedTubeProductHomeomorph i q
  have hp : 1 / 4 ≤ ‖p.2.1.1 - standardUnlinkNormalCenter i‖ := by
    change 1 / 4 ≤
      ‖((standardUnlinkOpenTubeHomeomorph i (by norm_num)).symm q.1).2.1 -
        standardUnlinkNormalCenter i‖
    rw [standardUnlinkOpenTubeHomeomorph_symm_snd_coe]
    exact hq
  rw [unlinkNormalEighthDiskHomeomorph_eq_self_of_quarter_le i p.2 hp]
  exact congrArg Subtype.val
    ((standardUnlinkOpenTubeHomeomorph i (by norm_num)).apply_symm_apply q.1)

theorem standardUnlinkPuncturedToExteriorEighthTubeHomeomorph_symm_eq_self_of_quarter_le
    (i : Fin 2) (q : StandardUnlinkExteriorEighthTube i)
    (hq : 1 / 4 ≤
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖) :
    (((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph i).symm q).1.1 : Sphere 4) =
      q.1.1 := by
  rw [standardUnlinkPuncturedToExteriorEighthTubeHomeomorph_symm_coe]
  let p := standardUnlinkExteriorEighthTubeProductHomeomorph i q
  have hp : 1 / 4 ≤ ‖p.2.1.1 - standardUnlinkNormalCenter i‖ := by
    change 1 / 4 ≤
      ‖((standardUnlinkOpenTubeHomeomorph i (by norm_num)).symm q.1).2.1 -
        standardUnlinkNormalCenter i‖
    rw [standardUnlinkOpenTubeHomeomorph_symm_snd_coe]
    exact hq
  rw [unlinkNormalEighthDiskHomeomorph_symm_eq_self_of_quarter_le i p.2 hp]
  exact congrArg Subtype.val
    ((standardUnlinkOpenTubeHomeomorph i (by norm_num)).apply_symm_apply q.1)

/-! ## The global source and target open sets -/

/-- The open interior of the radius-`1/8` coordinate exterior: equivalently, the complement of
the two closed radius-`1/8` tubes. -/
def standardUnlinkClosedTubeExteriorOpens : Opens (Sphere 4) :=
  ⟨(standardUnlinkClosedTubes (1 / 8 : ℝ))ᶜ,
    (isClosed_standardUnlinkClosedTubes (1 / 8 : ℝ)).isOpen_compl⟩

abbrev StandardUnlinkClosedTubeExterior :=
  standardUnlinkClosedTubeExteriorOpens

@[simp]
theorem mem_standardUnlinkClosedTubeExteriorOpens (q : Sphere 4) :
    q ∈ standardUnlinkClosedTubeExteriorOpens ↔
      ∀ i : Fin 2,
        1 / 8 < ‖standardUnlinkNormalProjection q - standardUnlinkNormalCenter i‖ := by
  change q ∉ standardUnlinkClosedTubes (1 / 8 : ℝ) ↔ _
  simp only [standardUnlinkClosedTubes, standardUnlinkClosedTube,
    mem_union, mem_preimage, mem_closedBall, dist_eq_norm, not_or, not_le]
  constructor
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1
  · intro h
    exact ⟨h 0, h 1⟩

theorem standardUnlinkClosedTubeExterior_subset_coordinateUnlinkExterior :
    (standardUnlinkClosedTubes (1 / 8 : ℝ))ᶜ ⊆
      coordinateUnlinkExterior (1 / 8 : ℝ) :=
  compl_subset_compl.mpr
    (standardUnlinkOpenTubes_subset_closedTubes (1 / 8 : ℝ))

theorem mem_standardUnlinkClosedTubeExterior_iff_mem_coordinateExterior_strict
    (q : Sphere 4) :
    q ∈ standardUnlinkClosedTubeExteriorOpens ↔
      q ∈ coordinateUnlinkExterior (1 / 8 : ℝ) ∧
        ∀ i : Fin 2,
          1 / 8 < ‖standardUnlinkNormalProjection q - standardUnlinkNormalCenter i‖ := by
  constructor
  · intro hq
    exact ⟨standardUnlinkClosedTubeExterior_subset_coordinateUnlinkExterior hq,
      (mem_standardUnlinkClosedTubeExteriorOpens q).mp hq⟩
  · exact fun hq ↦ (mem_standardUnlinkClosedTubeExteriorOpens q).mpr hq.2

theorem standardUnlinkClosedTube_eighth_subset_openTube_threeEighth (i : Fin 2) :
    standardUnlinkClosedTube i (1 / 8 : ℝ) ⊆
      standardUnlinkOpenTube i (3 / 8 : ℝ) :=
  preimage_mono (closedBall_subset_ball (by norm_num))

theorem not_mem_standardUnlinkClosedTube_eighth_iff (i : Fin 2) (q : Sphere 4) :
    q ∉ standardUnlinkClosedTube i (1 / 8 : ℝ) ↔
      1 / 8 < ‖standardUnlinkNormalProjection q - standardUnlinkNormalCenter i‖ := by
  simp only [standardUnlinkClosedTube, mem_preimage, mem_closedBall, dist_eq_norm, not_le]

/-- The intersection of the strict link complement with one radius-`3/8` product tube. -/
def standardUnlinkComplementTubeOpens (i : Fin 2) : Opens StandardUnlinkComplement :=
  ⟨{q | q.1 ∈ standardUnlinkOpenTube i (3 / 8 : ℝ)},
    (isOpen_standardUnlinkOpenTube i (3 / 8 : ℝ)).preimage continuous_subtype_val⟩

abbrev StandardUnlinkComplementTube (i : Fin 2) :=
  standardUnlinkComplementTubeOpens i

/-- The corresponding open tube inside the closed-tube exterior. -/
def standardUnlinkClosedTubeExteriorTubeOpens (i : Fin 2) :
    Opens StandardUnlinkClosedTubeExterior :=
  ⟨{q | q.1 ∈ standardUnlinkOpenTube i (3 / 8 : ℝ)},
    (isOpen_standardUnlinkOpenTube i (3 / 8 : ℝ)).preimage continuous_subtype_val⟩

abbrev StandardUnlinkClosedTubeExteriorTube (i : Fin 2) :=
  standardUnlinkClosedTubeExteriorTubeOpens i

/-- Forget the redundant complement subtype and regard a complement-tube point as a point of the
punctured ambient tube. -/
def standardUnlinkComplementTubeToPuncturedTube (i : Fin 2)
    (q : StandardUnlinkComplementTube i) :
    StandardUnlinkPuncturedTube i (3 / 8 : ℝ) := by
  refine ⟨⟨q.1.1, q.2⟩, ?_⟩
  change standardUnlinkNormalProjection q.1.1 ≠ standardUnlinkNormalCenter i
  intro h
  have hi : q.1.1 ∈ standardUnlinkComponent i := by
    rw [← preimage_singleton_standardUnlinkNormalCenter i]
    exact h
  apply q.1.2
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

theorem continuous_standardUnlinkComplementTubeToPuncturedTube (i : Fin 2) :
    Continuous (standardUnlinkComplementTubeToPuncturedTube i) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- Forget the redundant global-exterior subtype and regard a target-tube point as a point of the
local annular tube. -/
def standardUnlinkClosedTubeExteriorTubeToLocal (i : Fin 2)
    (q : StandardUnlinkClosedTubeExteriorTube i) :
    StandardUnlinkExteriorEighthTube i :=
  ⟨⟨q.1.1, q.2⟩,
    (mem_standardUnlinkClosedTubeExteriorOpens q.1.1).mp q.1.2 i⟩

theorem continuous_standardUnlinkClosedTubeExteriorTubeToLocal (i : Fin 2) :
    Continuous (standardUnlinkClosedTubeExteriorTubeToLocal i) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def standardUnlinkComplementTubeForward (i : Fin 2)
    (q : StandardUnlinkComplementTube i) : Sphere 4 :=
  (standardUnlinkPuncturedToExteriorEighthTubeHomeomorph i
    (standardUnlinkComplementTubeToPuncturedTube i q)).1.1

def standardUnlinkClosedTubeExteriorTubeInverse (i : Fin 2)
    (q : StandardUnlinkClosedTubeExteriorTube i) : Sphere 4 :=
  ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph i).symm
    (standardUnlinkClosedTubeExteriorTubeToLocal i q)).1.1

theorem continuous_standardUnlinkComplementTubeForward (i : Fin 2) :
    Continuous (standardUnlinkComplementTubeForward i) :=
  continuous_subtype_val.comp (continuous_subtype_val.comp
    ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph i).continuous.comp
      (continuous_standardUnlinkComplementTubeToPuncturedTube i)))

theorem continuous_standardUnlinkClosedTubeExteriorTubeInverse (i : Fin 2) :
    Continuous (standardUnlinkClosedTubeExteriorTubeInverse i) :=
  continuous_subtype_val.comp (continuous_subtype_val.comp
    ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph i).symm.continuous.comp
      (continuous_standardUnlinkClosedTubeExteriorTubeToLocal i)))

theorem standardUnlinkComplementTubeForward_eq_self_of_quarter_le
    (i : Fin 2) (q : StandardUnlinkComplementTube i)
    (hq : 1 / 4 ≤
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖) :
    standardUnlinkComplementTubeForward i q = q.1.1 :=
  standardUnlinkPuncturedToExteriorEighthTubeHomeomorph_eq_self_of_quarter_le
    i (standardUnlinkComplementTubeToPuncturedTube i q) hq

theorem standardUnlinkClosedTubeExteriorTubeInverse_eq_self_of_quarter_le
    (i : Fin 2) (q : StandardUnlinkClosedTubeExteriorTube i)
    (hq : 1 / 4 ≤
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖) :
    standardUnlinkClosedTubeExteriorTubeInverse i q = q.1.1 :=
  standardUnlinkPuncturedToExteriorEighthTubeHomeomorph_symm_eq_self_of_quarter_le
    i (standardUnlinkClosedTubeExteriorTubeToLocal i q) hq

/-! ## Piecewise global maps -/

def standardUnlinkComplementExteriorForwardRaw
    (q : StandardUnlinkComplement) : Sphere 4 := by
  classical
  exact if h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ) then
    standardUnlinkComplementTubeForward 0 ⟨q, h0⟩
  else if h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ) then
    standardUnlinkComplementTubeForward 1 ⟨q, h1⟩
  else q.1

def standardUnlinkComplementExteriorInverseRaw
    (q : StandardUnlinkClosedTubeExterior) : Sphere 4 := by
  classical
  exact if h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ) then
    standardUnlinkClosedTubeExteriorTubeInverse 0 ⟨q, h0⟩
  else if h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ) then
    standardUnlinkClosedTubeExteriorTubeInverse 1 ⟨q, h1⟩
  else q.1

theorem standardUnlinkComplementExteriorForwardRaw_of_mem_zero
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorForwardRaw q =
      standardUnlinkComplementTubeForward 0 ⟨q, hq⟩ := by
  rw [standardUnlinkComplementExteriorForwardRaw, dite_eq_left hq]

theorem standardUnlinkComplementExteriorForwardRaw_of_mem_one
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorForwardRaw q =
      standardUnlinkComplementTubeForward 1 ⟨q, hq⟩ := by
  have hq0 : q.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := fun hq0 ↦
    Set.disjoint_left.mp (disjoint_standardUnlinkOpenTube_zero_one (by norm_num)) hq0 hq
  rw [standardUnlinkComplementExteriorForwardRaw, dite_eq_right hq0, dite_eq_left hq]

theorem standardUnlinkComplementExteriorForwardRaw_of_not_mem
    (q : StandardUnlinkComplement)
    (h0 : q.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ))
    (h1 : q.1 ∉ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorForwardRaw q = q.1 := by
  rw [standardUnlinkComplementExteriorForwardRaw, dite_eq_right h0, dite_eq_right h1]

theorem standardUnlinkComplementExteriorInverseRaw_of_mem_zero
    (q : StandardUnlinkClosedTubeExterior)
    (hq : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorInverseRaw q =
      standardUnlinkClosedTubeExteriorTubeInverse 0 ⟨q, hq⟩ := by
  rw [standardUnlinkComplementExteriorInverseRaw, dite_eq_left hq]

theorem standardUnlinkComplementExteriorInverseRaw_of_mem_one
    (q : StandardUnlinkClosedTubeExterior)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorInverseRaw q =
      standardUnlinkClosedTubeExteriorTubeInverse 1 ⟨q, hq⟩ := by
  have hq0 : q.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := fun hq0 ↦
    Set.disjoint_left.mp (disjoint_standardUnlinkOpenTube_zero_one (by norm_num)) hq0 hq
  rw [standardUnlinkComplementExteriorInverseRaw, dite_eq_right hq0, dite_eq_left hq]

theorem standardUnlinkComplementExteriorInverseRaw_of_not_mem
    (q : StandardUnlinkClosedTubeExterior)
    (h0 : q.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ))
    (h1 : q.1 ∉ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorInverseRaw q = q.1 := by
  rw [standardUnlinkComplementExteriorInverseRaw, dite_eq_right h0, dite_eq_right h1]

theorem standardUnlinkComplementExteriorForwardRaw_mem_target
    (q : StandardUnlinkComplement) :
    standardUnlinkComplementExteriorForwardRaw q ∈
      standardUnlinkClosedTubeExteriorOpens := by
  rw [mem_standardUnlinkClosedTubeExteriorOpens]
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · let z := standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 0
      (standardUnlinkComplementTubeToPuncturedTube 0 ⟨q, h0⟩)
    have hzTube : z.1.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := z.1.2
    have hzStrict : 1 / 8 <
        ‖standardUnlinkNormalProjection z.1.1 - standardUnlinkNormalCenter 0‖ := z.2
    rw [standardUnlinkComplementExteriorForwardRaw, dite_eq_left h0]
    intro i
    fin_cases i
    · exact hzStrict
    · apply (not_mem_standardUnlinkClosedTube_eighth_iff 1 z.1.1).mp
      intro hzOne
      have hz0R : z.1.1 ∈ standardUnlinkClosedTube 0 (3 / 8 : ℝ) :=
        standardUnlinkOpenTube_subset_closedTube 0 (3 / 8 : ℝ) hzTube
      have hz1R : z.1.1 ∈ standardUnlinkClosedTube 1 (3 / 8 : ℝ) :=
        preimage_mono (closedBall_subset_closedBall (by norm_num)) hzOne
      exact Set.disjoint_left.mp
        (disjoint_standardUnlinkClosedTube_zero_one (by norm_num)) hz0R hz1R
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · let z := standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 1
        (standardUnlinkComplementTubeToPuncturedTube 1 ⟨q, h1⟩)
      have hzTube : z.1.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ) := z.1.2
      have hzStrict : 1 / 8 <
          ‖standardUnlinkNormalProjection z.1.1 - standardUnlinkNormalCenter 1‖ := z.2
      rw [standardUnlinkComplementExteriorForwardRaw, dite_eq_right h0, dite_eq_left h1]
      intro i
      fin_cases i
      · apply (not_mem_standardUnlinkClosedTube_eighth_iff 0 z.1.1).mp
        intro hzZero
        have hz0R : z.1.1 ∈ standardUnlinkClosedTube 0 (3 / 8 : ℝ) :=
          preimage_mono (closedBall_subset_closedBall (by norm_num)) hzZero
        have hz1R : z.1.1 ∈ standardUnlinkClosedTube 1 (3 / 8 : ℝ) :=
          standardUnlinkOpenTube_subset_closedTube 1 (3 / 8 : ℝ) hzTube
        exact Set.disjoint_left.mp
          (disjoint_standardUnlinkClosedTube_zero_one (by norm_num)) hz0R hz1R
      · exact hzStrict
    · rw [standardUnlinkComplementExteriorForwardRaw, dite_eq_right h0, dite_eq_right h1]
      intro i
      fin_cases i
      · exact (not_mem_standardUnlinkClosedTube_eighth_iff 0 q.1).mp
          (fun h ↦ h0 (standardUnlinkClosedTube_eighth_subset_openTube_threeEighth 0 h))
      · exact (not_mem_standardUnlinkClosedTube_eighth_iff 1 q.1).mp
          (fun h ↦ h1 (standardUnlinkClosedTube_eighth_subset_openTube_threeEighth 1 h))

theorem standardUnlinkComplementExteriorInverseRaw_mem_source
    (q : StandardUnlinkClosedTubeExterior) :
    standardUnlinkComplementExteriorInverseRaw q ∈ standardUnlinkComplementOpens := by
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · let z := (standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 0).symm
      (standardUnlinkClosedTubeExteriorTubeToLocal 0 ⟨q, h0⟩)
    rw [standardUnlinkComplementExteriorInverseRaw, dite_eq_left h0]
    intro hzCarrier
    rcases hzCarrier with hz0 | hz1
    · have hzProj : standardUnlinkNormalProjection z.1.1 =
          standardUnlinkNormalCenter 0 := by
        rw [← mem_singleton_iff, ← mem_preimage,
          preimage_singleton_standardUnlinkNormalCenter]
        exact hz0
      exact z.2 hzProj
    · have hzOther : z.1.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ) :=
        standardUnlinkComponent_subset_openTube 1 (by norm_num) hz1
      exact Set.disjoint_left.mp
        (disjoint_standardUnlinkOpenTube_zero_one (by norm_num)) z.1.2 hzOther
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · let z := (standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 1).symm
        (standardUnlinkClosedTubeExteriorTubeToLocal 1 ⟨q, h1⟩)
      rw [standardUnlinkComplementExteriorInverseRaw, dite_eq_right h0, dite_eq_left h1]
      intro hzCarrier
      rcases hzCarrier with hz0 | hz1
      · have hzOther : z.1.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ) :=
          standardUnlinkComponent_subset_openTube 0 (by norm_num) hz0
        exact Set.disjoint_left.mp
          (disjoint_standardUnlinkOpenTube_zero_one (by norm_num)) hzOther z.1.2
      · have hzProj : standardUnlinkNormalProjection z.1.1 =
            standardUnlinkNormalCenter 1 := by
          rw [← mem_singleton_iff, ← mem_preimage,
            preimage_singleton_standardUnlinkNormalCenter]
          exact hz1
        exact z.2 hzProj
    · rw [standardUnlinkComplementExteriorInverseRaw, dite_eq_right h0, dite_eq_right h1]
      intro hzCarrier
      rcases hzCarrier with hz0 | hz1
      · exact h0 (standardUnlinkComponent_subset_openTube 0 (by norm_num) hz0)
      · exact h1 (standardUnlinkComponent_subset_openTube 1 (by norm_num) hz1)

theorem standardUnlinkComplementExteriorForwardRaw_eq_self_of_not_mem_closedTubes_quarter
    (q : StandardUnlinkComplement)
    (hq : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ)) :
    standardUnlinkComplementExteriorForwardRaw q = q.1 := by
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · rw [standardUnlinkComplementExteriorForwardRaw, dite_eq_left h0]
    apply standardUnlinkComplementTubeForward_eq_self_of_quarter_le
    have hnot : q.1 ∉ standardUnlinkClosedTube 0 (1 / 4 : ℝ) :=
      fun h ↦ hq (Or.inl h)
    change ¬dist (standardUnlinkNormalProjection q.1)
      (standardUnlinkNormalCenter 0) ≤ 1 / 4 at hnot
    simpa only [dist_eq_norm] using (lt_of_not_ge hnot).le
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · simp only [standardUnlinkComplementExteriorForwardRaw, h0, h1, dite_false,
        dite_true]
      apply standardUnlinkComplementTubeForward_eq_self_of_quarter_le
      have hnot : q.1 ∉ standardUnlinkClosedTube 1 (1 / 4 : ℝ) :=
        fun h ↦ hq (Or.inr h)
      change ¬dist (standardUnlinkNormalProjection q.1)
        (standardUnlinkNormalCenter 1) ≤ 1 / 4 at hnot
      simpa only [dist_eq_norm] using (lt_of_not_ge hnot).le
    · simp [standardUnlinkComplementExteriorForwardRaw, h0, h1]

theorem standardUnlinkComplementExteriorInverseRaw_eq_self_of_not_mem_closedTubes_quarter
    (q : StandardUnlinkClosedTubeExterior)
    (hq : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ)) :
    standardUnlinkComplementExteriorInverseRaw q = q.1 := by
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · rw [standardUnlinkComplementExteriorInverseRaw, dite_eq_left h0]
    apply standardUnlinkClosedTubeExteriorTubeInverse_eq_self_of_quarter_le
    have hnot : q.1 ∉ standardUnlinkClosedTube 0 (1 / 4 : ℝ) :=
      fun h ↦ hq (Or.inl h)
    change ¬dist (standardUnlinkNormalProjection q.1)
      (standardUnlinkNormalCenter 0) ≤ 1 / 4 at hnot
    simpa only [dist_eq_norm] using (lt_of_not_ge hnot).le
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · simp only [standardUnlinkComplementExteriorInverseRaw, h0, h1, dite_false,
        dite_true]
      apply standardUnlinkClosedTubeExteriorTubeInverse_eq_self_of_quarter_le
      have hnot : q.1 ∉ standardUnlinkClosedTube 1 (1 / 4 : ℝ) :=
        fun h ↦ hq (Or.inr h)
      change ¬dist (standardUnlinkNormalProjection q.1)
        (standardUnlinkNormalCenter 1) ≤ 1 / 4 at hnot
      simpa only [dist_eq_norm] using (lt_of_not_ge hnot).le
    · simp [standardUnlinkComplementExteriorInverseRaw, h0, h1]

theorem continuous_standardUnlinkComplementExteriorForwardRaw :
    Continuous standardUnlinkComplementExteriorForwardRaw := by
  rw [continuous_iff_continuousAt]
  intro q
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · apply ((standardUnlinkComplementTubeOpens 0).isOpen.isOpenEmbedding_subtypeVal
      |>.continuousAt_iff (g := standardUnlinkComplementExteriorForwardRaw)
        (x := ⟨q, h0⟩)).mp
    apply (continuous_standardUnlinkComplementTubeForward 0).continuousAt.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y ↦ by
      have hy : y.1.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := y.2
      change standardUnlinkComplementExteriorForwardRaw y.1 =
        standardUnlinkComplementTubeForward 0 y
      rw [standardUnlinkComplementExteriorForwardRaw, dite_eq_left hy]
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · apply ((standardUnlinkComplementTubeOpens 1).isOpen.isOpenEmbedding_subtypeVal
        |>.continuousAt_iff (g := standardUnlinkComplementExteriorForwardRaw)
          (x := ⟨q, h1⟩)).mp
      apply (continuous_standardUnlinkComplementTubeForward 1).continuousAt.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun y ↦ by
        have hy : y.1.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ) := y.2
        have hy0 : y.1.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := fun hy0 ↦
          Set.disjoint_left.mp (disjoint_standardUnlinkOpenTube_zero_one (by norm_num)) hy0 hy
        change standardUnlinkComplementExteriorForwardRaw y.1 =
          standardUnlinkComplementTubeForward 1 y
        rw [standardUnlinkComplementExteriorForwardRaw, dite_eq_right hy0, dite_eq_left hy]
    · have hquarter : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ) := by
        rintro (hq0 | hq1)
        · exact h0 (preimage_mono (closedBall_subset_ball (by norm_num)) hq0)
        · exact h1 (preimage_mono (closedBall_subset_ball (by norm_num)) hq1)
      apply continuousAt_subtype_val.congr_of_eventuallyEq
      filter_upwards [((isClosed_standardUnlinkClosedTubes (1 / 4 : ℝ)).isOpen_compl.preimage
        continuous_subtype_val).mem_nhds hquarter] with y hy
      exact standardUnlinkComplementExteriorForwardRaw_eq_self_of_not_mem_closedTubes_quarter y hy

theorem continuous_standardUnlinkComplementExteriorInverseRaw :
    Continuous standardUnlinkComplementExteriorInverseRaw := by
  rw [continuous_iff_continuousAt]
  intro q
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · apply ((standardUnlinkClosedTubeExteriorTubeOpens 0).isOpen.isOpenEmbedding_subtypeVal
      |>.continuousAt_iff (g := standardUnlinkComplementExteriorInverseRaw)
        (x := ⟨q, h0⟩)).mp
    apply (continuous_standardUnlinkClosedTubeExteriorTubeInverse 0).continuousAt
      |>.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y ↦ by
      have hy : y.1.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := y.2
      change standardUnlinkComplementExteriorInverseRaw y.1 =
        standardUnlinkClosedTubeExteriorTubeInverse 0 y
      rw [standardUnlinkComplementExteriorInverseRaw, dite_eq_left hy]
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · apply ((standardUnlinkClosedTubeExteriorTubeOpens 1).isOpen.isOpenEmbedding_subtypeVal
        |>.continuousAt_iff (g := standardUnlinkComplementExteriorInverseRaw)
          (x := ⟨q, h1⟩)).mp
      apply (continuous_standardUnlinkClosedTubeExteriorTubeInverse 1).continuousAt
        |>.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun y ↦ by
        have hy : y.1.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ) := y.2
        have hy0 : y.1.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := fun hy0 ↦
          Set.disjoint_left.mp (disjoint_standardUnlinkOpenTube_zero_one (by norm_num)) hy0 hy
        change standardUnlinkComplementExteriorInverseRaw y.1 =
          standardUnlinkClosedTubeExteriorTubeInverse 1 y
        rw [standardUnlinkComplementExteriorInverseRaw, dite_eq_right hy0, dite_eq_left hy]
    · have hquarter : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ) := by
        rintro (hq0 | hq1)
        · exact h0 (preimage_mono (closedBall_subset_ball (by norm_num)) hq0)
        · exact h1 (preimage_mono (closedBall_subset_ball (by norm_num)) hq1)
      apply continuousAt_subtype_val.congr_of_eventuallyEq
      filter_upwards [((isClosed_standardUnlinkClosedTubes (1 / 4 : ℝ)).isOpen_compl.preimage
        continuous_subtype_val).mem_nhds hquarter] with y hy
      exact standardUnlinkComplementExteriorInverseRaw_eq_self_of_not_mem_closedTubes_quarter y hy

def standardUnlinkComplementExteriorForward
    (q : StandardUnlinkComplement) : StandardUnlinkClosedTubeExterior :=
  ⟨standardUnlinkComplementExteriorForwardRaw q,
    standardUnlinkComplementExteriorForwardRaw_mem_target q⟩

def standardUnlinkComplementExteriorInverse
    (q : StandardUnlinkClosedTubeExterior) : StandardUnlinkComplement :=
  ⟨standardUnlinkComplementExteriorInverseRaw q,
    standardUnlinkComplementExteriorInverseRaw_mem_source q⟩

theorem continuous_standardUnlinkComplementExteriorForward :
    Continuous standardUnlinkComplementExteriorForward :=
  continuous_standardUnlinkComplementExteriorForwardRaw.subtype_mk _

theorem continuous_standardUnlinkComplementExteriorInverse :
    Continuous standardUnlinkComplementExteriorInverse :=
  continuous_standardUnlinkComplementExteriorInverseRaw.subtype_mk _

theorem standardUnlinkComplementExteriorInverse_forward
    (q : StandardUnlinkComplement) :
    standardUnlinkComplementExteriorInverse
        (standardUnlinkComplementExteriorForward q) = q := by
  apply Subtype.ext
  change standardUnlinkComplementExteriorInverseRaw
      (standardUnlinkComplementExteriorForward q) = q.1
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · let u := standardUnlinkComplementTubeToPuncturedTube 0 ⟨q, h0⟩
    let z := standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 0 u
    have hF : (standardUnlinkComplementExteriorForward q).1 = z.1.1 := by
      change standardUnlinkComplementExteriorForwardRaw q = z.1.1
      simpa only [standardUnlinkComplementTubeForward, u, z] using
        standardUnlinkComplementExteriorForwardRaw_of_mem_zero q h0
    have hFtube : (standardUnlinkComplementExteriorForward q).1 ∈
        standardUnlinkOpenTube 0 (3 / 8 : ℝ) := by
      rw [hF]
      exact z.1.2
    have hlocal : standardUnlinkClosedTubeExteriorTubeToLocal 0
        ⟨standardUnlinkComplementExteriorForward q, hFtube⟩ = z := by
      apply Subtype.ext
      apply Subtype.ext
      exact hF
    rw [standardUnlinkComplementExteriorInverseRaw_of_mem_zero _ hFtube]
    change ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 0).symm
      (standardUnlinkClosedTubeExteriorTubeToLocal 0
        ⟨standardUnlinkComplementExteriorForward q, hFtube⟩)).1.1 = q.1
    rw [hlocal]
    exact congrArg (fun w ↦ w.1.1)
      ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 0).symm_apply_apply u)
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · let u := standardUnlinkComplementTubeToPuncturedTube 1 ⟨q, h1⟩
      let z := standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 1 u
      have hF : (standardUnlinkComplementExteriorForward q).1 = z.1.1 := by
        change standardUnlinkComplementExteriorForwardRaw q = z.1.1
        simpa only [standardUnlinkComplementTubeForward, u, z] using
          standardUnlinkComplementExteriorForwardRaw_of_mem_one q h1
      have hFtube : (standardUnlinkComplementExteriorForward q).1 ∈
          standardUnlinkOpenTube 1 (3 / 8 : ℝ) := by
        rw [hF]
        exact z.1.2
      have hlocal : standardUnlinkClosedTubeExteriorTubeToLocal 1
          ⟨standardUnlinkComplementExteriorForward q, hFtube⟩ = z := by
        apply Subtype.ext
        apply Subtype.ext
        exact hF
      rw [standardUnlinkComplementExteriorInverseRaw_of_mem_one _ hFtube]
      change ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 1).symm
        (standardUnlinkClosedTubeExteriorTubeToLocal 1
          ⟨standardUnlinkComplementExteriorForward q, hFtube⟩)).1.1 = q.1
      rw [hlocal]
      exact congrArg (fun w ↦ w.1.1)
        ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 1).symm_apply_apply u)
    · have hF : (standardUnlinkComplementExteriorForward q).1 = q.1 :=
        standardUnlinkComplementExteriorForwardRaw_of_not_mem q h0 h1
      have hF0 : (standardUnlinkComplementExteriorForward q).1 ∉
          standardUnlinkOpenTube 0 (3 / 8 : ℝ) := by simpa only [hF] using h0
      have hF1 : (standardUnlinkComplementExteriorForward q).1 ∉
          standardUnlinkOpenTube 1 (3 / 8 : ℝ) := by simpa only [hF] using h1
      rw [standardUnlinkComplementExteriorInverseRaw_of_not_mem _ hF0 hF1]
      exact hF

theorem standardUnlinkComplementExteriorForward_inverse
    (q : StandardUnlinkClosedTubeExterior) :
    standardUnlinkComplementExteriorForward
        (standardUnlinkComplementExteriorInverse q) = q := by
  apply Subtype.ext
  change standardUnlinkComplementExteriorForwardRaw
      (standardUnlinkComplementExteriorInverse q) = q.1
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · let v := standardUnlinkClosedTubeExteriorTubeToLocal 0 ⟨q, h0⟩
    let u := (standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 0).symm v
    have hI : (standardUnlinkComplementExteriorInverse q).1 = u.1.1 := by
      change standardUnlinkComplementExteriorInverseRaw q = u.1.1
      simpa only [standardUnlinkClosedTubeExteriorTubeInverse, v, u] using
        standardUnlinkComplementExteriorInverseRaw_of_mem_zero q h0
    have hItube : (standardUnlinkComplementExteriorInverse q).1 ∈
        standardUnlinkOpenTube 0 (3 / 8 : ℝ) := by
      rw [hI]
      exact u.1.2
    have hlocal : standardUnlinkComplementTubeToPuncturedTube 0
        ⟨standardUnlinkComplementExteriorInverse q, hItube⟩ = u := by
      apply Subtype.ext
      apply Subtype.ext
      exact hI
    rw [standardUnlinkComplementExteriorForwardRaw_of_mem_zero _ hItube]
    change (standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 0
      (standardUnlinkComplementTubeToPuncturedTube 0
        ⟨standardUnlinkComplementExteriorInverse q, hItube⟩)).1.1 = q.1
    rw [hlocal]
    exact congrArg (fun w ↦ w.1.1)
      ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 0).apply_symm_apply v)
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · let v := standardUnlinkClosedTubeExteriorTubeToLocal 1 ⟨q, h1⟩
      let u := (standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 1).symm v
      have hI : (standardUnlinkComplementExteriorInverse q).1 = u.1.1 := by
        change standardUnlinkComplementExteriorInverseRaw q = u.1.1
        simpa only [standardUnlinkClosedTubeExteriorTubeInverse, v, u] using
          standardUnlinkComplementExteriorInverseRaw_of_mem_one q h1
      have hItube : (standardUnlinkComplementExteriorInverse q).1 ∈
          standardUnlinkOpenTube 1 (3 / 8 : ℝ) := by
        rw [hI]
        exact u.1.2
      have hlocal : standardUnlinkComplementTubeToPuncturedTube 1
          ⟨standardUnlinkComplementExteriorInverse q, hItube⟩ = u := by
        apply Subtype.ext
        apply Subtype.ext
        exact hI
      rw [standardUnlinkComplementExteriorForwardRaw_of_mem_one _ hItube]
      change (standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 1
        (standardUnlinkComplementTubeToPuncturedTube 1
          ⟨standardUnlinkComplementExteriorInverse q, hItube⟩)).1.1 = q.1
      rw [hlocal]
      exact congrArg (fun w ↦ w.1.1)
        ((standardUnlinkPuncturedToExteriorEighthTubeHomeomorph 1).apply_symm_apply v)
    · have hI : (standardUnlinkComplementExteriorInverse q).1 = q.1 :=
        standardUnlinkComplementExteriorInverseRaw_of_not_mem q h0 h1
      have hI0 : (standardUnlinkComplementExteriorInverse q).1 ∉
          standardUnlinkOpenTube 0 (3 / 8 : ℝ) := by simpa only [hI] using h0
      have hI1 : (standardUnlinkComplementExteriorInverse q).1 ∉
          standardUnlinkOpenTube 1 (3 / 8 : ℝ) := by simpa only [hI] using h1
      rw [standardUnlinkComplementExteriorForwardRaw_of_not_mem _ hI0 hI1]
      exact hI

/-- The strict complement of the frozen unlink is homeomorphic to the open interior of its
concrete radius-`1/8` coordinate exterior. -/
def standardUnlinkComplementExteriorHomeomorph :
    StandardUnlinkComplement ≃ₜ StandardUnlinkClosedTubeExterior where
  toFun := standardUnlinkComplementExteriorForward
  invFun := standardUnlinkComplementExteriorInverse
  left_inv := standardUnlinkComplementExteriorInverse_forward
  right_inv := standardUnlinkComplementExteriorForward_inverse
  continuous_toFun := continuous_standardUnlinkComplementExteriorForward
  continuous_invFun := continuous_standardUnlinkComplementExteriorInverse

@[simp]
theorem standardUnlinkComplementExteriorHomeomorph_coe
    (q : StandardUnlinkComplement) :
    (standardUnlinkComplementExteriorHomeomorph q : Sphere 4) =
      standardUnlinkComplementExteriorForwardRaw q :=
  rfl

@[simp]
theorem standardUnlinkComplementExteriorHomeomorph_symm_coe
    (q : StandardUnlinkClosedTubeExterior) :
    (standardUnlinkComplementExteriorHomeomorph.symm q : Sphere 4) =
      standardUnlinkComplementExteriorInverseRaw q :=
  rfl

theorem standardUnlinkComplementExteriorHomeomorph_eq_self_of_not_mem_closedTubes_quarter
    (q : StandardUnlinkComplement)
    (hq : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ)) :
    (standardUnlinkComplementExteriorHomeomorph q : Sphere 4) = q.1 :=
  standardUnlinkComplementExteriorForwardRaw_eq_self_of_not_mem_closedTubes_quarter q hq

theorem standardUnlinkComplementExteriorHomeomorph_symm_eq_self_of_not_mem_closedTubes_quarter
    (q : StandardUnlinkClosedTubeExterior)
    (hq : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ)) :
    (standardUnlinkComplementExteriorHomeomorph.symm q : Sphere 4) = q.1 :=
  standardUnlinkComplementExteriorInverseRaw_eq_self_of_not_mem_closedTubes_quarter q hq

end SplittingSpheres
