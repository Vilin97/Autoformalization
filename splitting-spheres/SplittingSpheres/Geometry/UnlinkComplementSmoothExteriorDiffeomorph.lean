/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkComplementExteriorPowerHomeomorph

/-!
# A smooth radial equivalence from the unlink complement to a strict tube exterior

This file replaces the piecewise-linear radius change used by the existing topological
homeomorphism with a globally smooth scalar diffeomorphism. Its radius change sends zero to
`1/8`, restricts to `(0, infinity) -> (1/8, infinity)`, and is literally the identity from radius
`1/4` onward.
-/

@[expose] public section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

abbrev eighth : ℝ := 1 / 8

def unlinkSmoothEighthStep : ℝ ≃ₘ[ℝ] ℝ :=
  smoothUpStepDiffeomorph eighth eighth eighth (by norm_num) (by norm_num)

/-- The smooth radius change used in the exterior equivalence. -/
def unlinkSmoothEighthRadiusDiffeomorph : ℝ ≃ₘ[ℝ] ℝ where
  toFun r := unlinkSmoothEighthStep.symm (r + eighth)
  invFun s := unlinkSmoothEighthStep s - eighth
  left_inv r := by
    change unlinkSmoothEighthStep (unlinkSmoothEighthStep.symm (r + eighth)) - eighth = r
    rw [Diffeomorph.apply_symm_apply]
    ring
  right_inv s := by
    change unlinkSmoothEighthStep.symm (unlinkSmoothEighthStep s - eighth + eighth) = s
    rw [sub_add_cancel, Diffeomorph.symm_apply_apply]
  contMDiff_toFun :=
    unlinkSmoothEighthStep.symm.contMDiff.comp (contMDiff_id.add contMDiff_const)
  contMDiff_invFun :=
    unlinkSmoothEighthStep.contMDiff.sub contMDiff_const

theorem unlinkSmoothEighthStep_apply_eighth :
    unlinkSmoothEighthStep eighth = eighth := by
  rw [unlinkSmoothEighthStep, smoothUpStepDiffeomorph_apply,
    smoothUpStep_eq_self_of_le (by norm_num) le_rfl]

@[simp]
theorem unlinkSmoothEighthRadiusDiffeomorph_zero :
    unlinkSmoothEighthRadiusDiffeomorph 0 = (1 / 8 : ℝ) := by
  change unlinkSmoothEighthStep.symm (0 + eighth) = eighth
  calc
    unlinkSmoothEighthStep.symm (0 + eighth) =
        unlinkSmoothEighthStep.symm (unlinkSmoothEighthStep eighth) := by
      congr 1
      rw [unlinkSmoothEighthStep_apply_eighth, zero_add]
    _ = eighth := Diffeomorph.symm_apply_apply _ _

@[simp]
theorem unlinkSmoothEighthRadiusDiffeomorph_symm_eighth :
    unlinkSmoothEighthRadiusDiffeomorph.symm (1 / 8 : ℝ) = 0 := by
  change unlinkSmoothEighthStep eighth - eighth = 0
  rw [unlinkSmoothEighthStep_apply_eighth, sub_self]

theorem unlinkSmoothEighthRadiusDiffeomorph_strictMono :
    StrictMono unlinkSmoothEighthRadiusDiffeomorph := by
  intro x y hxy
  change unlinkSmoothEighthStep.symm (x + eighth) <
    unlinkSmoothEighthStep.symm (y + eighth)
  exact
    (smoothUpStepOrderIso eighth eighth eighth (by norm_num) (by norm_num)).symm.strictMono
      (by linarith)

theorem unlinkSmoothEighthRadiusDiffeomorph_symm_strictMono :
    StrictMono unlinkSmoothEighthRadiusDiffeomorph.symm := by
  intro x y hxy
  change unlinkSmoothEighthStep x - eighth < unlinkSmoothEighthStep y - eighth
  exact sub_lt_sub_right
    ((smoothUpStep_strictMono (L := eighth) (by norm_num) (by norm_num)) hxy) eighth

theorem unlinkSmoothEighthRadiusDiffeomorph_gt_eighth {r : ℝ} (hr : 0 < r) :
    (1 / 8 : ℝ) < unlinkSmoothEighthRadiusDiffeomorph r := by
  rw [← unlinkSmoothEighthRadiusDiffeomorph_zero]
  exact unlinkSmoothEighthRadiusDiffeomorph_strictMono hr

theorem unlinkSmoothEighthRadiusDiffeomorph_symm_pos {s : ℝ} (hs : (1 / 8 : ℝ) < s) :
    0 < unlinkSmoothEighthRadiusDiffeomorph.symm s := by
  rw [← unlinkSmoothEighthRadiusDiffeomorph_symm_eighth]
  exact unlinkSmoothEighthRadiusDiffeomorph_symm_strictMono hs

theorem unlinkSmoothEighthRadiusDiffeomorph_eq_self_of_quarter_le {r : ℝ}
    (hr : 1 / 4 ≤ r) : unlinkSmoothEighthRadiusDiffeomorph r = r := by
  change unlinkSmoothEighthStep.symm (r + eighth) = r
  rw [show r + eighth = unlinkSmoothEighthStep r by
    rw [unlinkSmoothEighthStep, smoothUpStepDiffeomorph_apply,
      smoothUpStep_eq_add_of_le (by norm_num)
        (by norm_num [eighth] at hr ⊢; linarith)],
    Diffeomorph.symm_apply_apply]

theorem unlinkSmoothEighthRadiusDiffeomorph_symm_eq_self_of_quarter_le {s : ℝ}
    (hs : 1 / 4 ≤ s) : unlinkSmoothEighthRadiusDiffeomorph.symm s = s := by
  change unlinkSmoothEighthStep s - eighth = s
  rw [unlinkSmoothEighthStep, smoothUpStepDiffeomorph_apply,
    smoothUpStep_eq_add_of_le (by norm_num)
      (by norm_num [eighth] at hs ⊢; linarith)]
  ring

theorem unlinkSmoothEighthRadiusDiffeomorph_lt_threeEighth_iff {r : ℝ} :
    unlinkSmoothEighthRadiusDiffeomorph r < 3 / 8 ↔ r < 3 / 8 := by
  calc
    unlinkSmoothEighthRadiusDiffeomorph r < 3 / 8 ↔
        unlinkSmoothEighthRadiusDiffeomorph r <
          unlinkSmoothEighthRadiusDiffeomorph (3 / 8) := by
      rw [unlinkSmoothEighthRadiusDiffeomorph_eq_self_of_quarter_le
        (show (1 / 4 : ℝ) ≤ 3 / 8 by norm_num)]
    _ ↔ r < 3 / 8 := unlinkSmoothEighthRadiusDiffeomorph_strictMono.lt_iff_lt

theorem unlinkSmoothEighthRadiusDiffeomorph_symm_lt_threeEighth_iff {s : ℝ} :
    unlinkSmoothEighthRadiusDiffeomorph.symm s < 3 / 8 ↔ s < 3 / 8 := by
  calc
    unlinkSmoothEighthRadiusDiffeomorph.symm s < 3 / 8 ↔
        unlinkSmoothEighthRadiusDiffeomorph.symm s <
          unlinkSmoothEighthRadiusDiffeomorph.symm (3 / 8) := by
      rw [unlinkSmoothEighthRadiusDiffeomorph_symm_eq_self_of_quarter_le
        (show (1 / 4 : ℝ) ≤ 3 / 8 by norm_num)]
    _ ↔ s < 3 / 8 :=
      unlinkSmoothEighthRadiusDiffeomorph_symm_strictMono.lt_iff_lt

def unlinkPositiveRadiusOpens : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩
def unlinkExteriorEighthRadiusOpens : Opens ℝ := ⟨Ioi (1 / 8 : ℝ), isOpen_Ioi⟩

/-- The smooth scalar equivalence between positive radii and radii strictly above `1/8`. -/
def unlinkSmoothEighthRadiusIoiDiffeomorph :
    unlinkPositiveRadiusOpens ≃ₘ^∞⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯
      unlinkExteriorEighthRadiusOpens where
  toFun r := ⟨unlinkSmoothEighthRadiusDiffeomorph r.1,
    unlinkSmoothEighthRadiusDiffeomorph_gt_eighth r.2⟩
  invFun s := ⟨unlinkSmoothEighthRadiusDiffeomorph.symm s.1,
    unlinkSmoothEighthRadiusDiffeomorph_symm_pos s.2⟩
  left_inv r := Subtype.ext (unlinkSmoothEighthRadiusDiffeomorph.symm_apply_apply r.1)
  right_inv s := Subtype.ext (unlinkSmoothEighthRadiusDiffeomorph.apply_symm_apply s.1)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff unlinkExteriorEighthRadiusOpens _).mp
    exact unlinkSmoothEighthRadiusDiffeomorph.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff unlinkPositiveRadiusOpens _).mp
    exact unlinkSmoothEighthRadiusDiffeomorph.symm.contMDiff.comp contMDiff_subtype_val

theorem centeredRadialMap_comp_of_inverse
    (f g : ℝ → ℝ) (center x : UnlinkNormalPlane) (hx : x ≠ center)
    (hfpos : 0 < f ‖x - center‖)
    (hgf : g (f ‖x - center‖) = ‖x - center‖) :
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

def unlinkSmoothNormalEighthForward (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i) : UnlinkNormalExteriorEighth i := by
  refine ⟨centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph
    (standardUnlinkNormalCenter i) v.1, ?_⟩
  rw [mem_unlinkNormalExteriorEighthOpens,
    norm_centeredRadialMap_sub_center unlinkSmoothEighthRadiusDiffeomorph
      (standardUnlinkNormalCenter i)
      (unlinkPuncturedNormalPlane_coe_ne_center i v)
      (lt_trans (by norm_num : (0 : ℝ) < eighth)
        (unlinkSmoothEighthRadiusDiffeomorph_gt_eighth
          (norm_pos_iff.mpr (sub_ne_zero.mpr
            (unlinkPuncturedNormalPlane_coe_ne_center i v)))))]
  exact unlinkSmoothEighthRadiusDiffeomorph_gt_eighth
    (norm_pos_iff.mpr (sub_ne_zero.mpr
      (unlinkPuncturedNormalPlane_coe_ne_center i v)))

def unlinkSmoothNormalEighthInverse (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i) : UnlinkPuncturedNormalPlane i := by
  have hvne : v.1 ≠ standardUnlinkNormalCenter i :=
    unlinkNormalExteriorEighth_ne_center i v
  have hpos : 0 < unlinkSmoothEighthRadiusDiffeomorph.symm
      ‖v.1 - standardUnlinkNormalCenter i‖ :=
    unlinkSmoothEighthRadiusDiffeomorph_symm_pos
      ((mem_unlinkNormalExteriorEighthOpens i v.1).mp v.2)
  refine ⟨centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph.symm
    (standardUnlinkNormalCenter i) v.1, ?_⟩
  intro h
  have hnorm := norm_centeredRadialMap_sub_center
    unlinkSmoothEighthRadiusDiffeomorph.symm
    (standardUnlinkNormalCenter i) hvne hpos
  rw [h, sub_self, norm_zero] at hnorm
  linarith

theorem unlinkSmoothNormalEighthInverse_forward (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i) :
    unlinkSmoothNormalEighthInverse i (unlinkSmoothNormalEighthForward i v) = v := by
  apply Subtype.ext
  change centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph.symm
      (standardUnlinkNormalCenter i)
      (centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph
        (standardUnlinkNormalCenter i) v.1) = v.1
  apply centeredRadialMap_comp_of_inverse
  · exact unlinkPuncturedNormalPlane_coe_ne_center i v
  · exact lt_trans (by norm_num : (0 : ℝ) < eighth)
      (unlinkSmoothEighthRadiusDiffeomorph_gt_eighth
        (norm_pos_iff.mpr (sub_ne_zero.mpr
          (unlinkPuncturedNormalPlane_coe_ne_center i v))))
  · exact unlinkSmoothEighthRadiusDiffeomorph.symm_apply_apply _

theorem unlinkSmoothNormalEighthForward_inverse (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i) :
    unlinkSmoothNormalEighthForward i (unlinkSmoothNormalEighthInverse i v) = v := by
  apply Subtype.ext
  change centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph
      (standardUnlinkNormalCenter i)
      (centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph.symm
        (standardUnlinkNormalCenter i) v.1) = v.1
  apply centeredRadialMap_comp_of_inverse
  · exact unlinkNormalExteriorEighth_ne_center i v
  · exact unlinkSmoothEighthRadiusDiffeomorph_symm_pos
      ((mem_unlinkNormalExteriorEighthOpens i v.1).mp v.2)
  · exact unlinkSmoothEighthRadiusDiffeomorph.apply_symm_apply _

theorem contMDiff_unlinkSmoothNormalEighthForward (i : Fin 2) :
    ContMDiff (𝓘(ℝ, UnlinkNormalPlane)) (𝓘(ℝ, UnlinkNormalPlane)) ∞
      (unlinkSmoothNormalEighthForward i) := by
  apply (ContMDiff.subtypeVal_comp_iff (unlinkNormalExteriorEighthOpens i) _).mp
  have hd := contMDiff_unlinkNormalDisplacement i
  have hn := contMDiff_unlinkNormalPolarRadius i
  have hnum := unlinkSmoothEighthRadiusDiffeomorph.contMDiff.comp hn
  have hinv := hn.inv₀ (fun v ↦ (unlinkNormalPolarRadius_pos i v).ne')
  have hsmooth : ContMDiff (𝓘(ℝ, UnlinkNormalPlane))
      (𝓘(ℝ, UnlinkNormalPlane)) ∞
      (fun v : UnlinkPuncturedNormalPlane i ↦
        standardUnlinkNormalCenter i +
          unlinkSmoothEighthRadiusDiffeomorph (unlinkNormalPolarRadius i v) •
            (unlinkNormalPolarRadius i v)⁻¹ •
              (v.1 - standardUnlinkNormalCenter i)) :=
    contMDiff_const.add (hnum.smul (hinv.smul hd))
  apply hsmooth.congr
  intro v
  change centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph
      (standardUnlinkNormalCenter i) v.1 = _
  rw [centeredRadialMap_of_ne unlinkSmoothEighthRadiusDiffeomorph
    (standardUnlinkNormalCenter i)
    (unlinkPuncturedNormalPlane_coe_ne_center i v)]
  simp only [unlinkNormalPolarRadius, div_eq_mul_inv, smul_smul]

def unlinkExteriorEighthToPunctured (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i) : UnlinkPuncturedNormalPlane i :=
  ⟨v.1, unlinkNormalExteriorEighth_ne_center i v⟩

theorem contMDiff_unlinkExteriorEighthToPunctured (i : Fin 2) :
    ContMDiff (𝓘(ℝ, UnlinkNormalPlane)) (𝓘(ℝ, UnlinkNormalPlane)) ∞
      (unlinkExteriorEighthToPunctured i) := by
  apply (ContMDiff.subtypeVal_comp_iff (unlinkPuncturedNormalPlane i) _).mp
  exact contMDiff_subtype_val

theorem contMDiff_unlinkSmoothNormalEighthInverse (i : Fin 2) :
    ContMDiff (𝓘(ℝ, UnlinkNormalPlane)) (𝓘(ℝ, UnlinkNormalPlane)) ∞
      (unlinkSmoothNormalEighthInverse i) := by
  apply (ContMDiff.subtypeVal_comp_iff (unlinkPuncturedNormalPlane i) _).mp
  have hd := (contMDiff_unlinkNormalDisplacement i).comp
    (contMDiff_unlinkExteriorEighthToPunctured i)
  have hn := (contMDiff_unlinkNormalPolarRadius i).comp
    (contMDiff_unlinkExteriorEighthToPunctured i)
  have hnum := unlinkSmoothEighthRadiusDiffeomorph.symm.contMDiff.comp hn
  have hinv := hn.inv₀ (fun v ↦ by
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr
      (unlinkNormalExteriorEighth_ne_center i v)))
  have hsmooth : ContMDiff (𝓘(ℝ, UnlinkNormalPlane))
      (𝓘(ℝ, UnlinkNormalPlane)) ∞
      (fun v : UnlinkNormalExteriorEighth i ↦
        standardUnlinkNormalCenter i +
          unlinkSmoothEighthRadiusDiffeomorph.symm
              (unlinkNormalPolarRadius i (unlinkExteriorEighthToPunctured i v)) •
            (unlinkNormalPolarRadius i (unlinkExteriorEighthToPunctured i v))⁻¹ •
              (v.1 - standardUnlinkNormalCenter i)) :=
    contMDiff_const.add (hnum.smul (hinv.smul hd))
  apply hsmooth.congr
  intro v
  change centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph.symm
      (standardUnlinkNormalCenter i) v.1 = _
  rw [centeredRadialMap_of_ne unlinkSmoothEighthRadiusDiffeomorph.symm
    (standardUnlinkNormalCenter i) (unlinkNormalExteriorEighth_ne_center i v)]
  simp only [unlinkNormalPolarRadius, unlinkExteriorEighthToPunctured,
    div_eq_mul_inv, smul_smul]

/-- The smooth centered radial equivalence from a punctured normal plane to the exterior of its
closed radius-`1/8` disk. -/
def unlinkSmoothNormalEighthDiffeomorph (i : Fin 2) :
    UnlinkPuncturedNormalPlane i ≃ₘ^∞⟮
      𝓘(ℝ, UnlinkNormalPlane), 𝓘(ℝ, UnlinkNormalPlane)⟯
      UnlinkNormalExteriorEighth i where
  toFun := unlinkSmoothNormalEighthForward i
  invFun := unlinkSmoothNormalEighthInverse i
  left_inv := unlinkSmoothNormalEighthInverse_forward i
  right_inv := unlinkSmoothNormalEighthForward_inverse i
  contMDiff_toFun := contMDiff_unlinkSmoothNormalEighthForward i
  contMDiff_invFun := contMDiff_unlinkSmoothNormalEighthInverse i

@[simp]
theorem unlinkSmoothNormalEighthDiffeomorph_apply_coe (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i) :
    (unlinkSmoothNormalEighthDiffeomorph i v : UnlinkNormalPlane) =
      centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph
        (standardUnlinkNormalCenter i) v.1 :=
  rfl

@[simp]
theorem unlinkSmoothNormalEighthDiffeomorph_symm_apply_coe (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i) :
    ((unlinkSmoothNormalEighthDiffeomorph i).symm v : UnlinkNormalPlane) =
      centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph.symm
        (standardUnlinkNormalCenter i) v.1 :=
  rfl

theorem norm_unlinkSmoothNormalEighthDiffeomorph_sub_center (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i) :
    ‖(unlinkSmoothNormalEighthDiffeomorph i v : UnlinkNormalPlane) -
        standardUnlinkNormalCenter i‖ =
      unlinkSmoothEighthRadiusDiffeomorph
        ‖v.1 - standardUnlinkNormalCenter i‖ := by
  rw [unlinkSmoothNormalEighthDiffeomorph_apply_coe]
  exact norm_centeredRadialMap_sub_center unlinkSmoothEighthRadiusDiffeomorph
    (standardUnlinkNormalCenter i)
    (unlinkPuncturedNormalPlane_coe_ne_center i v)
    (lt_trans (by norm_num : (0 : ℝ) < eighth)
      (unlinkSmoothEighthRadiusDiffeomorph_gt_eighth
        (norm_pos_iff.mpr (sub_ne_zero.mpr
          (unlinkPuncturedNormalPlane_coe_ne_center i v)))))

theorem norm_unlinkSmoothNormalEighthDiffeomorph_symm_sub_center (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i) :
    ‖((unlinkSmoothNormalEighthDiffeomorph i).symm v : UnlinkNormalPlane) -
        standardUnlinkNormalCenter i‖ =
      unlinkSmoothEighthRadiusDiffeomorph.symm
        ‖v.1 - standardUnlinkNormalCenter i‖ := by
  rw [unlinkSmoothNormalEighthDiffeomorph_symm_apply_coe]
  exact norm_centeredRadialMap_sub_center unlinkSmoothEighthRadiusDiffeomorph.symm
    (standardUnlinkNormalCenter i) (unlinkNormalExteriorEighth_ne_center i v)
    (unlinkSmoothEighthRadiusDiffeomorph_symm_pos
      ((mem_unlinkNormalExteriorEighthOpens i v.1).mp v.2))

theorem unlinkSmoothNormalEighthDiffeomorph_eq_self_of_quarter_le (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i)
    (hv : 1 / 4 ≤ ‖v.1 - standardUnlinkNormalCenter i‖) :
    (unlinkSmoothNormalEighthDiffeomorph i v : UnlinkNormalPlane) = v.1 := by
  rw [unlinkSmoothNormalEighthDiffeomorph_apply_coe]
  apply centeredRadialMap_eq_self_of_radius_eq
  exact unlinkSmoothEighthRadiusDiffeomorph_eq_self_of_quarter_le hv

theorem unlinkSmoothNormalEighthDiffeomorph_symm_eq_self_of_quarter_le (i : Fin 2)
    (v : UnlinkNormalExteriorEighth i)
    (hv : 1 / 4 ≤ ‖v.1 - standardUnlinkNormalCenter i‖) :
    ((unlinkSmoothNormalEighthDiffeomorph i).symm v : UnlinkNormalPlane) = v.1 := by
  rw [unlinkSmoothNormalEighthDiffeomorph_symm_apply_coe]
  apply centeredRadialMap_eq_self_of_radius_eq
  exact unlinkSmoothEighthRadiusDiffeomorph_symm_eq_self_of_quarter_le hv

theorem contMDiff_puncturedNormalThreeEighthDiskToPlane (i : Fin 2) :
    ContMDiff (𝓘(ℝ, UnlinkNormalPlane)) (𝓘(ℝ, UnlinkNormalPlane)) ∞
      (puncturedNormalThreeEighthDiskToPlane i) := by
  apply (ContMDiff.subtypeVal_comp_iff (unlinkPuncturedNormalPlane i) _).mp
  exact (contMDiff_subtype_val.comp contMDiff_subtype_val).congr fun _ ↦ rfl

theorem contMDiff_exteriorEighthNormalThreeEighthDiskToPlane (i : Fin 2) :
    ContMDiff (𝓘(ℝ, UnlinkNormalPlane)) (𝓘(ℝ, UnlinkNormalPlane)) ∞
      (exteriorEighthNormalThreeEighthDiskToPlane i) := by
  apply (ContMDiff.subtypeVal_comp_iff (unlinkNormalExteriorEighthOpens i) _).mp
  exact (contMDiff_subtype_val.comp contMDiff_subtype_val).congr fun _ ↦ rfl

/-- The smooth radial normal-plane equivalence restricted to the radius-`3/8` disk. -/
def unlinkSmoothNormalEighthDiskDiffeomorph (i : Fin 2) :
    UnlinkPuncturedNormalThreeEighthDisk i ≃ₘ^∞⟮
      𝓘(ℝ, UnlinkNormalPlane), 𝓘(ℝ, UnlinkNormalPlane)⟯
      UnlinkExteriorEighthNormalThreeEighthDisk i where
  toFun v := by
    let u := puncturedNormalThreeEighthDiskToPlane i v
    let w := unlinkSmoothNormalEighthDiffeomorph i u
    have hvR : ‖v.1.1 - standardUnlinkNormalCenter i‖ < 3 / 8 := by
      have h := v.1.2
      change dist v.1.1 (standardUnlinkNormalCenter i) < 3 / 8 at h
      simpa only [dist_eq_norm] using h
    have hwR : ‖(w : UnlinkNormalPlane) - standardUnlinkNormalCenter i‖ < 3 / 8 := by
      change ‖(unlinkSmoothNormalEighthDiffeomorph i u : UnlinkNormalPlane) -
        standardUnlinkNormalCenter i‖ < 3 / 8
      rw [norm_unlinkSmoothNormalEighthDiffeomorph_sub_center]
      exact unlinkSmoothEighthRadiusDiffeomorph_lt_threeEighth_iff.mpr hvR
    exact ⟨⟨w.1, by
      change dist w.1 (standardUnlinkNormalCenter i) < 3 / 8
      simpa only [dist_eq_norm] using hwR⟩, w.2⟩
  invFun v := by
    let u := exteriorEighthNormalThreeEighthDiskToPlane i v
    let w := (unlinkSmoothNormalEighthDiffeomorph i).symm u
    have hvR : ‖v.1.1 - standardUnlinkNormalCenter i‖ < 3 / 8 := by
      have h := v.1.2
      change dist v.1.1 (standardUnlinkNormalCenter i) < 3 / 8 at h
      simpa only [dist_eq_norm] using h
    have hwR : ‖(w : UnlinkNormalPlane) - standardUnlinkNormalCenter i‖ < 3 / 8 := by
      change ‖((unlinkSmoothNormalEighthDiffeomorph i).symm u : UnlinkNormalPlane) -
        standardUnlinkNormalCenter i‖ < 3 / 8
      rw [norm_unlinkSmoothNormalEighthDiffeomorph_symm_sub_center]
      exact unlinkSmoothEighthRadiusDiffeomorph_symm_lt_threeEighth_iff.mpr hvR
    exact ⟨⟨w.1, by
      change dist w.1 (standardUnlinkNormalCenter i) < 3 / 8
      simpa only [dist_eq_norm] using hwR⟩, w.2⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change ((unlinkSmoothNormalEighthDiffeomorph i).symm
      (unlinkSmoothNormalEighthDiffeomorph i
        (puncturedNormalThreeEighthDiskToPlane i v)) : UnlinkNormalPlane) = v.1.1
    exact congrArg Subtype.val
      ((unlinkSmoothNormalEighthDiffeomorph i).symm_apply_apply
        (puncturedNormalThreeEighthDiskToPlane i v))
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change (unlinkSmoothNormalEighthDiffeomorph i
      ((unlinkSmoothNormalEighthDiffeomorph i).symm
        (exteriorEighthNormalThreeEighthDiskToPlane i v)) : UnlinkNormalPlane) = v.1.1
    exact congrArg Subtype.val
      ((unlinkSmoothNormalEighthDiffeomorph i).apply_symm_apply
        (exteriorEighthNormalThreeEighthDiskToPlane i v))
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff
      (unlinkExteriorEighthNormalThreeEighthDiskOpens i) _).mp
    apply (ContMDiff.subtypeVal_comp_iff (unlinkNormalDisk i (3 / 8 : ℝ)) _).mp
    exact (contMDiff_subtype_val.comp
      ((unlinkSmoothNormalEighthDiffeomorph i).contMDiff.comp
        (contMDiff_puncturedNormalThreeEighthDiskToPlane i))).congr fun _ ↦ rfl
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff
      (unlinkPuncturedNormalThreeEighthDiskOpens i) _).mp
    apply (ContMDiff.subtypeVal_comp_iff (unlinkNormalDisk i (3 / 8 : ℝ)) _).mp
    exact (contMDiff_subtype_val.comp
      ((unlinkSmoothNormalEighthDiffeomorph i).symm.contMDiff.comp
        (contMDiff_exteriorEighthNormalThreeEighthDiskToPlane i))).congr fun _ ↦ rfl

@[simp]
theorem unlinkSmoothNormalEighthDiskDiffeomorph_apply_coe (i : Fin 2)
    (v : UnlinkPuncturedNormalThreeEighthDisk i) :
    ((unlinkSmoothNormalEighthDiskDiffeomorph i v).1.1 : UnlinkNormalPlane) =
      unlinkSmoothNormalEighthDiffeomorph i
        (puncturedNormalThreeEighthDiskToPlane i v) :=
  rfl

@[simp]
theorem unlinkSmoothNormalEighthDiskDiffeomorph_symm_apply_coe (i : Fin 2)
    (v : UnlinkExteriorEighthNormalThreeEighthDisk i) :
    (((unlinkSmoothNormalEighthDiskDiffeomorph i).symm v).1.1 : UnlinkNormalPlane) =
      (unlinkSmoothNormalEighthDiffeomorph i).symm
        (exteriorEighthNormalThreeEighthDiskToPlane i v) :=
  rfl

theorem unlinkSmoothNormalEighthDiskDiffeomorph_eq_self_of_quarter_le (i : Fin 2)
    (v : UnlinkPuncturedNormalThreeEighthDisk i)
    (hv : 1 / 4 ≤ ‖v.1.1 - standardUnlinkNormalCenter i‖) :
    (unlinkSmoothNormalEighthDiskDiffeomorph i v).1 = v.1 := by
  apply Subtype.ext
  rw [unlinkSmoothNormalEighthDiskDiffeomorph_apply_coe]
  exact unlinkSmoothNormalEighthDiffeomorph_eq_self_of_quarter_le i _ hv

theorem unlinkSmoothNormalEighthDiskDiffeomorph_symm_eq_self_of_quarter_le (i : Fin 2)
    (v : UnlinkExteriorEighthNormalThreeEighthDisk i)
    (hv : 1 / 4 ≤ ‖v.1.1 - standardUnlinkNormalCenter i‖) :
    ((unlinkSmoothNormalEighthDiskDiffeomorph i).symm v).1 = v.1 := by
  apply Subtype.ext
  rw [unlinkSmoothNormalEighthDiskDiffeomorph_symm_apply_coe]
  exact unlinkSmoothNormalEighthDiffeomorph_symm_eq_self_of_quarter_le i _ hv

def standardUnlinkPuncturedTubeProductDiffeomorph (i : Fin 2) :
    StandardUnlinkPuncturedTube i (3 / 8 : ℝ) ≃ₘ^∞⟮
      𝓡 4, (𝓡 2).prod 𝓘(ℝ, UnlinkNormalPlane)⟯
      Sphere 2 × UnlinkPuncturedNormalThreeEighthDisk i where
  toEquiv := (standardUnlinkPuncturedTubeProductHomeomorph i).toEquiv
  contMDiff_toFun := by
    have hval : ContMDiff (𝓡 4) (𝓡 4) ∞
        (Subtype.val : StandardUnlinkPuncturedTube i (3 / 8 : ℝ) →
          StandardUnlinkOpenTubeSpace i (3 / 8 : ℝ)) :=
      contMDiff_subtype_val
    have hp := (standardUnlinkOpenTubeDiffeomorph i
      (by norm_num : (3 / 8 : ℝ) < 1 / 2)).symm.contMDiff.comp hval
    have hfst := contMDiff_fst.comp hp
    have hsndRaw := contMDiff_snd.comp hp
    have hsnd : ContMDiff (𝓡 4) (𝓘(ℝ, UnlinkNormalPlane)) ∞
        (fun q : StandardUnlinkPuncturedTube i (3 / 8 : ℝ) ↦
          (standardUnlinkPuncturedTubeProductHomeomorph i q).2) := by
      apply (ContMDiff.subtypeVal_comp_iff
        (unlinkPuncturedNormalThreeEighthDiskOpens i) _).mp
      exact hsndRaw.congr fun _ ↦ rfl
    exact (hfst.prodMk hsnd).congr fun _ ↦ rfl
  contMDiff_invFun := by
    have hp : ContMDiff ((𝓡 2).prod 𝓘(ℝ, UnlinkNormalPlane))
        ((𝓡 2).prod 𝓘(ℝ, UnlinkNormalPlane)) ∞
        (fun p : Sphere 2 × UnlinkPuncturedNormalThreeEighthDisk i ↦
          (p.1, p.2.1)) :=
      contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    apply (ContMDiff.subtypeVal_comp_iff
      (standardUnlinkPuncturedTubeOpens i (3 / 8 : ℝ)) _).mp
    exact ((standardUnlinkOpenTubeDiffeomorph i (by norm_num)).contMDiff.comp hp).congr
      fun _ ↦ rfl

def standardUnlinkExteriorEighthTubeProductDiffeomorph (i : Fin 2) :
    StandardUnlinkExteriorEighthTube i ≃ₘ^∞⟮
      𝓡 4, (𝓡 2).prod 𝓘(ℝ, UnlinkNormalPlane)⟯
      Sphere 2 × UnlinkExteriorEighthNormalThreeEighthDisk i where
  toEquiv := (standardUnlinkExteriorEighthTubeProductHomeomorph i).toEquiv
  contMDiff_toFun := by
    have hval : ContMDiff (𝓡 4) (𝓡 4) ∞
        (Subtype.val : StandardUnlinkExteriorEighthTube i →
          StandardUnlinkOpenTubeSpace i (3 / 8 : ℝ)) :=
      contMDiff_subtype_val
    have hp := (standardUnlinkOpenTubeDiffeomorph i
      (by norm_num : (3 / 8 : ℝ) < 1 / 2)).symm.contMDiff.comp hval
    have hfst := contMDiff_fst.comp hp
    have hsndRaw := contMDiff_snd.comp hp
    have hsnd : ContMDiff (𝓡 4) (𝓘(ℝ, UnlinkNormalPlane)) ∞
        (fun q : StandardUnlinkExteriorEighthTube i ↦
          (standardUnlinkExteriorEighthTubeProductHomeomorph i q).2) := by
      apply (ContMDiff.subtypeVal_comp_iff
        (unlinkExteriorEighthNormalThreeEighthDiskOpens i) _).mp
      exact hsndRaw.congr fun _ ↦ rfl
    exact (hfst.prodMk hsnd).congr fun _ ↦ rfl
  contMDiff_invFun := by
    have hp : ContMDiff ((𝓡 2).prod 𝓘(ℝ, UnlinkNormalPlane))
        ((𝓡 2).prod 𝓘(ℝ, UnlinkNormalPlane)) ∞
        (fun p : Sphere 2 × UnlinkExteriorEighthNormalThreeEighthDisk i ↦
          (p.1, p.2.1)) :=
      contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    apply (ContMDiff.subtypeVal_comp_iff
      (standardUnlinkExteriorEighthTubeOpens i) _).mp
    exact ((standardUnlinkOpenTubeDiffeomorph i (by norm_num)).contMDiff.comp hp).congr
      fun _ ↦ rfl

/-- The local smooth tube equivalence which pushes the deleted center section to radius `1/8`. -/
def standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph (i : Fin 2) :
    StandardUnlinkPuncturedTube i (3 / 8 : ℝ) ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯
      StandardUnlinkExteriorEighthTube i :=
  (standardUnlinkPuncturedTubeProductDiffeomorph i).trans
    ((Diffeomorph.refl (𝓡 2) (Sphere 2) ∞).prodCongr
      (unlinkSmoothNormalEighthDiskDiffeomorph i) |>.trans
        (standardUnlinkExteriorEighthTubeProductDiffeomorph i).symm)

@[simp]
theorem standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph_coe
    (i : Fin 2) (q : StandardUnlinkPuncturedTube i (3 / 8 : ℝ)) :
    ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph i q).1.1 : Sphere 4) =
      (standardUnlinkOpenTubeDiffeomorph i
        (by norm_num : (3 / 8 : ℝ) < 1 / 2)
        ((standardUnlinkOpenTubeDiffeomorph i (by norm_num)).symm q.1 |>.1,
          (unlinkSmoothNormalEighthDiskDiffeomorph i
            (standardUnlinkPuncturedTubeProductDiffeomorph i q |>.2)).1)).1 :=
  rfl

@[simp]
theorem standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph_symm_coe
    (i : Fin 2) (q : StandardUnlinkExteriorEighthTube i) :
    (((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph i).symm q).1.1 :
        Sphere 4) =
      (standardUnlinkOpenTubeDiffeomorph i
        (by norm_num : (3 / 8 : ℝ) < 1 / 2)
        ((standardUnlinkOpenTubeDiffeomorph i (by norm_num)).symm q.1 |>.1,
          ((unlinkSmoothNormalEighthDiskDiffeomorph i).symm
            (standardUnlinkExteriorEighthTubeProductDiffeomorph i q |>.2)).1)).1 :=
  rfl

theorem standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph_eq_self_of_quarter_le
    (i : Fin 2) (q : StandardUnlinkPuncturedTube i (3 / 8 : ℝ))
    (hq : 1 / 4 ≤
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖) :
    ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph i q).1.1 :
        Sphere 4) = q.1.1 := by
  rw [standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph_coe]
  let p := standardUnlinkPuncturedTubeProductDiffeomorph i q
  have hp : 1 / 4 ≤ ‖p.2.1.1 - standardUnlinkNormalCenter i‖ := by
    change 1 / 4 ≤
      ‖((standardUnlinkOpenTubeDiffeomorph i (by norm_num)).symm q.1).2.1 -
        standardUnlinkNormalCenter i‖
    rw [show (standardUnlinkOpenTubeDiffeomorph i (by norm_num)).symm q.1 =
      (standardUnlinkOpenTubeHomeomorph i (by norm_num)).symm q.1 from rfl,
      standardUnlinkOpenTubeHomeomorph_symm_snd_coe]
    exact hq
  rw [unlinkSmoothNormalEighthDiskDiffeomorph_eq_self_of_quarter_le i p.2 hp]
  exact congrArg Subtype.val
    ((standardUnlinkOpenTubeDiffeomorph i (by norm_num)).apply_symm_apply q.1)

theorem standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph_symm_eq_self_of_quarter_le
    (i : Fin 2) (q : StandardUnlinkExteriorEighthTube i)
    (hq : 1 / 4 ≤
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖) :
    (((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph i).symm q).1.1 :
        Sphere 4) = q.1.1 := by
  rw [standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph_symm_coe]
  let p := standardUnlinkExteriorEighthTubeProductDiffeomorph i q
  have hp : 1 / 4 ≤ ‖p.2.1.1 - standardUnlinkNormalCenter i‖ := by
    change 1 / 4 ≤
      ‖((standardUnlinkOpenTubeDiffeomorph i (by norm_num)).symm q.1).2.1 -
        standardUnlinkNormalCenter i‖
    rw [show (standardUnlinkOpenTubeDiffeomorph i (by norm_num)).symm q.1 =
      (standardUnlinkOpenTubeHomeomorph i (by norm_num)).symm q.1 from rfl,
      standardUnlinkOpenTubeHomeomorph_symm_snd_coe]
    exact hq
  rw [unlinkSmoothNormalEighthDiskDiffeomorph_symm_eq_self_of_quarter_le i p.2 hp]
  exact congrArg Subtype.val
    ((standardUnlinkOpenTubeDiffeomorph i (by norm_num)).apply_symm_apply q.1)

theorem contMDiff_standardUnlinkComplementTubeToPuncturedTube (i : Fin 2) :
    ContMDiff (𝓡 4) (𝓡 4) ∞ (standardUnlinkComplementTubeToPuncturedTube i) := by
  apply (ContMDiff.subtypeVal_comp_iff
    (standardUnlinkPuncturedTubeOpens i (3 / 8 : ℝ)) _).mp
  apply (ContMDiff.subtypeVal_comp_iff
    (standardUnlinkOpenTubeOpens i (3 / 8 : ℝ)) _).mp
  exact (contMDiff_subtype_val.comp contMDiff_subtype_val).congr fun _ ↦ rfl

theorem contMDiff_standardUnlinkClosedTubeExteriorTubeToLocal (i : Fin 2) :
    ContMDiff (𝓡 4) (𝓡 4) ∞
      (standardUnlinkClosedTubeExteriorTubeToLocal i) := by
  apply (ContMDiff.subtypeVal_comp_iff (standardUnlinkExteriorEighthTubeOpens i) _).mp
  apply (ContMDiff.subtypeVal_comp_iff
    (standardUnlinkOpenTubeOpens i (3 / 8 : ℝ)) _).mp
  exact (contMDiff_subtype_val.comp contMDiff_subtype_val).congr fun _ ↦ rfl

def standardUnlinkSmoothComplementTubeForward (i : Fin 2)
    (q : StandardUnlinkComplementTube i) : Sphere 4 :=
  (standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph i
    (standardUnlinkComplementTubeToPuncturedTube i q)).1.1

def standardUnlinkSmoothClosedTubeExteriorTubeInverse (i : Fin 2)
    (q : StandardUnlinkClosedTubeExteriorTube i) : Sphere 4 :=
  ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph i).symm
    (standardUnlinkClosedTubeExteriorTubeToLocal i q)).1.1

theorem contMDiff_standardUnlinkSmoothComplementTubeForward (i : Fin 2) :
    ContMDiff (𝓡 4) (𝓡 4) ∞ (standardUnlinkSmoothComplementTubeForward i) := by
  exact (contMDiff_subtype_val.comp (contMDiff_subtype_val.comp
    ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph i).contMDiff.comp
      (contMDiff_standardUnlinkComplementTubeToPuncturedTube i)))).congr fun _ ↦ rfl

theorem contMDiff_standardUnlinkSmoothClosedTubeExteriorTubeInverse (i : Fin 2) :
    ContMDiff (𝓡 4) (𝓡 4) ∞
      (standardUnlinkSmoothClosedTubeExteriorTubeInverse i) := by
  exact (contMDiff_subtype_val.comp (contMDiff_subtype_val.comp
    ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph i).symm.contMDiff.comp
      (contMDiff_standardUnlinkClosedTubeExteriorTubeToLocal i)))).congr fun _ ↦ rfl

theorem standardUnlinkSmoothComplementTubeForward_eq_self_of_quarter_le
    (i : Fin 2) (q : StandardUnlinkComplementTube i)
    (hq : 1 / 4 ≤
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖) :
    standardUnlinkSmoothComplementTubeForward i q = q.1.1 :=
  standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph_eq_self_of_quarter_le
    i (standardUnlinkComplementTubeToPuncturedTube i q) hq

theorem standardUnlinkSmoothClosedTubeExteriorTubeInverse_eq_self_of_quarter_le
    (i : Fin 2) (q : StandardUnlinkClosedTubeExteriorTube i)
    (hq : 1 / 4 ≤
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖) :
    standardUnlinkSmoothClosedTubeExteriorTubeInverse i q = q.1.1 :=
  standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph_symm_eq_self_of_quarter_le
    i (standardUnlinkClosedTubeExteriorTubeToLocal i q) hq

def standardUnlinkComplementSmoothExteriorForwardRaw
    (q : StandardUnlinkComplement) : Sphere 4 := by
  classical
  exact if h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ) then
    standardUnlinkSmoothComplementTubeForward 0 ⟨q, h0⟩
  else if h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ) then
    standardUnlinkSmoothComplementTubeForward 1 ⟨q, h1⟩
  else q.1

def standardUnlinkComplementSmoothExteriorInverseRaw
    (q : StandardUnlinkClosedTubeExterior) : Sphere 4 := by
  classical
  exact if h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ) then
    standardUnlinkSmoothClosedTubeExteriorTubeInverse 0 ⟨q, h0⟩
  else if h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ) then
    standardUnlinkSmoothClosedTubeExteriorTubeInverse 1 ⟨q, h1⟩
  else q.1

theorem standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_zero
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorForwardRaw q =
      standardUnlinkSmoothComplementTubeForward 0 ⟨q, hq⟩ := by
  rw [standardUnlinkComplementSmoothExteriorForwardRaw, dite_eq_left hq]

theorem standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_one
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorForwardRaw q =
      standardUnlinkSmoothComplementTubeForward 1 ⟨q, hq⟩ := by
  have hq0 : q.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := fun hq0 ↦
    Set.disjoint_left.mp (disjoint_standardUnlinkOpenTube_zero_one (by norm_num)) hq0 hq
  rw [standardUnlinkComplementSmoothExteriorForwardRaw, dite_eq_right hq0, dite_eq_left hq]

theorem standardUnlinkComplementSmoothExteriorForwardRaw_of_not_mem
    (q : StandardUnlinkComplement)
    (h0 : q.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ))
    (h1 : q.1 ∉ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorForwardRaw q = q.1 := by
  rw [standardUnlinkComplementSmoothExteriorForwardRaw, dite_eq_right h0, dite_eq_right h1]

theorem standardUnlinkComplementSmoothExteriorInverseRaw_of_mem_zero
    (q : StandardUnlinkClosedTubeExterior)
    (hq : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorInverseRaw q =
      standardUnlinkSmoothClosedTubeExteriorTubeInverse 0 ⟨q, hq⟩ := by
  rw [standardUnlinkComplementSmoothExteriorInverseRaw, dite_eq_left hq]

theorem standardUnlinkComplementSmoothExteriorInverseRaw_of_mem_one
    (q : StandardUnlinkClosedTubeExterior)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorInverseRaw q =
      standardUnlinkSmoothClosedTubeExteriorTubeInverse 1 ⟨q, hq⟩ := by
  have hq0 : q.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := fun hq0 ↦
    Set.disjoint_left.mp (disjoint_standardUnlinkOpenTube_zero_one (by norm_num)) hq0 hq
  rw [standardUnlinkComplementSmoothExteriorInverseRaw, dite_eq_right hq0, dite_eq_left hq]

theorem standardUnlinkComplementSmoothExteriorInverseRaw_of_not_mem
    (q : StandardUnlinkClosedTubeExterior)
    (h0 : q.1 ∉ standardUnlinkOpenTube 0 (3 / 8 : ℝ))
    (h1 : q.1 ∉ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorInverseRaw q = q.1 := by
  rw [standardUnlinkComplementSmoothExteriorInverseRaw, dite_eq_right h0, dite_eq_right h1]

theorem standardUnlinkComplementSmoothExteriorForwardRaw_mem_target
    (q : StandardUnlinkComplement) :
    standardUnlinkComplementSmoothExteriorForwardRaw q ∈
      standardUnlinkClosedTubeExteriorOpens := by
  rw [mem_standardUnlinkClosedTubeExteriorOpens]
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · let z := standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 0
      (standardUnlinkComplementTubeToPuncturedTube 0 ⟨q, h0⟩)
    have hzTube : z.1.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ) := z.1.2
    have hzStrict : 1 / 8 <
        ‖standardUnlinkNormalProjection z.1.1 - standardUnlinkNormalCenter 0‖ := z.2
    rw [standardUnlinkComplementSmoothExteriorForwardRaw, dite_eq_left h0]
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
    · let z := standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 1
        (standardUnlinkComplementTubeToPuncturedTube 1 ⟨q, h1⟩)
      have hzTube : z.1.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ) := z.1.2
      have hzStrict : 1 / 8 <
          ‖standardUnlinkNormalProjection z.1.1 - standardUnlinkNormalCenter 1‖ := z.2
      rw [standardUnlinkComplementSmoothExteriorForwardRaw, dite_eq_right h0,
        dite_eq_left h1]
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
    · rw [standardUnlinkComplementSmoothExteriorForwardRaw, dite_eq_right h0,
        dite_eq_right h1]
      intro i
      fin_cases i
      · exact (not_mem_standardUnlinkClosedTube_eighth_iff 0 q.1).mp
          (fun h ↦ h0 (standardUnlinkClosedTube_eighth_subset_openTube_threeEighth 0 h))
      · exact (not_mem_standardUnlinkClosedTube_eighth_iff 1 q.1).mp
          (fun h ↦ h1 (standardUnlinkClosedTube_eighth_subset_openTube_threeEighth 1 h))

theorem standardUnlinkComplementSmoothExteriorInverseRaw_mem_source
    (q : StandardUnlinkClosedTubeExterior) :
    standardUnlinkComplementSmoothExteriorInverseRaw q ∈ standardUnlinkComplementOpens := by
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · let z := (standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 0).symm
      (standardUnlinkClosedTubeExteriorTubeToLocal 0 ⟨q, h0⟩)
    rw [standardUnlinkComplementSmoothExteriorInverseRaw, dite_eq_left h0]
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
    · let z := (standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 1).symm
        (standardUnlinkClosedTubeExteriorTubeToLocal 1 ⟨q, h1⟩)
      rw [standardUnlinkComplementSmoothExteriorInverseRaw, dite_eq_right h0,
        dite_eq_left h1]
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
    · rw [standardUnlinkComplementSmoothExteriorInverseRaw, dite_eq_right h0,
        dite_eq_right h1]
      intro hzCarrier
      rcases hzCarrier with hz0 | hz1
      · exact h0 (standardUnlinkComponent_subset_openTube 0 (by norm_num) hz0)
      · exact h1 (standardUnlinkComponent_subset_openTube 1 (by norm_num) hz1)

theorem
    standardUnlinkComplementSmoothExteriorForwardRaw_eq_self_of_not_mem_closedTubes_quarter
    (q : StandardUnlinkComplement)
    (hq : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ)) :
    standardUnlinkComplementSmoothExteriorForwardRaw q = q.1 := by
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · rw [standardUnlinkComplementSmoothExteriorForwardRaw, dite_eq_left h0]
    apply standardUnlinkSmoothComplementTubeForward_eq_self_of_quarter_le
    have hnot : q.1 ∉ standardUnlinkClosedTube 0 (1 / 4 : ℝ) :=
      fun h ↦ hq (Or.inl h)
    change ¬dist (standardUnlinkNormalProjection q.1)
      (standardUnlinkNormalCenter 0) ≤ 1 / 4 at hnot
    simpa only [dist_eq_norm] using (lt_of_not_ge hnot).le
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · simp only [standardUnlinkComplementSmoothExteriorForwardRaw, h0, h1,
        dite_false, dite_true]
      apply standardUnlinkSmoothComplementTubeForward_eq_self_of_quarter_le
      have hnot : q.1 ∉ standardUnlinkClosedTube 1 (1 / 4 : ℝ) :=
        fun h ↦ hq (Or.inr h)
      change ¬dist (standardUnlinkNormalProjection q.1)
        (standardUnlinkNormalCenter 1) ≤ 1 / 4 at hnot
      simpa only [dist_eq_norm] using (lt_of_not_ge hnot).le
    · simp [standardUnlinkComplementSmoothExteriorForwardRaw, h0, h1]

theorem
    standardUnlinkComplementSmoothExteriorInverseRaw_eq_self_of_not_mem_closedTubes_quarter
    (q : StandardUnlinkClosedTubeExterior)
    (hq : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ)) :
    standardUnlinkComplementSmoothExteriorInverseRaw q = q.1 := by
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · rw [standardUnlinkComplementSmoothExteriorInverseRaw, dite_eq_left h0]
    apply standardUnlinkSmoothClosedTubeExteriorTubeInverse_eq_self_of_quarter_le
    have hnot : q.1 ∉ standardUnlinkClosedTube 0 (1 / 4 : ℝ) :=
      fun h ↦ hq (Or.inl h)
    change ¬dist (standardUnlinkNormalProjection q.1)
      (standardUnlinkNormalCenter 0) ≤ 1 / 4 at hnot
    simpa only [dist_eq_norm] using (lt_of_not_ge hnot).le
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · simp only [standardUnlinkComplementSmoothExteriorInverseRaw, h0, h1,
        dite_false, dite_true]
      apply standardUnlinkSmoothClosedTubeExteriorTubeInverse_eq_self_of_quarter_le
      have hnot : q.1 ∉ standardUnlinkClosedTube 1 (1 / 4 : ℝ) :=
        fun h ↦ hq (Or.inr h)
      change ¬dist (standardUnlinkNormalProjection q.1)
        (standardUnlinkNormalCenter 1) ≤ 1 / 4 at hnot
      simpa only [dist_eq_norm] using (lt_of_not_ge hnot).le
    · simp [standardUnlinkComplementSmoothExteriorInverseRaw, h0, h1]

theorem contMDiff_standardUnlinkComplementSmoothExteriorForwardRaw :
    ContMDiff (𝓡 4) (𝓡 4) ∞
      standardUnlinkComplementSmoothExteriorForwardRaw := by
  intro q
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · apply (contMDiffAt_subtype_iff (I := 𝓡 4) (I' := 𝓡 4)
      (U := standardUnlinkComplementTubeOpens 0)
      (f := standardUnlinkComplementSmoothExteriorForwardRaw)
      (x := ⟨q, h0⟩)).mp
    apply (contMDiff_standardUnlinkSmoothComplementTubeForward 0).contMDiffAt
      |>.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y ↦ by
      exact standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_zero y.1 y.2
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · apply (contMDiffAt_subtype_iff (I := 𝓡 4) (I' := 𝓡 4)
        (U := standardUnlinkComplementTubeOpens 1)
        (f := standardUnlinkComplementSmoothExteriorForwardRaw)
        (x := ⟨q, h1⟩)).mp
      apply (contMDiff_standardUnlinkSmoothComplementTubeForward 1).contMDiffAt
        |>.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun y ↦ by
        exact standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_one y.1 y.2
    · have hquarter : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ) := by
        rintro (hq0 | hq1)
        · exact h0 (preimage_mono (closedBall_subset_ball (by norm_num)) hq0)
        · exact h1 (preimage_mono (closedBall_subset_ball (by norm_num)) hq1)
      apply contMDiff_subtype_val.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [((isClosed_standardUnlinkClosedTubes (1 / 4 : ℝ)).isOpen_compl.preimage
        continuous_subtype_val).mem_nhds hquarter] with y hy
      exact
        standardUnlinkComplementSmoothExteriorForwardRaw_eq_self_of_not_mem_closedTubes_quarter
          y hy

theorem contMDiff_standardUnlinkComplementSmoothExteriorInverseRaw :
    ContMDiff (𝓡 4) (𝓡 4) ∞
      standardUnlinkComplementSmoothExteriorInverseRaw := by
  intro q
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · apply (contMDiffAt_subtype_iff (I := 𝓡 4) (I' := 𝓡 4)
      (U := standardUnlinkClosedTubeExteriorTubeOpens 0)
      (f := standardUnlinkComplementSmoothExteriorInverseRaw)
      (x := ⟨q, h0⟩)).mp
    apply (contMDiff_standardUnlinkSmoothClosedTubeExteriorTubeInverse 0).contMDiffAt
      |>.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y ↦ by
      exact standardUnlinkComplementSmoothExteriorInverseRaw_of_mem_zero y.1 y.2
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · apply (contMDiffAt_subtype_iff (I := 𝓡 4) (I' := 𝓡 4)
        (U := standardUnlinkClosedTubeExteriorTubeOpens 1)
        (f := standardUnlinkComplementSmoothExteriorInverseRaw)
        (x := ⟨q, h1⟩)).mp
      apply (contMDiff_standardUnlinkSmoothClosedTubeExteriorTubeInverse 1).contMDiffAt
        |>.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun y ↦ by
        exact standardUnlinkComplementSmoothExteriorInverseRaw_of_mem_one y.1 y.2
    · have hquarter : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ) := by
        rintro (hq0 | hq1)
        · exact h0 (preimage_mono (closedBall_subset_ball (by norm_num)) hq0)
        · exact h1 (preimage_mono (closedBall_subset_ball (by norm_num)) hq1)
      apply contMDiff_subtype_val.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [((isClosed_standardUnlinkClosedTubes (1 / 4 : ℝ)).isOpen_compl.preimage
        continuous_subtype_val).mem_nhds hquarter] with y hy
      exact
        standardUnlinkComplementSmoothExteriorInverseRaw_eq_self_of_not_mem_closedTubes_quarter
          y hy

def standardUnlinkComplementSmoothExteriorForward
    (q : StandardUnlinkComplement) : StandardUnlinkClosedTubeExterior :=
  ⟨standardUnlinkComplementSmoothExteriorForwardRaw q,
    standardUnlinkComplementSmoothExteriorForwardRaw_mem_target q⟩

def standardUnlinkComplementSmoothExteriorInverse
    (q : StandardUnlinkClosedTubeExterior) : StandardUnlinkComplement :=
  ⟨standardUnlinkComplementSmoothExteriorInverseRaw q,
    standardUnlinkComplementSmoothExteriorInverseRaw_mem_source q⟩

theorem contMDiff_standardUnlinkComplementSmoothExteriorForward :
    ContMDiff (𝓡 4) (𝓡 4) ∞ standardUnlinkComplementSmoothExteriorForward := by
  apply (ContMDiff.subtypeVal_comp_iff standardUnlinkClosedTubeExteriorOpens _).mp
  exact contMDiff_standardUnlinkComplementSmoothExteriorForwardRaw

theorem contMDiff_standardUnlinkComplementSmoothExteriorInverse :
    ContMDiff (𝓡 4) (𝓡 4) ∞ standardUnlinkComplementSmoothExteriorInverse := by
  apply (ContMDiff.subtypeVal_comp_iff standardUnlinkComplementOpens _).mp
  exact contMDiff_standardUnlinkComplementSmoothExteriorInverseRaw

theorem standardUnlinkComplementSmoothExteriorInverse_forward
    (q : StandardUnlinkComplement) :
    standardUnlinkComplementSmoothExteriorInverse
        (standardUnlinkComplementSmoothExteriorForward q) = q := by
  apply Subtype.ext
  change standardUnlinkComplementSmoothExteriorInverseRaw
      (standardUnlinkComplementSmoothExteriorForward q) = q.1
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · let u := standardUnlinkComplementTubeToPuncturedTube 0 ⟨q, h0⟩
    let z := standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 0 u
    have hF : (standardUnlinkComplementSmoothExteriorForward q).1 = z.1.1 := by
      change standardUnlinkComplementSmoothExteriorForwardRaw q = z.1.1
      simpa only [standardUnlinkSmoothComplementTubeForward, u, z] using
        standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_zero q h0
    have hFtube : (standardUnlinkComplementSmoothExteriorForward q).1 ∈
        standardUnlinkOpenTube 0 (3 / 8 : ℝ) := by
      rw [hF]
      exact z.1.2
    have hlocal : standardUnlinkClosedTubeExteriorTubeToLocal 0
        ⟨standardUnlinkComplementSmoothExteriorForward q, hFtube⟩ = z := by
      apply Subtype.ext
      apply Subtype.ext
      exact hF
    rw [standardUnlinkComplementSmoothExteriorInverseRaw_of_mem_zero _ hFtube]
    change ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 0).symm
      (standardUnlinkClosedTubeExteriorTubeToLocal 0
        ⟨standardUnlinkComplementSmoothExteriorForward q, hFtube⟩)).1.1 = q.1
    rw [hlocal]
    exact congrArg (fun w ↦ w.1.1)
      ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 0).symm_apply_apply u)
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · let u := standardUnlinkComplementTubeToPuncturedTube 1 ⟨q, h1⟩
      let z := standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 1 u
      have hF : (standardUnlinkComplementSmoothExteriorForward q).1 = z.1.1 := by
        change standardUnlinkComplementSmoothExteriorForwardRaw q = z.1.1
        simpa only [standardUnlinkSmoothComplementTubeForward, u, z] using
          standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_one q h1
      have hFtube : (standardUnlinkComplementSmoothExteriorForward q).1 ∈
          standardUnlinkOpenTube 1 (3 / 8 : ℝ) := by
        rw [hF]
        exact z.1.2
      have hlocal : standardUnlinkClosedTubeExteriorTubeToLocal 1
          ⟨standardUnlinkComplementSmoothExteriorForward q, hFtube⟩ = z := by
        apply Subtype.ext
        apply Subtype.ext
        exact hF
      rw [standardUnlinkComplementSmoothExteriorInverseRaw_of_mem_one _ hFtube]
      change ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 1).symm
        (standardUnlinkClosedTubeExteriorTubeToLocal 1
          ⟨standardUnlinkComplementSmoothExteriorForward q, hFtube⟩)).1.1 = q.1
      rw [hlocal]
      exact congrArg (fun w ↦ w.1.1)
        ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 1).symm_apply_apply u)
    · have hF : (standardUnlinkComplementSmoothExteriorForward q).1 = q.1 :=
        standardUnlinkComplementSmoothExteriorForwardRaw_of_not_mem q h0 h1
      have hF0 : (standardUnlinkComplementSmoothExteriorForward q).1 ∉
          standardUnlinkOpenTube 0 (3 / 8 : ℝ) := by simpa only [hF] using h0
      have hF1 : (standardUnlinkComplementSmoothExteriorForward q).1 ∉
          standardUnlinkOpenTube 1 (3 / 8 : ℝ) := by simpa only [hF] using h1
      rw [standardUnlinkComplementSmoothExteriorInverseRaw_of_not_mem _ hF0 hF1]
      exact hF

theorem standardUnlinkComplementSmoothExteriorForward_inverse
    (q : StandardUnlinkClosedTubeExterior) :
    standardUnlinkComplementSmoothExteriorForward
        (standardUnlinkComplementSmoothExteriorInverse q) = q := by
  apply Subtype.ext
  change standardUnlinkComplementSmoothExteriorForwardRaw
      (standardUnlinkComplementSmoothExteriorInverse q) = q.1
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · let v := standardUnlinkClosedTubeExteriorTubeToLocal 0 ⟨q, h0⟩
    let u := (standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 0).symm v
    have hI : (standardUnlinkComplementSmoothExteriorInverse q).1 = u.1.1 := by
      change standardUnlinkComplementSmoothExteriorInverseRaw q = u.1.1
      simpa only [standardUnlinkSmoothClosedTubeExteriorTubeInverse, v, u] using
        standardUnlinkComplementSmoothExteriorInverseRaw_of_mem_zero q h0
    have hItube : (standardUnlinkComplementSmoothExteriorInverse q).1 ∈
        standardUnlinkOpenTube 0 (3 / 8 : ℝ) := by
      rw [hI]
      exact u.1.2
    have hlocal : standardUnlinkComplementTubeToPuncturedTube 0
        ⟨standardUnlinkComplementSmoothExteriorInverse q, hItube⟩ = u := by
      apply Subtype.ext
      apply Subtype.ext
      exact hI
    rw [standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_zero _ hItube]
    change (standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 0
      (standardUnlinkComplementTubeToPuncturedTube 0
        ⟨standardUnlinkComplementSmoothExteriorInverse q, hItube⟩)).1.1 = q.1
    rw [hlocal]
    exact congrArg (fun w ↦ w.1.1)
      ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 0).apply_symm_apply v)
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · let v := standardUnlinkClosedTubeExteriorTubeToLocal 1 ⟨q, h1⟩
      let u := (standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 1).symm v
      have hI : (standardUnlinkComplementSmoothExteriorInverse q).1 = u.1.1 := by
        change standardUnlinkComplementSmoothExteriorInverseRaw q = u.1.1
        simpa only [standardUnlinkSmoothClosedTubeExteriorTubeInverse, v, u] using
          standardUnlinkComplementSmoothExteriorInverseRaw_of_mem_one q h1
      have hItube : (standardUnlinkComplementSmoothExteriorInverse q).1 ∈
          standardUnlinkOpenTube 1 (3 / 8 : ℝ) := by
        rw [hI]
        exact u.1.2
      have hlocal : standardUnlinkComplementTubeToPuncturedTube 1
          ⟨standardUnlinkComplementSmoothExteriorInverse q, hItube⟩ = u := by
        apply Subtype.ext
        apply Subtype.ext
        exact hI
      rw [standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_one _ hItube]
      change (standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 1
        (standardUnlinkComplementTubeToPuncturedTube 1
          ⟨standardUnlinkComplementSmoothExteriorInverse q, hItube⟩)).1.1 = q.1
      rw [hlocal]
      exact congrArg (fun w ↦ w.1.1)
        ((standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph 1).apply_symm_apply v)
    · have hI : (standardUnlinkComplementSmoothExteriorInverse q).1 = q.1 :=
        standardUnlinkComplementSmoothExteriorInverseRaw_of_not_mem q h0 h1
      have hI0 : (standardUnlinkComplementSmoothExteriorInverse q).1 ∉
          standardUnlinkOpenTube 0 (3 / 8 : ℝ) := by simpa only [hI] using h0
      have hI1 : (standardUnlinkComplementSmoothExteriorInverse q).1 ∉
          standardUnlinkOpenTube 1 (3 / 8 : ℝ) := by simpa only [hI] using h1
      rw [standardUnlinkComplementSmoothExteriorForwardRaw_of_not_mem _ hI0 hI1]
      exact hI

/-- A genuine smooth equivalence from the strict unlink complement to the open interior outside
the two closed coordinate tubes of radius `1/8`. -/
def standardUnlinkComplementSmoothExteriorDiffeomorph :
    StandardUnlinkComplement ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯
      StandardUnlinkClosedTubeExterior where
  toFun := standardUnlinkComplementSmoothExteriorForward
  invFun := standardUnlinkComplementSmoothExteriorInverse
  left_inv := standardUnlinkComplementSmoothExteriorInverse_forward
  right_inv := standardUnlinkComplementSmoothExteriorForward_inverse
  contMDiff_toFun := contMDiff_standardUnlinkComplementSmoothExteriorForward
  contMDiff_invFun := contMDiff_standardUnlinkComplementSmoothExteriorInverse

@[simp]
theorem standardUnlinkComplementSmoothExteriorDiffeomorph_coe
    (q : StandardUnlinkComplement) :
    (standardUnlinkComplementSmoothExteriorDiffeomorph q : Sphere 4) =
      standardUnlinkComplementSmoothExteriorForwardRaw q :=
  rfl

@[simp]
theorem standardUnlinkComplementSmoothExteriorDiffeomorph_symm_coe
    (q : StandardUnlinkClosedTubeExterior) :
    (standardUnlinkComplementSmoothExteriorDiffeomorph.symm q : Sphere 4) =
      standardUnlinkComplementSmoothExteriorInverseRaw q :=
  rfl

theorem
    standardUnlinkComplementSmoothExteriorDiffeomorph_eq_self_of_not_mem_closedTubes_quarter
    (q : StandardUnlinkComplement)
    (hq : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ)) :
    (standardUnlinkComplementSmoothExteriorDiffeomorph q : Sphere 4) = q.1 :=
  standardUnlinkComplementSmoothExteriorForwardRaw_eq_self_of_not_mem_closedTubes_quarter q hq

theorem
    standardUnlinkComplementSmoothExteriorDiffeomorph_symm_eq_self_of_not_mem_closedTubes_quarter
    (q : StandardUnlinkClosedTubeExterior)
    (hq : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ)) :
    (standardUnlinkComplementSmoothExteriorDiffeomorph.symm q : Sphere 4) = q.1 :=
  standardUnlinkComplementSmoothExteriorInverseRaw_eq_self_of_not_mem_closedTubes_quarter q hq

theorem standardUnlinkComplementSmoothExteriorDiffeomorph_equator
    (x : Sphere 3) :
    standardUnlinkComplementSmoothExteriorDiffeomorph (equatorUnlinkComplementMap x) =
      equatorUnlinkClosedTubeExteriorMap x := by
  apply Subtype.ext
  exact standardUnlinkComplementSmoothExteriorDiffeomorph_eq_self_of_not_mem_closedTubes_quarter
    (equatorUnlinkComplementMap x)
    (by
      intro hx
      rcases hx with hx | hx
      · have hle :
            ‖standardUnlinkNormalProjection (equatorSphereMap x) -
              standardUnlinkNormalCenter 0‖ ≤ 1 / 4 := by
          simpa only [standardUnlinkClosedTube, mem_preimage, mem_closedBall,
            dist_eq_norm, equatorUnlinkComplementMap_coe] using hx
        exact (not_lt_of_ge hle)
          (quarter_lt_norm_standardUnlinkNormalProjection_equator_sub_center 0 x)
      · have hle :
            ‖standardUnlinkNormalProjection (equatorSphereMap x) -
              standardUnlinkNormalCenter 1‖ ≤ 1 / 4 := by
          simpa only [standardUnlinkClosedTube, mem_preimage, mem_closedBall,
            dist_eq_norm, equatorUnlinkComplementMap_coe] using hx
        exact (not_lt_of_ge hle)
          (quarter_lt_norm_standardUnlinkNormalProjection_equator_sub_center 1 x))

end SplittingSpheres
