/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkEquatorPowerLift

/-!
# Smooth collars of the lifted unlink equator

The latitude coordinate `t` gives an explicit diffeomorphism from
`Sphere 3 × (-1/2, 1/2)` onto an open equatorial region of `Sphere 4`.  That entire region avoids
the standard unlink.  A rotated principal-logarithm branch then lifts this collar to every
labelled sheet of the nonzero-degree power cover.

Each lifted map is a diffeomorphism onto its literal open range in the pulled-back smooth atlas,
and its zero slice is exactly the previously defined equatorial lift.  Distinct labels give
disjoint open collar ranges.  No compact-exterior, flower, star, or smooth gluing structure is
asserted here.
-/

@[expose] public section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold

namespace SplittingSpheres

noncomputable section

def equatorCollarIntervalOpens : Opens ℝ :=
  ⟨Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ), isOpen_Ioo⟩

abbrev EquatorCollarInterval := equatorCollarIntervalOpens

def equatorCollarScale (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)

def equatorCollarAmbientMap (x : EuclideanSpace ℝ (Fin 4)) (t : ℝ) :
    EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2
    ![equatorCollarScale t * x 0, equatorCollarScale t * x 1,
      equatorCollarScale t * x 2, t, equatorCollarScale t * x 3]

@[simp] theorem equatorCollarAmbientMap_apply_zero (x : EuclideanSpace ℝ (Fin 4)) (t : ℝ) :
    equatorCollarAmbientMap x t 0 = equatorCollarScale t * x 0 := rfl

@[simp] theorem equatorCollarAmbientMap_apply_one (x : EuclideanSpace ℝ (Fin 4)) (t : ℝ) :
    equatorCollarAmbientMap x t 1 = equatorCollarScale t * x 1 := rfl

@[simp] theorem equatorCollarAmbientMap_apply_two (x : EuclideanSpace ℝ (Fin 4)) (t : ℝ) :
    equatorCollarAmbientMap x t 2 = equatorCollarScale t * x 2 := rfl

@[simp] theorem equatorCollarAmbientMap_apply_three (x : EuclideanSpace ℝ (Fin 4)) (t : ℝ) :
    equatorCollarAmbientMap x t 3 = t := rfl

@[simp] theorem equatorCollarAmbientMap_apply_four (x : EuclideanSpace ℝ (Fin 4)) (t : ℝ) :
    equatorCollarAmbientMap x t 4 = equatorCollarScale t * x 3 := rfl

theorem equatorCollarScale_pos {t : ℝ} (ht : t ∈ Set.Ioo (-(1 : ℝ)) 1) :
    0 < equatorCollarScale t := by
  rw [equatorCollarScale]
  apply Real.sqrt_pos.mpr
  have hplus : 0 < 1 + t := by
    linarith [ht.1]
  nlinarith [mul_pos (sub_pos.mpr ht.2) hplus]

theorem equatorCollarScale_sq {t : ℝ} (ht : t ∈ Set.Ioo (-(1 : ℝ)) 1) :
    equatorCollarScale t ^ 2 = 1 - t ^ 2 := by
  rw [equatorCollarScale, Real.sq_sqrt]
  nlinarith [ht.1, ht.2]

theorem norm_equatorCollarAmbientMap (x : Sphere 3) (t : EquatorCollarInterval) :
    ‖equatorCollarAmbientMap x.1 t.1‖ = 1 := by
  have ht : (t : ℝ) ∈ Set.Ioo (-(1 : ℝ)) 1 := by
    constructor <;> linarith [t.2.1, t.2.2]
  have hx : ‖(x : EuclideanSpace ℝ (Fin 4))‖ ^ 2 = 1 := by
    have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp x.2
    nlinarith
  have hcoords :
      x.1 0 ^ 2 + (x.1 1 ^ 2 + (x.1 2 ^ 2 + x.1 3 ^ 2)) = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq x.1
    rw [hx] at h
    simpa [Fin.sum_univ_succ] using h.symm
  have hsq := equatorCollarScale_sq ht
  have hnormsq : ‖equatorCollarAmbientMap x.1 t.1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (equatorCollarScale t.1 * x.1 0) ^ 2 +
      ((equatorCollarScale t.1 * x.1 1) ^ 2 +
        ((equatorCollarScale t.1 * x.1 2) ^ 2 +
          (t.1 ^ 2 + (equatorCollarScale t.1 * x.1 3) ^ 2))) = 1
    nlinarith
  nlinarith [norm_nonneg (equatorCollarAmbientMap x.1 t.1)]

def equatorCollarSphereMap (p : Sphere 3 × EquatorCollarInterval) : Sphere 4 :=
  ⟨equatorCollarAmbientMap p.1.1 p.2.1, by
    simpa [mem_sphere_zero_iff_norm] using norm_equatorCollarAmbientMap p.1 p.2⟩

@[simp] theorem equatorCollarSphereMap_coord_three (p : Sphere 3 × EquatorCollarInterval) :
    (equatorCollarSphereMap p).1 3 = p.2.1 := rfl

@[simp] theorem equatorCollarSphereMap_zero (x : Sphere 3) :
    equatorCollarSphereMap
        (x, ⟨0, show (0 : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) by norm_num⟩) =
      equatorSphereMap x := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [equatorCollarSphereMap, equatorCollarAmbientMap,
    equatorCollarScale, equatorSphereMap, equatorAmbientMap]

def equatorCollarRegion : Opens (Sphere 4) :=
  ⟨{y | y.1 3 ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)}, by
    have hcoord : Continuous (fun y : Sphere 4 ↦ y.1 3) := by fun_prop
    exact isOpen_Ioo.preimage hcoord⟩

abbrev EquatorCollarRegion := equatorCollarRegion

def equatorCollarForward (p : Sphere 3 × EquatorCollarInterval) :
    EquatorCollarRegion :=
  ⟨equatorCollarSphereMap p, by
    change p.2.1 ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
    exact p.2.2⟩

@[simp] theorem equatorCollarForward_coe (p : Sphere 3 × EquatorCollarInterval) :
    (equatorCollarForward p : Sphere 4) = equatorCollarSphereMap p := rfl

theorem equatorAmbientProjection_equatorCollarSphereMap
    (p : Sphere 3 × EquatorCollarInterval) :
    equatorAmbientProjection (equatorCollarSphereMap p).1 =
      equatorCollarScale p.2.1 • p.1.1 := by
  ext i
  fin_cases i <;> rfl

def equatorCollarInverseSphere (y : EquatorCollarRegion) : Sphere 3 := by
  let t : ℝ := y.1.1 3
  let s : ℝ := equatorCollarScale t
  let x : EuclideanSpace ℝ (Fin 4) := s⁻¹ • equatorAmbientProjection y.1.1
  have htHalf : t ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := y.2
  have ht : t ∈ Set.Ioo (-(1 : ℝ)) 1 := by
    constructor <;> linarith [htHalf.1, htHalf.2]
  have hspos : 0 < s := equatorCollarScale_pos ht
  have hynorm : ‖y.1.1‖ = 1 := by
    exact mem_sphere_zero_iff_norm.mp y.1.2
  have hprojSq : ‖equatorAmbientProjection y.1.1‖ ^ 2 + t ^ 2 = 1 := by
    simpa [t, hynorm] using norm_equatorAmbientProjection_sq_add_coord_three y.1.1
  have hsSq : s ^ 2 = 1 - t ^ 2 := equatorCollarScale_sq ht
  have hprojNorm : ‖equatorAmbientProjection y.1.1‖ = s := by
    nlinarith [norm_nonneg (equatorAmbientProjection y.1.1)]
  have hxnorm : ‖x‖ = 1 := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hspos, hprojNorm,
      inv_mul_cancel₀ hspos.ne']
  exact ⟨x, by simpa [mem_sphere_zero_iff_norm] using hxnorm⟩

def equatorCollarInverse (y : EquatorCollarRegion) :
    Sphere 3 × EquatorCollarInterval :=
  (equatorCollarInverseSphere y, ⟨y.1.1 3, y.2⟩)

@[simp] theorem equatorCollarInverse_snd (y : EquatorCollarRegion) :
    (equatorCollarInverse y).2.1 = y.1.1 3 := rfl

@[simp] theorem equatorCollarInverseSphere_coe (y : EquatorCollarRegion) :
    (equatorCollarInverseSphere y : EuclideanSpace ℝ (Fin 4)) =
      (equatorCollarScale (y.1.1 3))⁻¹ • equatorAmbientProjection y.1.1 := rfl

theorem equatorCollarInverse_forward (p : Sphere 3 × EquatorCollarInterval) :
    equatorCollarInverse (equatorCollarForward p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    change (equatorCollarInverseSphere (equatorCollarForward p) :
      EuclideanSpace ℝ (Fin 4)) = p.1.1
    rw [equatorCollarInverseSphere_coe]
    change (equatorCollarScale p.2.1)⁻¹ •
      equatorAmbientProjection (equatorCollarSphereMap p).1 = p.1.1
    rw [equatorAmbientProjection_equatorCollarSphereMap,
      smul_smul, inv_mul_cancel₀]
    · simp
    · exact (equatorCollarScale_pos (t := p.2.1) (by
        constructor <;> linarith [p.2.2.1, p.2.2.2])).ne'
  · rfl

theorem equatorCollarForward_inverse (y : EquatorCollarRegion) :
    equatorCollarForward (equatorCollarInverse y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  fin_cases i
  · change equatorCollarScale (y.1.1 3) *
      ((equatorCollarScale (y.1.1 3))⁻¹ * y.1.1 0) = y.1.1 0
    rw [← mul_assoc, mul_inv_cancel₀]
    · simp
    · exact (equatorCollarScale_pos (t := y.1.1 3) (by
        constructor <;> linarith [y.2.1, y.2.2])).ne'
  · change equatorCollarScale (y.1.1 3) *
      ((equatorCollarScale (y.1.1 3))⁻¹ * y.1.1 1) = y.1.1 1
    rw [← mul_assoc, mul_inv_cancel₀]
    · simp
    · exact (equatorCollarScale_pos (t := y.1.1 3) (by
        constructor <;> linarith [y.2.1, y.2.2])).ne'
  · change equatorCollarScale (y.1.1 3) *
      ((equatorCollarScale (y.1.1 3))⁻¹ * y.1.1 2) = y.1.1 2
    rw [← mul_assoc, mul_inv_cancel₀]
    · simp
    · exact (equatorCollarScale_pos (t := y.1.1 3) (by
        constructor <;> linarith [y.2.1, y.2.2])).ne'
  · rfl
  · change equatorCollarScale (y.1.1 3) *
      ((equatorCollarScale (y.1.1 3))⁻¹ * y.1.1 4) = y.1.1 4
    rw [← mul_assoc, mul_inv_cancel₀]
    · simp
    · exact (equatorCollarScale_pos (t := y.1.1 3) (by
        constructor <;> linarith [y.2.1, y.2.2])).ne'

def equatorCollarEquiv :
    (Sphere 3 × EquatorCollarInterval) ≃ EquatorCollarRegion where
  toFun := equatorCollarForward
  invFun := equatorCollarInverse
  left_inv := equatorCollarInverse_forward
  right_inv := equatorCollarForward_inverse

theorem contMDiff_equatorCollarScale :
    ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ∞
      (fun t : EquatorCollarInterval ↦ equatorCollarScale t.1) := by
  intro t
  rw [contMDiffAt_subtype_iff]
  apply ContDiffAt.contMDiffAt
  unfold equatorCollarScale
  apply ContDiffAt.sqrt
  · exact contDiffAt_const.sub (contDiffAt_id.pow 2)
  · have ht : (t : ℝ) ∈ Set.Ioo (-(1 : ℝ)) 1 := by
      constructor <;> linarith [t.2.1, t.2.2]
    have hs := equatorCollarScale_pos ht
    rw [equatorCollarScale, Real.sqrt_pos] at hs
    exact hs.ne'

theorem contMDiff_equatorCollarAmbientMap :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5))) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦
        equatorCollarAmbientMap p.1.1 p.2.1) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let raw : Sphere 3 × EquatorCollarInterval → (Fin 5 → ℝ) :=
    fun p ↦ ![equatorCollarScale p.2.1 * p.1.1 0,
      equatorCollarScale p.2.1 * p.1.1 1,
      equatorCollarScale p.2.1 * p.1.1 2,
      p.2.1,
      equatorCollarScale p.2.1 * p.1.1 3]
  have hx : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.1.1) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  have ht : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.2.1) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hs : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ equatorCollarScale p.2.1) :=
    contMDiff_equatorCollarScale.comp contMDiff_snd
  have hxcoord (j : Fin 4) : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.1.1 j) := by
    have heval : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 4) ↦ x j) := by
      fun_prop
    exact heval.comp_contMDiff hx
  have hmul (j : Fin 4) : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦
        equatorCollarScale p.2.1 * p.1.1 j) := by
    exact (hs.smul (hxcoord j)).congr fun _ ↦ by simp [smul_eq_mul]
  have hraw : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (Fin 5 → ℝ)) ∞ raw := by
    rw [contMDiff_pi_space]
    intro j
    fin_cases j
    · simpa [raw] using hmul 0
    · simpa [raw] using hmul 1
    · simpa [raw] using hmul 2
    · simpa [raw] using ht
    · simpa [raw] using hmul 3
  have htoLp : ContMDiff (modelWithCornersSelf ℝ (Fin 5 → ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5))) ∞
      (WithLp.toLp 2) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 ↦ ℝ)).symm.toContinuousLinearMap.contMDiff
  exact (htoLp.comp hraw).congr fun _ ↦ rfl

theorem contMDiff_equatorCollarSphereMap :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      equatorCollarSphereMap := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  exact (contMDiff_equatorCollarAmbientMap.codRestrict_sphere (n := 4)
    fun p ↦ (equatorCollarSphereMap p).2).congr fun _ ↦ rfl

theorem contMDiff_equatorCollarForward :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      equatorCollarForward := by
  apply (ContMDiff.subtypeVal_comp_iff equatorCollarRegion equatorCollarForward).mp
  exact contMDiff_equatorCollarSphereMap.congr fun _ ↦ rfl

theorem contMDiff_equatorAmbientProjectionOnCollarRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun y : EquatorCollarRegion ↦ equatorAmbientProjection y.1.1) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  have hproj : ContDiff ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin 5) ↦ equatorAmbientProjection y) := by
    unfold equatorAmbientProjection
    rw [contDiff_piLp]
    intro j
    fin_cases j
    · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
      fun_prop
    · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      fun_prop
    · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
      fun_prop
    · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
      fun_prop
  exact hproj.comp_contMDiff (contMDiff_coe_sphere.comp contMDiff_subtype_val)

theorem contMDiff_equatorCollarCoord :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : EquatorCollarRegion ↦ y.1.1 3) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  have hcoord : ContDiff ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin 5) ↦ y 3) := by fun_prop
  exact hcoord.comp_contMDiff (contMDiff_coe_sphere.comp contMDiff_subtype_val)

theorem contMDiff_equatorCollarCoordSubtype :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : EquatorCollarRegion ↦
        (⟨y.1.1 3, y.2⟩ : EquatorCollarInterval)) := by
  apply (ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens _).mp
  exact contMDiff_equatorCollarCoord

theorem contMDiff_equatorCollarScaleOnRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : EquatorCollarRegion ↦ equatorCollarScale (y.1.1 3)) :=
  contMDiff_equatorCollarScale.comp contMDiff_equatorCollarCoordSubtype

theorem contMDiff_equatorCollarInverseRaw :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun y : EquatorCollarRegion ↦
        (equatorCollarScale (y.1.1 3))⁻¹ • equatorAmbientProjection y.1.1) := by
  have hinv : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : EquatorCollarRegion ↦ (equatorCollarScale (y.1.1 3))⁻¹) :=
    contMDiff_equatorCollarScaleOnRegion.inv₀ fun y ↦
      (equatorCollarScale_pos (t := y.1.1 3) (by
        constructor <;> linarith [y.2.1, y.2.2])).ne'
  exact hinv.smul contMDiff_equatorAmbientProjectionOnCollarRegion

theorem contMDiff_equatorCollarInverseSphere :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      equatorCollarInverseSphere := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  exact (contMDiff_equatorCollarInverseRaw.codRestrict_sphere (n := 3)
    fun y ↦ (equatorCollarInverseSphere y).2).congr fun _ ↦ rfl

theorem contMDiff_equatorCollarInverse :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ)) ∞
      equatorCollarInverse :=
  (contMDiff_equatorCollarInverseSphere.prodMk
    contMDiff_equatorCollarCoordSubtype).congr fun _ ↦ rfl

def equatorCollarDiffeomorph :
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ),
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯
      EquatorCollarRegion where
  toEquiv := equatorCollarEquiv
  contMDiff_toFun := contMDiff_equatorCollarForward
  contMDiff_invFun := contMDiff_equatorCollarInverse

theorem equatorCollarSphereMap_not_mem_standardUnlinkCarrier
    (p : Sphere 3 × EquatorCollarInterval) :
    equatorCollarSphereMap p ∉ standardUnlinkCarrier := by
  intro hp
  rcases hp with hp | hp
  · change (equatorCollarSphereMap p).1 3 = -(1 / 2 : ℝ) ∧
      (equatorCollarSphereMap p).1 4 = 0 at hp
    rw [equatorCollarSphereMap_coord_three] at hp
    linarith [p.2.2.1]
  · change (equatorCollarSphereMap p).1 3 = (1 / 2 : ℝ) ∧
      (equatorCollarSphereMap p).1 4 = 0 at hp
    rw [equatorCollarSphereMap_coord_three] at hp
    linarith [p.2.2.2]

def equatorUnlinkCollarRegion : Opens StandardUnlinkComplement :=
  ⟨{y | y.1.1 3 ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)}, by
    have hcoord : Continuous (fun y : StandardUnlinkComplement ↦ y.1.1 3) := by fun_prop
    exact isOpen_Ioo.preimage hcoord⟩

abbrev EquatorUnlinkCollarRegion := equatorUnlinkCollarRegion

def equatorUnlinkCollarForward
    (p : Sphere 3 × EquatorCollarInterval) : EquatorUnlinkCollarRegion :=
  ⟨⟨equatorCollarSphereMap p, equatorCollarSphereMap_not_mem_standardUnlinkCarrier p⟩, by
    change p.2.1 ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
    exact p.2.2⟩

@[simp] theorem equatorUnlinkCollarForward_coe
    (p : Sphere 3 × EquatorCollarInterval) :
    ((equatorUnlinkCollarForward p : StandardUnlinkComplement) : Sphere 4) =
      equatorCollarSphereMap p := rfl

def equatorUnlinkCollarToSphereRegion
    (y : EquatorUnlinkCollarRegion) : EquatorCollarRegion :=
  ⟨y.1.1, y.2⟩

def equatorUnlinkCollarInverse
    (y : EquatorUnlinkCollarRegion) : Sphere 3 × EquatorCollarInterval :=
  equatorCollarInverse (equatorUnlinkCollarToSphereRegion y)

theorem equatorUnlinkCollarInverse_forward
    (p : Sphere 3 × EquatorCollarInterval) :
    equatorUnlinkCollarInverse (equatorUnlinkCollarForward p) = p :=
  equatorCollarInverse_forward p

theorem equatorUnlinkCollarForward_inverse (y : EquatorUnlinkCollarRegion) :
    equatorUnlinkCollarForward (equatorUnlinkCollarInverse y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  change equatorCollarSphereMap (equatorUnlinkCollarInverse y) = y.1.1
  exact congrArg Subtype.val (equatorCollarForward_inverse
    (equatorUnlinkCollarToSphereRegion y))

def equatorUnlinkCollarEquiv :
    (Sphere 3 × EquatorCollarInterval) ≃ EquatorUnlinkCollarRegion where
  toFun := equatorUnlinkCollarForward
  invFun := equatorUnlinkCollarInverse
  left_inv := equatorUnlinkCollarInverse_forward
  right_inv := equatorUnlinkCollarForward_inverse

theorem contMDiff_equatorUnlinkCollarForward :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      equatorUnlinkCollarForward := by
  apply (ContMDiff.subtypeVal_comp_iff equatorUnlinkCollarRegion _).mp
  apply (ContMDiff.subtypeVal_comp_iff standardUnlinkComplementOpens _).mp
  exact contMDiff_equatorCollarSphereMap.congr fun _ ↦ rfl

theorem contMDiff_equatorUnlinkCollarToSphereRegion :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      equatorUnlinkCollarToSphereRegion := by
  apply (ContMDiff.subtypeVal_comp_iff equatorCollarRegion _).mp
  exact (contMDiff_subtype_val.comp contMDiff_subtype_val).congr fun _ ↦ rfl

theorem contMDiff_equatorUnlinkCollarInverse :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ)) ∞
      equatorUnlinkCollarInverse :=
  contMDiff_equatorCollarInverse.comp contMDiff_equatorUnlinkCollarToSphereRegion

def equatorUnlinkCollarDiffeomorph :
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ),
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯
      EquatorUnlinkCollarRegion where
  toEquiv := equatorUnlinkCollarEquiv
  contMDiff_toFun := contMDiff_equatorUnlinkCollarForward
  contMDiff_invFun := contMDiff_equatorUnlinkCollarInverse

def equatorUnlinkCollarCharacter
    (p : Sphere 3 × EquatorCollarInterval) : ℂ :=
  ((p.2.1 - 1 / 2 : ℝ) : ℂ) +
    ((equatorCollarScale p.2.1 * p.1.1 3 : ℝ) : ℂ) * Complex.I

@[simp] theorem standardUnlinkRightDisplacementComplex_equatorCollarSphereMap
    (p : Sphere 3 × EquatorCollarInterval) :
    standardUnlinkRightDisplacementComplex (equatorCollarSphereMap p) =
      equatorUnlinkCollarCharacter p := by
  simp [standardUnlinkRightDisplacementComplex,
    standardUnlinkNormalProjection, standardUnlinkNormalCenter,
    standardUnlinkHeight, unlinkNormalPlaneToComplex,
    Complex.equivRealProdCLM_symm_apply, equatorUnlinkCollarCharacter]
  norm_cast

theorem neg_equatorUnlinkCollarCharacter_mem_slitPlane
    (p : Sphere 3 × EquatorCollarInterval) :
    -equatorUnlinkCollarCharacter p ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp [equatorUnlinkCollarCharacter]
  linarith [p.2.2.2]

def equatorUnlinkCollarPowerRoot (m : ℕ)
    (p : Sphere 3 × EquatorCollarInterval) : ℂ :=
  Complex.exp
    ((Complex.log (-equatorUnlinkCollarCharacter p) +
      (Real.pi : ℂ) * Complex.I) / (m : ℂ))

@[simp] theorem equatorUnlinkCollarPowerRoot_pow
    (m : ℕ) [NeZero m] (p : Sphere 3 × EquatorCollarInterval) :
    equatorUnlinkCollarPowerRoot m p ^ m = equatorUnlinkCollarCharacter p := by
  unfold equatorUnlinkCollarPowerRoot
  rw [← Complex.exp_nat_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [show (m : ℂ) *
      ((Complex.log (-equatorUnlinkCollarCharacter p) +
        (Real.pi : ℂ) * Complex.I) / (m : ℂ)) =
      Complex.log (-equatorUnlinkCollarCharacter p) +
        (Real.pi : ℂ) * Complex.I by field_simp]
  rw [Complex.exp_add, Complex.exp_log
    (Complex.slitPlane_ne_zero
      (neg_equatorUnlinkCollarCharacter_mem_slitPlane p)),
    Complex.exp_pi_mul_I]
  ring

theorem equatorUnlinkCollarPowerRoot_ne_zero (m : ℕ)
    (p : Sphere 3 × EquatorCollarInterval) :
    equatorUnlinkCollarPowerRoot m p ≠ 0 :=
  Complex.exp_ne_zero _

def equatorUnlinkCollarPowerRootTranslate
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) : ℂ :=
  (((standardRootsOfUnityZModMulEquiv m
    (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
      equatorUnlinkCollarPowerRoot m p

@[simp] theorem equatorUnlinkCollarPowerRootTranslate_pow
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    equatorUnlinkCollarPowerRootTranslate m a p ^ m =
      equatorUnlinkCollarCharacter p := by
  rw [equatorUnlinkCollarPowerRootTranslate, mul_pow,
    (mem_rootsOfUnity' m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1).mp
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).2,
    one_mul, equatorUnlinkCollarPowerRoot_pow]

theorem equatorUnlinkCollarPowerRootTranslate_ne_zero
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    equatorUnlinkCollarPowerRootTranslate m a p ≠ 0 :=
  mul_ne_zero
    (Units.ne_zero
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1)
    (equatorUnlinkCollarPowerRoot_ne_zero m p)

def equatorUnlinkCollarPowerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) : {z : ℂ // z ≠ 0} :=
  ⟨equatorUnlinkCollarPowerRootTranslate m a p,
    equatorUnlinkCollarPowerRootTranslate_ne_zero m a p⟩

def equatorUnlinkPowerCollarLift
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) : StandardUnlinkPowerPullback m :=
  ⟨((equatorUnlinkCollarForward p).1,
      equatorUnlinkCollarPowerCoordinate m a p), by
    apply Subtype.ext
    change standardUnlinkRightDisplacementComplex (equatorCollarSphereMap p) =
      equatorUnlinkCollarPowerRootTranslate m a p ^ m
    rw [standardUnlinkRightDisplacementComplex_equatorCollarSphereMap,
      equatorUnlinkCollarPowerRootTranslate_pow]⟩

@[simp] theorem equatorUnlinkPowerCollarLift_proj
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    standardUnlinkPowerPullbackProj m (equatorUnlinkPowerCollarLift m a p) =
      (equatorUnlinkCollarForward p).1 := rfl

@[simp] theorem equatorUnlinkPowerCollarLift_zero
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    equatorUnlinkPowerCollarLift m a
        (x, ⟨0, show (0 : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) by norm_num⟩) =
      equatorUnlinkPowerLift m a x := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact equatorCollarSphereMap_zero x
  · apply Subtype.ext
    change equatorUnlinkCollarPowerRootTranslate m a
        (x, ⟨0, show (0 : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) by norm_num⟩) =
      equatorUnlinkPowerRootTranslate m a x
    unfold equatorUnlinkCollarPowerRootTranslate equatorUnlinkPowerRootTranslate
    congr 1
    unfold equatorUnlinkCollarPowerRoot equatorUnlinkPowerRoot
    congr 3
    simp [equatorUnlinkCollarCharacter, equatorUnlinkCharacter, equatorCollarScale]

theorem contMDiff_equatorUnlinkCollarCharacter :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℂ) ∞
      equatorUnlinkCollarCharacter := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
    ⟨by simp⟩
  have ht : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.2.1) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hx : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.1.1 3) := by
    have hxambient : ContMDiff
        ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
          (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (fun p : Sphere 3 × EquatorCollarInterval ↦ p.1.1) :=
      contMDiff_coe_sphere.comp contMDiff_fst
    have heval : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 3) := by
      fun_prop
    exact heval.comp_contMDiff hxambient
  have hscale : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦
        equatorCollarScale p.2.1) :=
    contMDiff_equatorCollarScale.comp contMDiff_snd
  have hre : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦
        ((p.2.1 - 1 / 2 : ℝ) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp_contMDiff
      (ht.sub contMDiff_const)
  have him : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦
        ((equatorCollarScale p.2.1 * p.1.1 3 : ℝ) : ℂ) * Complex.I) := by
    have hreal : ContMDiff
        ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
          (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : Sphere 3 × EquatorCollarInterval ↦
          equatorCollarScale p.2.1 * p.1.1 3) :=
      (hscale.smul hx).congr fun _ ↦ by simp [smul_eq_mul]
    have hofReal : ContMDiff
        ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
          (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ ℂ) ∞
        (fun p : Sphere 3 × EquatorCollarInterval ↦
          ((equatorCollarScale p.2.1 * p.1.1 3 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp_contMDiff hreal
    have hmulI : ContMDiff
        (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
        (fun z : ℂ ↦ z * Complex.I) :=
      contMDiff_iff_contDiff.mpr (contDiff_id.mul contDiff_const)
    exact hmulI.comp hofReal
  exact hre.add him

theorem contMDiff_equatorUnlinkCollarPowerRoot (m : ℕ) :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℂ) ∞
      (equatorUnlinkCollarPowerRoot m) := by
  intro p
  have hneg : ContDiffAt ℝ ∞ (fun z : ℂ ↦ -z)
      (equatorUnlinkCollarCharacter p) := contDiffAt_id.neg
  have hlog : ContDiffAt ℝ ∞
      (fun z : ℂ ↦ Complex.log (-z))
      (equatorUnlinkCollarCharacter p) :=
    (Complex.contDiffAt_log
      (neg_equatorUnlinkCollarCharacter_mem_slitPlane p))
      |>.restrict_scalars ℝ |>.comp _ hneg
  have harg : ContDiffAt ℝ ∞
      (fun z : ℂ ↦
        (Complex.log (-z) + (Real.pi : ℂ) * Complex.I) / (m : ℂ))
      (equatorUnlinkCollarCharacter p) :=
    (hlog.add contDiffAt_const).div_const _
  have hbranch : ContMDiffAt
      (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : ℂ ↦ Complex.exp
        ((Complex.log (-z) + (Real.pi : ℂ) * Complex.I) / (m : ℂ)))
      (equatorUnlinkCollarCharacter p) :=
    contMDiffAt_iff_contDiffAt.mpr
      ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp _ harg)
  exact hbranch.comp p contMDiff_equatorUnlinkCollarCharacter.contMDiffAt

theorem contMDiff_equatorUnlinkCollarPowerRootTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℂ) ∞
      (equatorUnlinkCollarPowerRootTranslate m a) := by
  let c : ℂ :=
    (((standardRootsOfUnityZModMulEquiv m
      (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ)
  have hmul : ContMDiff
      (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : ℂ ↦ c * z) :=
    contMDiff_iff_contDiff.mpr (contDiff_const.mul contDiff_id)
  exact hmul.comp (contMDiff_equatorUnlinkCollarPowerRoot m)

theorem continuous_equatorUnlinkCollarPowerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (equatorUnlinkCollarPowerCoordinate m a) := by
  apply Continuous.subtype_mk
  exact (contMDiff_equatorUnlinkCollarPowerRootTranslate m a).continuous

theorem continuous_equatorUnlinkPowerCollarLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (equatorUnlinkPowerCollarLift m a) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp
      contMDiff_equatorUnlinkCollarForward.continuous).prodMk
    (continuous_equatorUnlinkCollarPowerCoordinate m a)

theorem contMDiff_equatorUnlinkPowerCollarLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (equatorUnlinkPowerCollarLift m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply contMDiff_of_comp_isLocalDiffeomorph
    ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
      (modelWithCornersSelf ℝ ℝ))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
    (continuous_equatorUnlinkPowerCollarLift m a)
  exact (contMDiff_subtype_val.comp
    contMDiff_equatorUnlinkCollarForward).congr fun _ ↦ rfl

def equatorUnlinkCollarBase
    (p : Sphere 3 × EquatorCollarInterval) : StandardUnlinkComplement :=
  (equatorUnlinkCollarForward p).1

@[simp] theorem equatorUnlinkCollarBase_apply
    (p : Sphere 3 × EquatorCollarInterval) :
    equatorUnlinkCollarBase p = (equatorUnlinkCollarForward p).1 := rfl

theorem isOpenEmbedding_equatorUnlinkCollarBase :
    IsOpenEmbedding equatorUnlinkCollarBase := by
  exact equatorUnlinkCollarRegion.2.isOpenEmbedding_subtypeVal.comp
    equatorUnlinkCollarDiffeomorph.toHomeomorph.isOpenEmbedding

theorem isOpenEmbedding_equatorUnlinkPowerCollarLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsOpenEmbedding (equatorUnlinkPowerCollarLift m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply IsLocalHomeomorph.isOpenEmbedding_of_comp
    (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph.isLocalHomeomorph
  · rw [show standardUnlinkPowerPullbackProj m ∘
        equatorUnlinkPowerCollarLift m a = equatorUnlinkCollarBase by
      funext p
      rfl]
    exact isOpenEmbedding_equatorUnlinkCollarBase
  · exact continuous_equatorUnlinkPowerCollarLift m a

def equatorUnlinkPowerCollarImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Opens (StandardUnlinkPowerPullback m) :=
  ⟨range (equatorUnlinkPowerCollarLift m a),
    (isOpenEmbedding_equatorUnlinkPowerCollarLift m a).isOpen_range⟩

abbrev EquatorUnlinkPowerCollarImage
    (m : ℕ) [NeZero m] (a : ZMod m) :=
  equatorUnlinkPowerCollarImage m a

def equatorUnlinkPowerCollarToImage
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    EquatorUnlinkPowerCollarImage m a :=
  ⟨equatorUnlinkPowerCollarLift m a p, mem_range_self p⟩

def equatorUnlinkPowerCollarImageToBaseRegion
    (m : ℕ) [NeZero m] (a : ZMod m)
    (q : EquatorUnlinkPowerCollarImage m a) : EquatorUnlinkCollarRegion :=
  ⟨standardUnlinkPowerPullbackProj m q.1, by
    rcases q.2 with ⟨p, hp⟩
    rw [← hp]
    exact (equatorUnlinkCollarForward p).2⟩

def equatorUnlinkPowerCollarFromImage
    (m : ℕ) [NeZero m] (a : ZMod m)
    (q : EquatorUnlinkPowerCollarImage m a) :
    Sphere 3 × EquatorCollarInterval :=
  equatorUnlinkCollarInverse
    (equatorUnlinkPowerCollarImageToBaseRegion m a q)

theorem equatorUnlinkPowerCollarFromImage_toImage
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    equatorUnlinkPowerCollarFromImage m a
      (equatorUnlinkPowerCollarToImage m a p) = p :=
  equatorUnlinkCollarInverse_forward p

theorem equatorUnlinkPowerCollarToImage_fromImage
    (m : ℕ) [NeZero m] (a : ZMod m)
    (q : EquatorUnlinkPowerCollarImage m a) :
    equatorUnlinkPowerCollarToImage m a
      (equatorUnlinkPowerCollarFromImage m a q) = q := by
  rcases q.2 with ⟨p, hp⟩
  have hq : q = equatorUnlinkPowerCollarToImage m a p := by
    apply Subtype.ext
    exact hp.symm
  subst q
  apply Subtype.ext
  change equatorUnlinkPowerCollarLift m a
      (equatorUnlinkPowerCollarFromImage m a
        (equatorUnlinkPowerCollarToImage m a p)) =
    equatorUnlinkPowerCollarLift m a p
  rw [equatorUnlinkPowerCollarFromImage_toImage]

def equatorUnlinkPowerCollarEquiv
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (Sphere 3 × EquatorCollarInterval) ≃
      EquatorUnlinkPowerCollarImage m a where
  toFun := equatorUnlinkPowerCollarToImage m a
  invFun := equatorUnlinkPowerCollarFromImage m a
  left_inv := equatorUnlinkPowerCollarFromImage_toImage m a
  right_inv := equatorUnlinkPowerCollarToImage_fromImage m a

theorem contMDiff_equatorUnlinkPowerCollarToImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (equatorUnlinkPowerCollarToImage m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  rw [← ContMDiff.subtypeVal_comp_iff
    (equatorUnlinkPowerCollarImage m a)]
  exact contMDiff_equatorUnlinkPowerCollarLift m a

theorem contMDiff_equatorUnlinkPowerCollarImageToBaseRegion
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (equatorUnlinkPowerCollarImageToBaseRegion m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  rw [← ContMDiff.subtypeVal_comp_iff equatorUnlinkCollarRegion]
  exact ((smoothCover_standardUnlinkPowerPullbackProj m).contMDiff.comp
    contMDiff_subtype_val).congr fun _ ↦ rfl

theorem contMDiff_equatorUnlinkPowerCollarFromImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ)) ∞
      (equatorUnlinkPowerCollarFromImage m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact equatorUnlinkCollarDiffeomorph.symm.contMDiff.comp
    (contMDiff_equatorUnlinkPowerCollarImageToBaseRegion m a)

def equatorUnlinkPowerCollarDiffeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ)),
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯
      EquatorUnlinkPowerCollarImage m a := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact {
    toEquiv := equatorUnlinkPowerCollarEquiv m a
    contMDiff_toFun := contMDiff_equatorUnlinkPowerCollarToImage m a
    contMDiff_invFun := contMDiff_equatorUnlinkPowerCollarFromImage m a }

@[simp] theorem equatorUnlinkPowerCollarDiffeomorph_apply_coe
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    (equatorUnlinkPowerCollarDiffeomorph m a p :
      StandardUnlinkPowerPullback m) =
      equatorUnlinkPowerCollarLift m a p := rfl

@[simp] theorem equatorUnlinkPowerCollarDiffeomorph_zero_coe
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    (equatorUnlinkPowerCollarDiffeomorph m a
      (x, ⟨0, show (0 : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) by
        norm_num⟩) : StandardUnlinkPowerPullback m) =
      equatorUnlinkPowerLift m a x := by
  rw [equatorUnlinkPowerCollarDiffeomorph_apply_coe,
    equatorUnlinkPowerCollarLift_zero]

theorem injective_equatorUnlinkPowerCollarLift_family
    (m : ℕ) [NeZero m] :
    Function.Injective
      (fun z : ZMod m × (Sphere 3 × EquatorCollarInterval) ↦
        equatorUnlinkPowerCollarLift m z.1 z.2) := by
  rintro ⟨a, p⟩ ⟨b, q⟩ hab
  have hbase := congrArg (standardUnlinkPowerPullbackProj m) hab
  have hpq : p = q := isOpenEmbedding_equatorUnlinkCollarBase.injective <| by
    simpa only [equatorUnlinkPowerCollarLift_proj,
      equatorUnlinkCollarBase] using hbase
  subst q
  have hval := congrArg
    (fun z : StandardUnlinkPowerPullback m ↦ z.1.2.1) hab
  have hroot :
      (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) =
        (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd b)).1 : ℂˣ) : ℂ) := by
    apply mul_right_cancel₀ (equatorUnlinkCollarPowerRoot_ne_zero m p)
    exact hval
  have hroots :
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) =
        standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b) := by
    apply Subtype.ext
    apply Units.ext
    exact hroot
  have hab' : a = b := Multiplicative.ofAdd.injective <|
    (standardRootsOfUnityZModMulEquiv m).injective hroots
  exact Prod.ext hab' rfl

theorem pairwise_disjoint_equatorUnlinkPowerCollarImage
    (m : ℕ) [NeZero m] :
    Pairwise fun a b : ZMod m ↦
      Disjoint (equatorUnlinkPowerCollarImage m a :
        Set (StandardUnlinkPowerPullback m))
        (equatorUnlinkPowerCollarImage m b :
          Set (StandardUnlinkPowerPullback m)) := by
  intro a b hab
  rw [Set.disjoint_left]
  intro z hza hzb
  obtain ⟨p, hp⟩ := hza
  obtain ⟨q, hq⟩ := hzb
  have hpq : (a, p) = (b, q) :=
    injective_equatorUnlinkPowerCollarLift_family m (hp.trans hq.symm)
  exact hab (congrArg Prod.fst hpq)

theorem range_equatorUnlinkPowerLift_subset_collarImage
    (m : ℕ) [NeZero m] (a : ZMod m) :
    range (equatorUnlinkPowerLift m a) ⊆
      (equatorUnlinkPowerCollarImage m a :
        Set (StandardUnlinkPowerPullback m)) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨(x, ⟨0, ?_⟩), ?_⟩
  · change (0 : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
    norm_num
  · exact equatorUnlinkPowerCollarLift_zero m a x

end

end SplittingSpheres
