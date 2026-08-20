/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Radially extending a unit-sphere homeomorphism

A homeomorphism of the unit sphere of a real normed space extends radially to the whole space:
the radius is unchanged and only the unit direction is moved.  The formula is continuous at the
origin because it preserves norms exactly.  Restricting the extension gives a homeomorphism of
the closed unit ball whose boundary action is the original sphere homeomorphism.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unit direction of a nonzero vector. -/
def nonzeroUnitDirection (x : {x : E // x ≠ 0}) : sphere (0 : E) 1 :=
  ⟨NormedSpace.normalize x.1, by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize x.2⟩

@[simp]
theorem nonzeroUnitDirection_coe (x : {x : E // x ≠ 0}) :
    (nonzeroUnitDirection x : E) = NormedSpace.normalize x.1 :=
  rfl

theorem continuous_nonzeroUnitDirection :
    Continuous (nonzeroUnitDirection : {x : E // x ≠ 0} → sphere (0 : E) 1) := by
  apply Continuous.subtype_mk
  unfold NormedSpace.normalize
  have hnorm : Continuous (fun x : {x : E // x ≠ 0} ↦ ‖x.1‖) :=
    continuous_norm.comp continuous_subtype_val
  exact hnorm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr x.2) |>.smul continuous_subtype_val

/-- Extend a unit-sphere homeomorphism radially, fixing the origin. -/
def radialSphereExtensionMap
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : E) : E := by
  classical
  exact if hx : x = 0 then 0
    else ‖x‖ • (e (nonzeroUnitDirection ⟨x, hx⟩)).1

@[simp]
theorem radialSphereExtensionMap_zero
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    radialSphereExtensionMap e (0 : E) = 0 := by
  simp [radialSphereExtensionMap]

theorem radialSphereExtensionMap_of_ne_zero
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1)
    {x : E} (hx : x ≠ 0) :
    radialSphereExtensionMap e x =
      ‖x‖ • (e (nonzeroUnitDirection ⟨x, hx⟩)).1 := by
  simp [radialSphereExtensionMap, hx]

@[simp]
theorem norm_radialSphereExtensionMap
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : E) :
    ‖radialSphereExtensionMap e x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [radialSphereExtensionMap_of_ne_zero e hx, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x),
      mem_sphere_zero_iff_norm.mp (e (nonzeroUnitDirection ⟨x, hx⟩)).2, mul_one]

theorem radialSphereExtensionMap_ne_zero_iff
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : E) :
    radialSphereExtensionMap e x ≠ 0 ↔ x ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_radialSphereExtensionMap, norm_ne_zero_iff]

/-- Away from the origin, the radial extension is a composite of continuous norm,
normalization, and the supplied sphere homeomorphism. -/
theorem continuousOn_radialSphereExtensionMap_compl_zero
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    ContinuousOn (radialSphereExtensionMap e) ({0} : Set E)ᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  let direction : ↥(({0} : Set E)ᶜ) → sphere (0 : E) 1 := fun x ↦
    nonzeroUnitDirection ⟨x.1, by
      intro hx
      exact x.2 (by simp [hx])⟩
  have hdirection : Continuous direction := by
    exact continuous_nonzeroUnitDirection.comp <|
      continuous_subtype_val.subtype_mk _
  have hformula :
      (({0} : Set E)ᶜ).domRestrict (radialSphereExtensionMap e) =
        fun x ↦ ‖x.1‖ • (e (direction x)).1 := by
    funext x
    apply radialSphereExtensionMap_of_ne_zero
  rw [hformula]
  exact (continuous_norm.comp continuous_subtype_val).smul <|
    continuous_subtype_val.comp (e.continuous.comp hdirection)

/-- The radial extension is continuous at the origin because it preserves the norm. -/
theorem continuousAt_radialSphereExtensionMap_zero
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    ContinuousAt (radialSphereExtensionMap e) (0 : E) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx
  simpa [dist_zero_right, norm_radialSphereExtensionMap] using hx

theorem continuous_radialSphereExtensionMap
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    Continuous (radialSphereExtensionMap e) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simpa [hx] using continuousAt_radialSphereExtensionMap_zero e
  · exact (continuousOn_radialSphereExtensionMap_compl_zero e).continuousAt <|
      isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hx)

theorem radialSphereExtensionMap_symm_leftInverse
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    LeftInverse (radialSphereExtensionMap e.symm) (radialSphereExtensionMap e) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hforward : radialSphereExtensionMap e x =
        ‖x‖ • (e (nonzeroUnitDirection ⟨x, hx⟩)).1 :=
      radialSphereExtensionMap_of_ne_zero e hx
    have hforward_ne : radialSphereExtensionMap e x ≠ 0 :=
      (radialSphereExtensionMap_ne_zero_iff e x).2 hx
    rw [radialSphereExtensionMap_of_ne_zero e.symm hforward_ne,
      norm_radialSphereExtensionMap]
    have hunit :
        NormedSpace.normalize
            (‖x‖ • (e (nonzeroUnitDirection ⟨x, hx⟩)).1) =
          (e (nonzeroUnitDirection ⟨x, hx⟩)).1 := by
      rw [NormedSpace.normalize_smul_of_pos hxnorm]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one <|
        mem_sphere_zero_iff_norm.mp (e (nonzeroUnitDirection ⟨x, hx⟩)).2
    have hdirection :
        nonzeroUnitDirection
            ⟨radialSphereExtensionMap e x, hforward_ne⟩ =
          e (nonzeroUnitDirection ⟨x, hx⟩) := by
      apply Subtype.ext
      change NormedSpace.normalize (radialSphereExtensionMap e x) = _
      rw [hforward]
      exact hunit
    rw [hdirection, e.symm_apply_apply]
    exact NormedSpace.norm_smul_normalize x

theorem radialSphereExtensionMap_symm_rightInverse
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    RightInverse (radialSphereExtensionMap e.symm) (radialSphereExtensionMap e) :=
  radialSphereExtensionMap_symm_leftInverse e.symm

/-- The global radial extension of a unit-sphere homeomorphism. -/
def radialSphereExtensionHomeomorph
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) : E ≃ₜ E where
  toFun := radialSphereExtensionMap e
  invFun := radialSphereExtensionMap e.symm
  left_inv := radialSphereExtensionMap_symm_leftInverse e
  right_inv := radialSphereExtensionMap_symm_rightInverse e
  continuous_toFun := continuous_radialSphereExtensionMap e
  continuous_invFun := continuous_radialSphereExtensionMap e.symm

@[simp]
theorem radialSphereExtensionHomeomorph_apply
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : E) :
    radialSphereExtensionHomeomorph e x = radialSphereExtensionMap e x :=
  rfl

theorem image_radialSphereExtensionHomeomorph_closedBall
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    radialSphereExtensionHomeomorph e '' closedBall (0 : E) 1 =
      closedBall (0 : E) 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mem_closedBall_zero_iff, norm_radialSphereExtensionMap] using hy
  · intro hx
    refine ⟨radialSphereExtensionHomeomorph e |>.symm x, ?_,
      (radialSphereExtensionHomeomorph e).apply_symm_apply x⟩
    rw [mem_closedBall_zero_iff]
    change ‖radialSphereExtensionMap e.symm x‖ ≤ 1
    simpa [norm_radialSphereExtensionMap] using hx

/-- Restriction of the radial extension to the closed unit ball. -/
def radialSphereExtensionBallHomeomorph
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1 :=
  ((radialSphereExtensionHomeomorph e).image (closedBall (0 : E) 1)).trans <|
    Homeomorph.setCongr (image_radialSphereExtensionHomeomorph_closedBall e)

@[simp]
theorem radialSphereExtensionBallHomeomorph_apply_val
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1)
    (x : closedBall (0 : E) 1) :
    (radialSphereExtensionBallHomeomorph e x).1 =
      radialSphereExtensionMap e x.1 :=
  rfl

/-- On the unit sphere, the radial extension is exactly the original homeomorphism. -/
@[simp]
theorem radialSphereExtensionMap_of_mem_sphere
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1)
    (u : sphere (0 : E) 1) :
    radialSphereExtensionMap e u.1 = (e u).1 := by
  have hu : u.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, mem_sphere_zero_iff_norm.mp u.2]
    norm_num
  rw [radialSphereExtensionMap_of_ne_zero e hu,
    mem_sphere_zero_iff_norm.mp u.2, one_smul]
  have hdirection : nonzeroUnitDirection ⟨u.1, hu⟩ = u := by
    apply Subtype.ext
    exact NormedSpace.normalize_eq_self_of_norm_eq_one <|
      mem_sphere_zero_iff_norm.mp u.2
  rw [hdirection]

end SplittingSpheres
