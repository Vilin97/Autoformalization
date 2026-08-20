/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homeomorph.Lemmas
public import SplittingSpheres.Handlebody.BoundaryAttachment

/-!
# A direct handle decomposition of the four-sphere

This file identifies the topological pushout
`(S¹ × B³) ∪_{S¹ × S²} (D² × S²)` with the project's literal `Sphere 4`.  Both face maps are
given directly in the coordinate splitting `ℝ⁵ = ℝ² ⊕ ℝ³`, at radius `1 / √2`.

Mathlib equips an ordinary product of normed spaces with the supremum norm.  We therefore do not
treat `EuclideanSpace.finAddEquivProd` as an isometry into that product.  Instead, the Euclidean
sum-of-squares identity is proved by factoring it through the `WithLp 2` product used in its
definition.

Everything in this file is topological.  In particular, no smoothness, collar, boundary
orientation, or smooth-gluing statement is asserted.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-- The first, two-dimensional block of the Euclidean coordinate splitting. -/
abbrev SphereHandleFirst : Type := EuclideanSpace ℝ (Fin 2)

/-- The second, three-dimensional block of the Euclidean coordinate splitting. -/
abbrev SphereHandleSecond : Type := EuclideanSpace ℝ (Fin 3)

/-- The five-dimensional Euclidean ambient space of `Sphere 4`. -/
abbrev SphereHandleAmbient : Type := EuclideanSpace ℝ (Fin (2 + 3))

/-- The canonical coordinate splitting of Euclidean five-space. -/
abbrev sphereHandleSplitEquiv :
    SphereHandleAmbient ≃L[ℝ] SphereHandleFirst × SphereHandleSecond :=
  EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 3)

/-- The `L²`-normed version of the coordinate splitting, before forgetting to the ordinary
product topology. -/
private abbrev sphereHandleL2SplitEquiv :
    SphereHandleAmbient ≃ₗᵢ[ℝ] WithLp 2 (SphereHandleFirst × SphereHandleSecond) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ))

/-- Forget the `L²` product norm while retaining its underlying product coordinates. -/
private abbrev sphereHandleForgetL2Equiv :
    WithLp 2 (SphereHandleFirst × SphereHandleSecond) ≃L[ℝ]
      SphereHandleFirst × SphereHandleSecond :=
  WithLp.prodContinuousLinearEquiv 2 ℝ SphereHandleFirst SphereHandleSecond

/-- Although the ordinary product on the right has the supremum norm, the inverse coordinate
splitting has the expected Euclidean sum-of-squares formula. -/
theorem sphereHandleSplitEquiv_symm_norm_sq
    (u : SphereHandleFirst) (v : SphereHandleSecond) :
    ‖sphereHandleSplitEquiv.symm (u, v)‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  change ‖sphereHandleL2SplitEquiv.symm
    (sphereHandleForgetL2Equiv.symm (u, v))‖ ^ 2 = _
  rw [sphereHandleL2SplitEquiv.symm.norm_map]
  exact WithLp.prod_norm_sq_eq_of_L2 (sphereHandleForgetL2Equiv.symm (u, v))

/-- The forward coordinate splitting also satisfies the Euclidean sum-of-squares formula. -/
theorem sphereHandleSplitEquiv_norm_sq (q : SphereHandleAmbient) :
    ‖(sphereHandleSplitEquiv q).1‖ ^ 2 + ‖(sphereHandleSplitEquiv q).2‖ ^ 2 =
      ‖q‖ ^ 2 := by
  change ‖(sphereHandleForgetL2Equiv (sphereHandleL2SplitEquiv q)).1‖ ^ 2 +
    ‖(sphereHandleForgetL2Equiv (sphereHandleL2SplitEquiv q)).2‖ ^ 2 = _
  have h := WithLp.prod_norm_sq_eq_of_L2 (sphereHandleL2SplitEquiv q)
  rw [sphereHandleL2SplitEquiv.norm_map] at h
  exact h.symm

/-- The two block norms of a point on the literal unit four-sphere have squared sum one. -/
theorem sphereHandleSplitEquiv_sphere_norm_sq (q : Sphere 4) :
    ‖(sphereHandleSplitEquiv q.1).1‖ ^ 2 + ‖(sphereHandleSplitEquiv q.1).2‖ ^ 2 =
      1 := by
  calc
    _ = ‖q.1‖ ^ 2 := sphereHandleSplitEquiv_norm_sq q.1
    _ = 1 := by rw [mem_sphere_zero_iff_norm.mp q.2]; norm_num

/-- The radius at which the two solid faces meet on the unit four-sphere. -/
def sphereHandleRadius : ℝ := 1 / Real.sqrt 2

theorem sphereHandleRadius_pos : 0 < sphereHandleRadius := by
  exact div_pos zero_lt_one (Real.sqrt_pos.2 (by norm_num))

theorem sphereHandleRadius_ne_zero : sphereHandleRadius ≠ 0 :=
  sphereHandleRadius_pos.ne'

@[simp]
theorem sphereHandleRadius_sq : sphereHandleRadius ^ 2 = (1 / 2 : ℝ) := by
  rw [sphereHandleRadius, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem sphereHandleRadius_le_one : sphereHandleRadius ≤ 1 := by
  rw [← sq_le_sq₀ sphereHandleRadius_pos.le zero_le_one, sphereHandleRadius_sq]
  norm_num

/-- The complementary radial scale used in both face parameterizations. -/
def sphereHandleScale (t : ℝ) : ℝ :=
  Real.sqrt (1 - sphereHandleRadius ^ 2 * t ^ 2)

theorem continuous_sphereHandleScale : Continuous sphereHandleScale := by
  unfold sphereHandleScale
  fun_prop

theorem sphereHandleScale_nonneg (t : ℝ) : 0 ≤ sphereHandleScale t :=
  Real.sqrt_nonneg _

private theorem sphereHandleRadicand_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ 1 - sphereHandleRadius ^ 2 * t ^ 2 := by
  have ht2 : t ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ ht0 zero_le_one).2 ht1
  rw [sphereHandleRadius_sq]
  nlinarith

@[simp]
theorem sphereHandleScale_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sphereHandleScale t ^ 2 = 1 - sphereHandleRadius ^ 2 * t ^ 2 :=
  Real.sq_sqrt (sphereHandleRadicand_nonneg ht0 ht1)

theorem sphereHandleScale_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < sphereHandleScale t := by
  apply Real.sqrt_pos.2
  have ht2 : t ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ ht0 zero_le_one).2 ht1
  rw [sphereHandleRadius_sq]
  nlinarith

@[simp]
theorem sphereHandleScale_one : sphereHandleScale 1 = sphereHandleRadius := by
  apply (sq_eq_sq₀ (sphereHandleScale_nonneg _) sphereHandleRadius_pos.le).mp
  rw [sphereHandleScale_sq zero_le_one le_rfl, sphereHandleRadius_sq]
  ring

/-- The raw Euclidean parameterization of the `S¹ × B³` face. -/
def oneHandleSphereRaw (x : OneHandlePiece) : SphereHandleAmbient :=
  sphereHandleSplitEquiv.symm
    (sphereHandleScale ‖x.2.1‖ • x.1.1, sphereHandleRadius • x.2.1)

/-- The raw Euclidean parameterization of the `D² × S²` face. -/
def capSphereRaw (x : CapPiece) : SphereHandleAmbient :=
  sphereHandleSplitEquiv.symm
    (sphereHandleRadius • x.1.1, sphereHandleScale ‖x.1.1‖ • x.2.1)

theorem oneHandleSphereRaw_norm (x : OneHandlePiece) : ‖oneHandleSphereRaw x‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [oneHandleSphereRaw, sphereHandleSplitEquiv_symm_norm_sq]
  have hz : ‖x.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.1.2
  have hb : ‖x.2.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2.2
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sphereHandleScale_nonneg _), abs_of_nonneg sphereHandleRadius_pos.le,
    hz, mul_one, sphereHandleScale_sq (norm_nonneg _) hb]
  ring

theorem capSphereRaw_norm (x : CapPiece) : ‖capSphereRaw x‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [capSphereRaw, sphereHandleSplitEquiv_symm_norm_sq]
  have ha : ‖x.1.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.1.2
  have hw : ‖x.2.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2.2
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg sphereHandleRadius_pos.le, abs_of_nonneg (sphereHandleScale_nonneg _),
    hw, mul_one, sphereHandleScale_sq (norm_nonneg _) ha]
  ring

theorem continuous_oneHandleSphereRaw : Continuous oneHandleSphereRaw := by
  apply sphereHandleSplitEquiv.symm.continuous.comp
  have hscale : Continuous (fun x : OneHandlePiece ↦ sphereHandleScale ‖x.2.1‖) :=
    continuous_sphereHandleScale.comp
      (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))
  have hz : Continuous (fun x : OneHandlePiece ↦ x.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hb : Continuous (fun x : OneHandlePiece ↦ x.2.1) :=
    continuous_subtype_val.comp continuous_snd
  exact (hscale.smul hz).prodMk
    ((continuous_const : Continuous (fun _ : OneHandlePiece ↦ sphereHandleRadius)).smul hb)

theorem continuous_capSphereRaw : Continuous capSphereRaw := by
  apply sphereHandleSplitEquiv.symm.continuous.comp
  have hscale : Continuous (fun x : CapPiece ↦ sphereHandleScale ‖x.1.1‖) :=
    continuous_sphereHandleScale.comp
      (continuous_norm.comp (continuous_subtype_val.comp continuous_fst))
  have ha : Continuous (fun x : CapPiece ↦ x.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hw : Continuous (fun x : CapPiece ↦ x.2.1) :=
    continuous_subtype_val.comp continuous_snd
  exact
    ((continuous_const : Continuous (fun _ : CapPiece ↦ sphereHandleRadius)).smul ha).prodMk
      (hscale.smul hw)

/-- The direct continuous parameterization of the `S¹ × B³` face in the literal four-sphere. -/
def oneHandleSphereMap : C(OneHandlePiece, Sphere 4) where
  toFun x := ⟨oneHandleSphereRaw x, mem_sphere_zero_iff_norm.mpr (oneHandleSphereRaw_norm x)⟩
  continuous_toFun := continuous_oneHandleSphereRaw.subtype_mk _

/-- The direct continuous parameterization of the `D² × S²` face in the literal four-sphere. -/
def sphereHandleCapMap : C(CapPiece, Sphere 4) where
  toFun x := ⟨capSphereRaw x, mem_sphere_zero_iff_norm.mpr (capSphereRaw_norm x)⟩
  continuous_toFun := continuous_capSphereRaw.subtype_mk _

@[simp]
theorem oneHandleSphereMap_coe (x : OneHandlePiece) :
    (oneHandleSphereMap x : SphereHandleAmbient) = oneHandleSphereRaw x :=
  rfl

@[simp]
theorem sphereHandleCapMap_coe (x : CapPiece) :
    (sphereHandleCapMap x : SphereHandleAmbient) = capSphereRaw x :=
  rfl

@[simp]
theorem sphereHandleSplitEquiv_oneHandleSphereMap (x : OneHandlePiece) :
    sphereHandleSplitEquiv (oneHandleSphereMap x).1 =
      (sphereHandleScale ‖x.2.1‖ • x.1.1, sphereHandleRadius • x.2.1) := by
  change sphereHandleSplitEquiv
    (sphereHandleSplitEquiv.symm
      (sphereHandleScale ‖x.2.1‖ • x.1.1, sphereHandleRadius • x.2.1)) = _
  exact sphereHandleSplitEquiv.apply_symm_apply _

@[simp]
theorem sphereHandleSplitEquiv_sphereHandleCapMap (x : CapPiece) :
    sphereHandleSplitEquiv (sphereHandleCapMap x).1 =
      (sphereHandleRadius • x.1.1, sphereHandleScale ‖x.1.1‖ • x.2.1) := by
  change sphereHandleSplitEquiv
    (sphereHandleSplitEquiv.symm
      (sphereHandleRadius • x.1.1, sphereHandleScale ‖x.1.1‖ • x.2.1)) = _
  exact sphereHandleSplitEquiv.apply_symm_apply _

private theorem sphereHandle_nonzero_smul_injective {E : Type*}
    [AddCommGroup E] [Module ℝ E] {c : ℝ} (hc : c ≠ 0) :
    Injective (fun x : E ↦ c • x) := by
  intro x y h
  have := congr_arg (fun z ↦ c⁻¹ • z) h
  simpa only [inv_smul_smul₀ hc] using this

/-- The one-handle face parameterization is injective. -/
theorem oneHandleSphereMap_injective : Injective oneHandleSphereMap := by
  intro x y h
  have hraw : oneHandleSphereRaw x = oneHandleSphereRaw y := congr_arg Subtype.val h
  have hp := sphereHandleSplitEquiv.symm.injective hraw
  have hbscaled := congr_arg Prod.snd hp
  have hb : x.2.1 = y.2.1 :=
    sphereHandle_nonzero_smul_injective sphereHandleRadius_ne_zero hbscaled
  apply Prod.ext
  · apply Subtype.ext
    have hzscaled := congr_arg Prod.fst hp
    rw [← hb] at hzscaled
    exact sphereHandle_nonzero_smul_injective
      (sphereHandleScale_pos (norm_nonneg _)
        (mem_closedBall_zero_iff.mp x.2.2)).ne' hzscaled
  · exact Subtype.ext hb

/-- The cap-face parameterization is injective. -/
theorem sphereHandleCapMap_injective : Injective sphereHandleCapMap := by
  intro x y h
  have hraw : capSphereRaw x = capSphereRaw y := congr_arg Subtype.val h
  have hp := sphereHandleSplitEquiv.symm.injective hraw
  have hascaled := congr_arg Prod.fst hp
  have ha : x.1.1 = y.1.1 :=
    sphereHandle_nonzero_smul_injective sphereHandleRadius_ne_zero hascaled
  apply Prod.ext
  · exact Subtype.ext ha
  · apply Subtype.ext
    have hwscaled := congr_arg Prod.snd hp
    rw [← ha] at hwscaled
    exact sphereHandle_nonzero_smul_injective
      (sphereHandleScale_pos (norm_nonneg _)
        (mem_closedBall_zero_iff.mp x.1.2)).ne' hwscaled

/-- The two direct face maps agree exactly on their common coordinate boundary. -/
theorem oneHandleSphereMap_boundary_agreement (y : OneHandleCapBoundary) :
    oneHandleSphereMap (oneHandleBoundaryInclusion y) =
      sphereHandleCapMap (capBoundaryInclusion y) := by
  apply Subtype.ext
  apply sphereHandleSplitEquiv.injective
  have hy1 : ‖y.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp y.1.2
  have hy2 : ‖y.2.1‖ = 1 := mem_sphere_zero_iff_norm.mp y.2.2
  rw [sphereHandleSplitEquiv_oneHandleSphereMap,
    sphereHandleSplitEquiv_sphereHandleCapMap]
  simp [hy1, hy2]

/-- A point of the one-handle face and a point of the cap face have the same spherical image
exactly when both come from one common boundary point. -/
theorem oneHandleSphereMap_eq_sphereHandleCapMap_iff
    (x : OneHandlePiece) (y : CapPiece) :
    oneHandleSphereMap x = sphereHandleCapMap y ↔
      ∃ z : OneHandleCapBoundary,
        oneHandleBoundaryInclusion z = x ∧ capBoundaryInclusion z = y := by
  constructor
  · intro h
    have hraw : oneHandleSphereRaw x = capSphereRaw y := congr_arg Subtype.val h
    have hp := sphereHandleSplitEquiv.symm.injective hraw
    have hu := congr_arg Prod.fst hp
    have hv := congr_arg Prod.snd hp
    have hbnorm : ‖x.2.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2.2
    have hanorm : ‖y.1.1‖ ≤ 1 := mem_closedBall_zero_iff.mp y.1.2
    have hznorm : ‖x.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.1.2
    have hwnorm : ‖y.2.1‖ = 1 := mem_sphere_zero_iff_norm.mp y.2.2
    have hunorm := congr_arg norm hu
    have hvnorm := congr_arg norm hv
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sphereHandleScale_nonneg _),
      abs_of_nonneg sphereHandleRadius_pos.le, hznorm, mul_one] at hunorm
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg sphereHandleRadius_pos.le,
      abs_of_nonneg (sphereHandleScale_nonneg _), hwnorm, mul_one] at hvnorm
    have hbsq : ‖x.2.1‖ ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hbnorm
    have hasq : ‖y.1.1‖ ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hanorm
    have hsum : ‖x.2.1‖ ^ 2 + ‖y.1.1‖ ^ 2 = 2 := by
      have husq := congr_arg (fun t : ℝ ↦ t ^ 2) hunorm
      rw [sphereHandleScale_sq (norm_nonneg _) hbnorm,
        mul_pow, sphereHandleRadius_sq] at husq
      nlinarith
    have hbsq_eq : ‖x.2.1‖ ^ 2 = 1 := by nlinarith
    have hasq_eq : ‖y.1.1‖ ^ 2 = 1 := by nlinarith
    have hbnorm_eq : ‖x.2.1‖ = 1 :=
      (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hbsq_eq)
    have hanorm_eq : ‖y.1.1‖ = 1 :=
      (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hasq_eq)
    have hza : x.1.1 = y.1.1 := by
      rw [hbnorm_eq, sphereHandleScale_one] at hu
      exact sphereHandle_nonzero_smul_injective sphereHandleRadius_ne_zero hu
    have hbw : x.2.1 = y.2.1 := by
      rw [hanorm_eq, sphereHandleScale_one] at hv
      exact sphereHandle_nonzero_smul_injective sphereHandleRadius_ne_zero hv
    let z : OneHandleCapBoundary :=
      (x.1, ⟨x.2.1, mem_sphere_zero_iff_norm.mpr hbnorm_eq⟩)
    refine ⟨z, ?_, ?_⟩
    · apply Prod.ext
      · rfl
      · exact Subtype.ext rfl
    · apply Prod.ext
      · exact Subtype.ext hza
      · exact Subtype.ext hbw
  · rintro ⟨z, rfl, rfl⟩
    exact oneHandleSphereMap_boundary_agreement z

/-- A spherical point whose second block has norm at most `1 / √2` lies in the one-handle
face image. -/
theorem exists_oneHandleSphereMap_eq_of_second_norm_le
    (q : Sphere 4)
    (hv : ‖(sphereHandleSplitEquiv q.1).2‖ ≤ sphereHandleRadius) :
    ∃ x : OneHandlePiece, oneHandleSphereMap x = q := by
  let u : SphereHandleFirst := (sphereHandleSplitEquiv q.1).1
  let v : SphereHandleSecond := (sphereHandleSplitEquiv q.1).2
  have hsum : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1 := sphereHandleSplitEquiv_sphere_norm_sq q
  have hvsq : ‖v‖ ^ 2 ≤ sphereHandleRadius ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le).2 hv
  have hu_sq_pos : 0 < ‖u‖ ^ 2 := by
    rw [sphereHandleRadius_sq] at hvsq
    nlinarith
  have hu_pos : 0 < ‖u‖ :=
    lt_of_le_of_ne (norm_nonneg _) (sq_pos_iff.mp hu_sq_pos).symm
  have hbmem : ‖sphereHandleRadius⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr sphereHandleRadius_pos)]
    exact (inv_mul_le_one₀ sphereHandleRadius_pos).2 hv
  have hznorm : ‖‖u‖⁻¹ • u‖ = 1 := by
    simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu_pos.ne']
  have hbnorm : ‖sphereHandleRadius⁻¹ • v‖ = sphereHandleRadius⁻¹ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr sphereHandleRadius_pos)]
  have hscale : sphereHandleScale ‖sphereHandleRadius⁻¹ • v‖ = ‖u‖ := by
    apply (sq_eq_sq₀ (sphereHandleScale_nonneg _) (norm_nonneg _)).mp
    rw [sphereHandleScale_sq (norm_nonneg _) hbmem, hbnorm]
    have hcancel :
        sphereHandleRadius ^ 2 * (sphereHandleRadius⁻¹ * ‖v‖) ^ 2 = ‖v‖ ^ 2 := by
      field_simp [sphereHandleRadius_ne_zero]
    rw [hcancel]
    nlinarith
  let z : Sphere 1 :=
    ⟨‖u‖⁻¹ • u, mem_sphere_zero_iff_norm.mpr hznorm⟩
  let b : EuclideanClosedBall 3 :=
    ⟨sphereHandleRadius⁻¹ • v, mem_closedBall_zero_iff.mpr hbmem⟩
  refine ⟨(z, b), ?_⟩
  apply Subtype.ext
  apply sphereHandleSplitEquiv.injective
  rw [sphereHandleSplitEquiv_oneHandleSphereMap]
  change
    (sphereHandleScale ‖sphereHandleRadius⁻¹ • v‖ • (‖u‖⁻¹ • u),
      sphereHandleRadius • (sphereHandleRadius⁻¹ • v)) = (u, v)
  rw [hscale, smul_smul, mul_inv_cancel₀ hu_pos.ne', one_smul,
    smul_smul, mul_inv_cancel₀ sphereHandleRadius_ne_zero, one_smul]

/-- A spherical point whose first block has norm at most `1 / √2` lies in the cap-face image. -/
theorem exists_sphereHandleCapMap_eq_of_first_norm_le
    (q : Sphere 4)
    (hu : ‖(sphereHandleSplitEquiv q.1).1‖ ≤ sphereHandleRadius) :
    ∃ x : CapPiece, sphereHandleCapMap x = q := by
  let u : SphereHandleFirst := (sphereHandleSplitEquiv q.1).1
  let v : SphereHandleSecond := (sphereHandleSplitEquiv q.1).2
  have hsum : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1 := sphereHandleSplitEquiv_sphere_norm_sq q
  have husq : ‖u‖ ^ 2 ≤ sphereHandleRadius ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le).2 hu
  have hv_sq_pos : 0 < ‖v‖ ^ 2 := by
    rw [sphereHandleRadius_sq] at husq
    nlinarith
  have hv_pos : 0 < ‖v‖ :=
    lt_of_le_of_ne (norm_nonneg _) (sq_pos_iff.mp hv_sq_pos).symm
  have hamem : ‖sphereHandleRadius⁻¹ • u‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr sphereHandleRadius_pos)]
    exact (inv_mul_le_one₀ sphereHandleRadius_pos).2 hu
  have hwnorm : ‖‖v‖⁻¹ • v‖ = 1 := by
    simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv_pos.ne']
  have hanorm : ‖sphereHandleRadius⁻¹ • u‖ = sphereHandleRadius⁻¹ * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr sphereHandleRadius_pos)]
  have hscale : sphereHandleScale ‖sphereHandleRadius⁻¹ • u‖ = ‖v‖ := by
    apply (sq_eq_sq₀ (sphereHandleScale_nonneg _) (norm_nonneg _)).mp
    rw [sphereHandleScale_sq (norm_nonneg _) hamem, hanorm]
    have hcancel :
        sphereHandleRadius ^ 2 * (sphereHandleRadius⁻¹ * ‖u‖) ^ 2 = ‖u‖ ^ 2 := by
      field_simp [sphereHandleRadius_ne_zero]
    rw [hcancel]
    nlinarith
  let a : EuclideanClosedBall 2 :=
    ⟨sphereHandleRadius⁻¹ • u, mem_closedBall_zero_iff.mpr hamem⟩
  let w : Sphere 2 :=
    ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.mpr hwnorm⟩
  refine ⟨(a, w), ?_⟩
  apply Subtype.ext
  apply sphereHandleSplitEquiv.injective
  rw [sphereHandleSplitEquiv_sphereHandleCapMap]
  change
    (sphereHandleRadius • (sphereHandleRadius⁻¹ • u),
      sphereHandleScale ‖sphereHandleRadius⁻¹ • u‖ • (‖v‖⁻¹ • v)) = (u, v)
  rw [smul_smul, mul_inv_cancel₀ sphereHandleRadius_ne_zero, one_smul,
    hscale, smul_smul, mul_inv_cancel₀ hv_pos.ne', one_smul]

/-- Every point of the literal four-sphere lies in at least one of the two direct face images. -/
theorem exists_oneHandleSphereMap_or_sphereHandleCapMap (q : Sphere 4) :
    (∃ x : OneHandlePiece, oneHandleSphereMap x = q) ∨
      ∃ y : CapPiece, sphereHandleCapMap y = q := by
  by_cases hv : ‖(sphereHandleSplitEquiv q.1).2‖ ≤ sphereHandleRadius
  · exact Or.inl (exists_oneHandleSphereMap_eq_of_second_norm_le q hv)
  · apply Or.inr
    apply exists_sphereHandleCapMap_eq_of_first_norm_le q
    have hsum := sphereHandleSplitEquiv_sphere_norm_sq q
    have hvlt : sphereHandleRadius < ‖(sphereHandleSplitEquiv q.1).2‖ :=
      lt_of_not_ge hv
    have hvsq : sphereHandleRadius ^ 2 < ‖(sphereHandleSplitEquiv q.1).2‖ ^ 2 :=
      (sq_lt_sq₀ sphereHandleRadius_pos.le (norm_nonneg _)).2 hvlt
    have husq : ‖(sphereHandleSplitEquiv q.1).1‖ ^ 2 < sphereHandleRadius ^ 2 := by
      rw [sphereHandleRadius_sq] at hvsq ⊢
      nlinarith
    exact ((sq_lt_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le).1 husq).le

/-- The ranges of the two face maps cover the literal four-sphere. -/
theorem range_oneHandleSphereMap_union_range_sphereHandleCapMap :
    range oneHandleSphereMap ∪ range sphereHandleCapMap = univ := by
  ext q
  constructor
  · exact fun _ ↦ mem_univ q
  · intro _
    rcases exists_oneHandleSphereMap_or_sphereHandleCapMap q with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨y, hy⟩

/-- The two compatible face maps descend to the capped topological pushout. -/
def cappedOneHandleToSphere : C(CappedOneHandle, Sphere 4) :=
  topologicalPushoutDesc oneHandleBoundaryInclusion capBoundaryInclusion
    oneHandleSphereMap sphereHandleCapMap oneHandleSphereMap_boundary_agreement

@[simp]
theorem cappedOneHandleToSphere_inl (x : OneHandlePiece) :
    cappedOneHandleToSphere (cappedOneHandleInl x) = oneHandleSphereMap x := by
  exact topologicalPushoutDesc_inl oneHandleBoundaryInclusion capBoundaryInclusion
    oneHandleSphereMap sphereHandleCapMap oneHandleSphereMap_boundary_agreement x

@[simp]
theorem cappedOneHandleToSphere_inr (x : CapPiece) :
    cappedOneHandleToSphere (cappedOneHandleInr x) = sphereHandleCapMap x := by
  exact topologicalPushoutDesc_inr oneHandleBoundaryInclusion capBoundaryInclusion
    oneHandleSphereMap sphereHandleCapMap oneHandleSphereMap_boundary_agreement x

/-- The descended spherical map is surjective. -/
theorem cappedOneHandleToSphere_surjective : Surjective cappedOneHandleToSphere := by
  intro q
  rcases exists_oneHandleSphereMap_or_sphereHandleCapMap q with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨cappedOneHandleInl x, by simpa using hx⟩
  · exact ⟨cappedOneHandleInr y, by simpa using hy⟩

/-- The descended spherical map is injective.  Same-face equality uses the two face
parameterizations' injectivity; cross-face equality uses the exact common-boundary theorem. -/
theorem cappedOneHandleToSphere_injective : Injective cappedOneHandleToSphere := by
  intro p q h
  rcases topologicalPushout_jointly_surjective oneHandleBoundaryInclusion
      capBoundaryInclusion p with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases topologicalPushout_jointly_surjective oneHandleBoundaryInclusion
      capBoundaryInclusion q with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · have hxy : oneHandleSphereMap x = oneHandleSphereMap y := by simpa using h
    rw [oneHandleSphereMap_injective hxy]
  · have hxy : oneHandleSphereMap x = sphereHandleCapMap y := by simpa using h
    obtain ⟨z, hz1, hz2⟩ := (oneHandleSphereMap_eq_sphereHandleCapMap_iff x y).mp hxy
    rw [← hz1, ← hz2]
    exact cappedOneHandle_condition z
  · have hxy : oneHandleSphereMap y = sphereHandleCapMap x := by simpa using h.symm
    obtain ⟨z, hz1, hz2⟩ := (oneHandleSphereMap_eq_sphereHandleCapMap_iff y x).mp hxy
    rw [← hz2, ← hz1]
    exact (cappedOneHandle_condition z).symm
  · have hxy : sphereHandleCapMap x = sphereHandleCapMap y := by simpa using h
    rw [sphereHandleCapMap_injective hxy]

theorem cappedOneHandleToSphere_bijective : Bijective cappedOneHandleToSphere :=
  ⟨cappedOneHandleToSphere_injective, cappedOneHandleToSphere_surjective⟩

/-- The capped one-handle adjunction space is homeomorphic to the literal project four-sphere.

Continuity is inherited from the pushout descent.  The inverse is continuous because the source
is compact, the target sphere is Hausdorff, and the descended map is bijective. -/
def directCappedOneHandleHomeomorphSphere : CappedOneHandle ≃ₜ Sphere 4 :=
  (isHomeomorph_iff_continuous_bijective.mpr
    ⟨cappedOneHandleToSphere.continuous, cappedOneHandleToSphere_bijective⟩).homeomorph
      cappedOneHandleToSphere

@[simp]
theorem directCappedOneHandleHomeomorphSphere_apply (x : CappedOneHandle) :
    directCappedOneHandleHomeomorphSphere x = cappedOneHandleToSphere x :=
  rfl

@[simp]
theorem directCappedOneHandleHomeomorphSphere_inl (x : OneHandlePiece) :
    directCappedOneHandleHomeomorphSphere (cappedOneHandleInl x) =
      oneHandleSphereMap x := by
  rw [directCappedOneHandleHomeomorphSphere_apply, cappedOneHandleToSphere_inl]

@[simp]
theorem directCappedOneHandleHomeomorphSphere_inr (x : CapPiece) :
    directCappedOneHandleHomeomorphSphere (cappedOneHandleInr x) = sphereHandleCapMap x := by
  rw [directCappedOneHandleHomeomorphSphere_apply, cappedOneHandleToSphere_inr]

end SplittingSpheres
