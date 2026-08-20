/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import SplittingSpheres.Geometry.SpherePolarProduct

/-!
# Radial boundary collars for the coordinate unlink exterior

This file supplies the local geometric input for putting a smooth manifold-with-boundary
structure on a coordinate unlink exterior.  For radii `0 < r < R < 1/2`, the normal annulus

`{v | r ≤ ‖v - cᵢ‖ ∧ ‖v - cᵢ‖ < R}`

is identified with `S¹ × [r,R)`.  The half-open radial factor is implemented as an open
submanifold of `Set.Icc r R`; consequently it has the standard `𝒜∂ 1` boundary model at
`r`, but no artificial boundary at `R`.  We prove the exact homeomorphism, smoothness of its
forward map into the normal plane, and smooth polar inverse coordinates on the punctured normal
plane.  We then transport the collar forward through the already constructed smooth unlink-tube
coordinates.

No global `ChartedSpace` or `IsManifold` instance is asserted for the exterior here.  Such an
instance additionally requires constructing a common atlas and checking transitions between the
ambient `S⁴` charts and the collar charts.
-/

@[expose] public section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The half-open interval `[r,R)`, represented as an open submanifold of `[r,R]`.

The inherited model is `𝒜∂ 1`: the point `r` is a boundary point, while `R` is absent. -/
def unlinkExteriorCollarRadius (r R : ℝ) [Fact (r < R)] : Opens (Set.Icc r R) :=
  ⟨{t | (t : ℝ) < R}, isOpen_lt continuous_subtype_val continuous_const⟩

/-- The half-open radial factor as a manifold subtype. -/
abbrev UnlinkExteriorCollarRadius (r R : ℝ) [Fact (r < R)] :=
  unlinkExteriorCollarRadius r R

@[simp]
theorem unlinkExteriorCollarRadius_mem_iff {r R : ℝ} [Fact (r < R)]
    (t : Set.Icc r R) :
    t ∈ unlinkExteriorCollarRadius r R ↔ (t : ℝ) < R :=
  Iff.rfl

/-- The real value of a half-open collar radius. -/
def unlinkExteriorCollarRadiusValue {r R : ℝ} [Fact (r < R)]
    (t : UnlinkExteriorCollarRadius r R) : ℝ :=
  t.1.1

@[simp]
theorem unlinkExteriorCollarRadiusValue_coe {r R : ℝ} [Fact (r < R)]
    (t : UnlinkExteriorCollarRadius r R) :
    unlinkExteriorCollarRadiusValue t = (t.1 : ℝ) :=
  rfl

theorem unlinkExteriorCollarRadiusValue_lower {r R : ℝ} [Fact (r < R)]
    (t : UnlinkExteriorCollarRadius r R) :
    r ≤ unlinkExteriorCollarRadiusValue t :=
  t.1.2.1

theorem unlinkExteriorCollarRadiusValue_lt_upper {r R : ℝ} [Fact (r < R)]
    (t : UnlinkExteriorCollarRadius r R) :
    unlinkExteriorCollarRadiusValue t < R :=
  t.2

/-- The underlying real radius varies continuously. -/
@[continuity, fun_prop]
theorem continuous_unlinkExteriorCollarRadiusValue {r R : ℝ} [Fact (r < R)] :
    Continuous
      (unlinkExteriorCollarRadiusValue : UnlinkExteriorCollarRadius r R → ℝ) :=
  continuous_subtype_val.comp continuous_subtype_val

/-- The standard model for `S¹ × [r,R)`. -/
abbrev unlinkNormalExteriorCollarModel :=
  (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).prod
    (modelWithCornersEuclideanHalfSpace 1)

/-- The included left endpoint of the half-open collar radius. -/
def unlinkExteriorCollarInnerRadius (r R : ℝ) [Fact (r < R)] :
    UnlinkExteriorCollarRadius r R :=
  ⟨⟨r, le_rfl, (Fact.out : r < R).le⟩, by
    exact (Fact.out : r < R)⟩

@[simp]
theorem unlinkExteriorCollarInnerRadius_value (r R : ℝ) [Fact (r < R)] :
    unlinkExteriorCollarRadiusValue (unlinkExteriorCollarInnerRadius r R) = r :=
  rfl

/-- The half-open radius has exactly one model-boundary point: its included left endpoint. -/
theorem unlinkExteriorCollarRadius_boundary (r R : ℝ) [Fact (r < R)] :
    (modelWithCornersEuclideanHalfSpace 1).boundary
        (UnlinkExteriorCollarRadius r R) =
      {unlinkExteriorCollarInnerRadius r R} := by
  rw [ModelWithCorners.boundary_open, boundary_Icc]
  ext t
  constructor
  · intro ht
    rcases ht with (ht | ht)
    · apply Subtype.ext
      apply Subtype.ext
      change (t.1 : ℝ) = r
      simpa only [Set.Icc.coe_bot] using congrArg Subtype.val ht
    · have htop : (t.1 : ℝ) = R := by
        simpa using congrArg Subtype.val ht
      exact False.elim (not_lt_of_ge htop.ge t.2)
  · rintro rfl
    exact Or.inl (by rfl)

/-- `S¹ × [r,R)` is an honest smooth manifold with boundary. -/
theorem isManifold_unlinkNormalExteriorCollarDomain
    (r R : ℝ) [Fact (r < R)] (n : ℕ∞ω) :
    IsManifold unlinkNormalExteriorCollarModel n
      (Sphere 1 × UnlinkExteriorCollarRadius r R) :=
  inferInstance

/-- The model boundary of the normal collar domain is exactly `S¹ × {r}`. -/
theorem unlinkNormalExteriorCollarModel_boundary
    (r R : ℝ) [Fact (r < R)] :
    unlinkNormalExteriorCollarModel.boundary
        (Sphere 1 × UnlinkExteriorCollarRadius r R) =
      (univ : Set (Sphere 1)) ×ˢ {unlinkExteriorCollarInnerRadius r R} := by
  rw [ModelWithCorners.boundary_of_boundaryless_left,
    unlinkExteriorCollarRadius_boundary]
  ext p
  rfl

/-- A half-open normal annulus about the `i`th normal center. -/
def unlinkNormalExteriorCollarSet (i : Fin 2) (r R : ℝ) : Set UnlinkNormalPlane :=
  {v | r ≤ ‖v - standardUnlinkNormalCenter i‖ ∧
    ‖v - standardUnlinkNormalCenter i‖ < R}

/-- The normal annulus as a topological subtype.  No manifold instance is inferred from this
arbitrary locally closed subtype. -/
abbrev UnlinkNormalExteriorCollar (i : Fin 2) (r R : ℝ) :=
  unlinkNormalExteriorCollarSet i r R

@[simp]
theorem mem_unlinkNormalExteriorCollarSet_iff (i : Fin 2) (r R : ℝ)
    (v : UnlinkNormalPlane) :
    v ∈ unlinkNormalExteriorCollarSet i r R ↔
      r ≤ ‖v - standardUnlinkNormalCenter i‖ ∧
        ‖v - standardUnlinkNormalCenter i‖ < R :=
  Iff.rfl

/-- Radial coordinates map `S¹ × [r,R)` into the displayed normal annulus. -/
def unlinkNormalExteriorCollarForward (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r)
    (p : Sphere 1 × UnlinkExteriorCollarRadius r R) :
    UnlinkNormalExteriorCollar i r R := by
  let t := unlinkExteriorCollarRadiusValue p.2
  let v := standardUnlinkNormalCenter i + t • p.1.1
  have hu : ‖p.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
  have ht : 0 ≤ t := le_trans hr.le (unlinkExteriorCollarRadiusValue_lower p.2)
  have hnorm : ‖v - standardUnlinkNormalCenter i‖ = t := by
    simp [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hu]
  exact ⟨v, by
    rw [mem_unlinkNormalExteriorCollarSet_iff, hnorm]
    exact ⟨unlinkExteriorCollarRadiusValue_lower p.2,
      unlinkExteriorCollarRadiusValue_lt_upper p.2⟩⟩

@[simp]
theorem unlinkNormalExteriorCollarForward_coe (i : Fin 2) {r R : ℝ}
    [Fact (r < R)] (hr : 0 < r)
    (p : Sphere 1 × UnlinkExteriorCollarRadius r R) :
    (unlinkNormalExteriorCollarForward i hr p : UnlinkNormalPlane) =
      standardUnlinkNormalCenter i + unlinkExteriorCollarRadiusValue p.2 • p.1.1 :=
  rfl

@[simp]
theorem norm_unlinkNormalExteriorCollarForward_sub_center (i : Fin 2) {r R : ℝ}
    [Fact (r < R)] (hr : 0 < r)
    (p : Sphere 1 × UnlinkExteriorCollarRadius r R) :
    ‖(unlinkNormalExteriorCollarForward i hr p : UnlinkNormalPlane) -
        standardUnlinkNormalCenter i‖ = unlinkExteriorCollarRadiusValue p.2 := by
  have hu : ‖p.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
  have ht : 0 ≤ unlinkExteriorCollarRadiusValue p.2 :=
    le_trans hr.le (unlinkExteriorCollarRadiusValue_lower p.2)
  rw [unlinkNormalExteriorCollarForward_coe, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht, hu, mul_one]

/-- Polar coordinates on the normal annulus. -/
def unlinkNormalExteriorCollarInverse (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (v : UnlinkNormalExteriorCollar i r R) :
    Sphere 1 × UnlinkExteriorCollarRadius r R := by
  let d : UnlinkNormalPlane := v.1 - standardUnlinkNormalCenter i
  let t : ℝ := ‖d‖
  have htpos : 0 < t := lt_of_lt_of_le hr v.2.1
  have hu : ‖t⁻¹ • d‖ = 1 := by
    simp [t, norm_smul, htpos.ne']
  let u : Sphere 1 := ⟨t⁻¹ • d, mem_sphere_zero_iff_norm.mpr hu⟩
  let s : Set.Icc r R := ⟨t, v.2.1, v.2.2.le⟩
  exact (u, ⟨s, v.2.2⟩)

@[simp]
theorem unlinkNormalExteriorCollarInverse_fst_coe (i : Fin 2) {r R : ℝ}
    [Fact (r < R)] (hr : 0 < r) (v : UnlinkNormalExteriorCollar i r R) :
    ((unlinkNormalExteriorCollarInverse i hr v).1 : UnlinkNormalPlane) =
      ‖v.1 - standardUnlinkNormalCenter i‖⁻¹ •
        (v.1 - standardUnlinkNormalCenter i) :=
  rfl

@[simp]
theorem unlinkNormalExteriorCollarInverse_radius (i : Fin 2) {r R : ℝ}
    [Fact (r < R)] (hr : 0 < r) (v : UnlinkNormalExteriorCollar i r R) :
    unlinkExteriorCollarRadiusValue (unlinkNormalExteriorCollarInverse i hr v).2 =
      ‖v.1 - standardUnlinkNormalCenter i‖ :=
  rfl

theorem unlinkNormalExteriorCollarInverse_forward (i : Fin 2) {r R : ℝ}
    [Fact (r < R)] (hr : 0 < r)
    (p : Sphere 1 × UnlinkExteriorCollarRadius r R) :
    unlinkNormalExteriorCollarInverse i hr
        (unlinkNormalExteriorCollarForward i hr p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    rw [unlinkNormalExteriorCollarInverse_fst_coe,
      norm_unlinkNormalExteriorCollarForward_sub_center]
    have htpos : 0 < unlinkExteriorCollarRadiusValue p.2 :=
      lt_of_lt_of_le hr (unlinkExteriorCollarRadiusValue_lower p.2)
    rw [unlinkNormalExteriorCollarForward_coe, add_sub_cancel_left]
    exact inv_smul_smul₀ htpos.ne' p.1.1
  · apply Subtype.ext
    apply Subtype.ext
    exact norm_unlinkNormalExteriorCollarForward_sub_center i hr p

theorem unlinkNormalExteriorCollarForward_inverse (i : Fin 2) {r R : ℝ}
    [Fact (r < R)] (hr : 0 < r)
    (v : UnlinkNormalExteriorCollar i r R) :
    unlinkNormalExteriorCollarForward i hr
        (unlinkNormalExteriorCollarInverse i hr v) = v := by
  apply Subtype.ext
  rw [unlinkNormalExteriorCollarForward_coe,
    unlinkNormalExteriorCollarInverse_radius,
    unlinkNormalExteriorCollarInverse_fst_coe]
  have htpos : 0 < ‖v.1 - standardUnlinkNormalCenter i‖ :=
    lt_of_lt_of_le hr v.2.1
  rw [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul, add_sub_cancel]

/-- The radial identification of `S¹ × [r,R)` with the exact normal annulus. -/
def unlinkNormalExteriorCollarHomeomorph (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) :
    (Sphere 1 × UnlinkExteriorCollarRadius r R) ≃ₜ
      UnlinkNormalExteriorCollar i r R where
  toFun := unlinkNormalExteriorCollarForward i hr
  invFun := unlinkNormalExteriorCollarInverse i hr
  left_inv := unlinkNormalExteriorCollarInverse_forward i hr
  right_inv := unlinkNormalExteriorCollarForward_inverse i hr
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.add
      ((continuous_unlinkExteriorCollarRadiusValue.comp continuous_snd).smul
        (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    have hd : Continuous
        (fun v : UnlinkNormalExteriorCollar i r R ↦
          v.1 - standardUnlinkNormalCenter i) := by fun_prop
    have hn : Continuous
        (fun v : UnlinkNormalExteriorCollar i r R ↦
          ‖v.1 - standardUnlinkNormalCenter i‖) := continuous_norm.comp hd
    have hnne : ∀ v : UnlinkNormalExteriorCollar i r R,
        ‖v.1 - standardUnlinkNormalCenter i‖ ≠ 0 := fun v ↦
      (lt_of_lt_of_le hr v.2.1).ne'
    have hu : Continuous
        (fun v : UnlinkNormalExteriorCollar i r R ↦
          (⟨‖v.1 - standardUnlinkNormalCenter i‖⁻¹ •
              (v.1 - standardUnlinkNormalCenter i),
            (unlinkNormalExteriorCollarInverse i hr v).1.2⟩ : Sphere 1)) :=
      Continuous.subtype_mk ((hn.inv₀ hnne).smul hd) _
    have ht : Continuous
        (fun v : UnlinkNormalExteriorCollar i r R ↦
          (⟨⟨‖v.1 - standardUnlinkNormalCenter i‖, v.2.1, v.2.2.le⟩,
            v.2.2⟩ : UnlinkExteriorCollarRadius r R)) :=
      Continuous.subtype_mk (Continuous.subtype_mk hn _) _
    exact (hu.prodMk ht).congr fun _ ↦ rfl

@[simp]
theorem unlinkNormalExteriorCollarHomeomorph_apply (i : Fin 2) {r R : ℝ}
    [Fact (r < R)] (hr : 0 < r)
    (p : Sphere 1 × UnlinkExteriorCollarRadius r R) :
    unlinkNormalExteriorCollarHomeomorph i hr p =
      unlinkNormalExteriorCollarForward i hr p :=
  rfl

@[simp]
theorem unlinkNormalExteriorCollarHomeomorph_symm_apply (i : Fin 2) {r R : ℝ}
    [Fact (r < R)] (hr : 0 < r)
    (v : UnlinkNormalExteriorCollar i r R) :
    (unlinkNormalExteriorCollarHomeomorph i hr).symm v =
      unlinkNormalExteriorCollarInverse i hr v :=
  rfl

/-- The half-open collar radius has its honest inherited smooth inclusion into `ℝ`. -/
theorem contMDiff_unlinkExteriorCollarRadiusValue {r R : ℝ} [Fact (r < R)] :
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ ℝ) ∞
      (unlinkExteriorCollarRadiusValue : UnlinkExteriorCollarRadius r R → ℝ) := by
  exact (contMDiff_subtypeVal_Icc.comp contMDiff_subtype_val).congr fun _ ↦ rfl

/-- The radial collar map is smooth into the ambient normal plane. -/
theorem contMDiff_unlinkNormalExteriorCollarForward_ambient
    (i : Fin 2) {r R : ℝ} [Fact (r < R)] (hr : 0 < r) :
    ContMDiff unlinkNormalExteriorCollarModel
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
      (fun p : Sphere 1 × UnlinkExteriorCollarRadius r R ↦
        (unlinkNormalExteriorCollarForward i hr p : UnlinkNormalPlane)) := by
  letI : Fact (Module.finrank ℝ UnlinkNormalPlane = 1 + 1) := ⟨by simp⟩
  have ht : ContMDiff unlinkNormalExteriorCollarModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 1 × UnlinkExteriorCollarRadius r R ↦
        unlinkExteriorCollarRadiusValue p.2) :=
    contMDiff_unlinkExteriorCollarRadiusValue.comp contMDiff_snd
  have hu : ContMDiff unlinkNormalExteriorCollarModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      (fun p : Sphere 1 × UnlinkExteriorCollarRadius r R ↦
        (p.1 : UnlinkNormalPlane)) :=
    (contMDiff_coe_sphere (n := 1)).comp contMDiff_fst
  exact (contMDiff_const.add (ht.smul hu)).congr fun _ ↦ rfl

/-- The punctured normal plane about component `i`, bundled as an open manifold. -/
def unlinkPuncturedNormalPlane (i : Fin 2) : Opens UnlinkNormalPlane :=
  ⟨{standardUnlinkNormalCenter i}ᶜ, isOpen_compl_singleton⟩

/-- The punctured normal plane as an open manifold subtype. -/
abbrev UnlinkPuncturedNormalPlane (i : Fin 2) := unlinkPuncturedNormalPlane i

theorem unlinkPuncturedNormalPlane_coe_ne_center (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i) :
    v.1 ≠ standardUnlinkNormalCenter i := by
  have hv := v.2
  change v.1 ≠ standardUnlinkNormalCenter i at hv
  exact hv

/-- The radial coordinate on the punctured normal plane. -/
def unlinkNormalPolarRadius (i : Fin 2) (v : UnlinkPuncturedNormalPlane i) : ℝ :=
  ‖v.1 - standardUnlinkNormalCenter i‖

theorem unlinkNormalPolarRadius_pos (i : Fin 2) (v : UnlinkPuncturedNormalPlane i) :
    0 < unlinkNormalPolarRadius i v := by
  rw [unlinkNormalPolarRadius, norm_pos_iff]
  exact sub_ne_zero.mpr (unlinkPuncturedNormalPlane_coe_ne_center i v)

theorem norm_unlinkNormalPolarDirectionRaw (i : Fin 2)
    (v : UnlinkPuncturedNormalPlane i) :
    ‖‖v.1 - standardUnlinkNormalCenter i‖⁻¹ •
        (v.1 - standardUnlinkNormalCenter i)‖ = 1 := by
  have hd : v.1 - standardUnlinkNormalCenter i ≠ 0 :=
    sub_ne_zero.mpr (unlinkPuncturedNormalPlane_coe_ne_center i v)
  simp [norm_smul, hd]

/-- The angular coordinate on the punctured normal plane. -/
def unlinkNormalPolarDirection (i : Fin 2) (v : UnlinkPuncturedNormalPlane i) : Sphere 1 :=
  ⟨‖v.1 - standardUnlinkNormalCenter i‖⁻¹ •
      (v.1 - standardUnlinkNormalCenter i),
    mem_sphere_zero_iff_norm.mpr (norm_unlinkNormalPolarDirectionRaw i v)⟩

@[simp]
theorem unlinkNormalPolarDirection_coe (i : Fin 2) (v : UnlinkPuncturedNormalPlane i) :
    (unlinkNormalPolarDirection i v : UnlinkNormalPlane) =
      ‖v.1 - standardUnlinkNormalCenter i‖⁻¹ •
        (v.1 - standardUnlinkNormalCenter i) :=
  rfl

/-- Polar coordinates on the punctured normal plane, with an ordinary real radial coordinate. -/
def unlinkNormalPolarCoordinates (i : Fin 2) (v : UnlinkPuncturedNormalPlane i) :
    Sphere 1 × ℝ :=
  (unlinkNormalPolarDirection i v, unlinkNormalPolarRadius i v)

/-- The nonzero displacement from the normal center is smooth. -/
theorem contMDiff_unlinkNormalDisplacement (i : Fin 2) :
    ContMDiff (modelWithCornersSelf ℝ UnlinkNormalPlane)
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
      (fun v : UnlinkPuncturedNormalPlane i ↦
        v.1 - standardUnlinkNormalCenter i) := by
  exact contMDiff_subtype_val.sub contMDiff_const

/-- The radial coordinate is smooth away from the normal center. -/
theorem contMDiff_unlinkNormalPolarRadius (i : Fin 2) :
    ContMDiff (modelWithCornersSelf ℝ UnlinkNormalPlane)
      (modelWithCornersSelf ℝ ℝ) ∞
      (unlinkNormalPolarRadius i) := by
  intro v
  have hd : v.1 - standardUnlinkNormalCenter i ≠ 0 :=
    norm_ne_zero_iff.mp (unlinkNormalPolarRadius_pos i v).ne'
  have h := (contDiffAt_norm ℝ hd).contMDiffAt.comp v
    (contMDiff_unlinkNormalDisplacement i).contMDiffAt
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- The normalized angular coordinate is smooth away from the normal center. -/
theorem contMDiff_unlinkNormalPolarDirection (i : Fin 2) :
    ContMDiff (modelWithCornersSelf ℝ UnlinkNormalPlane)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
      (unlinkNormalPolarDirection i) := by
  letI : Fact (Module.finrank ℝ UnlinkNormalPlane = 1 + 1) := ⟨by simp⟩
  have hraw : ContMDiff (modelWithCornersSelf ℝ UnlinkNormalPlane)
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
      (fun v : UnlinkPuncturedNormalPlane i ↦
        (unlinkNormalPolarRadius i v)⁻¹ •
          (v.1 - standardUnlinkNormalCenter i)) :=
    ((contMDiff_unlinkNormalPolarRadius i).inv₀
      (fun v ↦ (unlinkNormalPolarRadius_pos i v).ne')).smul
        (contMDiff_unlinkNormalDisplacement i)
  have hcod := hraw.codRestrict_sphere (n := 1)
    (fun v ↦ by
      rw [mem_sphere_zero_iff_norm]
      simpa only [unlinkNormalPolarRadius] using
        norm_unlinkNormalPolarDirectionRaw i v)
  exact hcod.congr fun _ ↦ rfl

/-- Both ordinary polar inverse coordinates are jointly smooth on the punctured normal plane. -/
theorem contMDiff_unlinkNormalPolarCoordinates (i : Fin 2) :
    ContMDiff (modelWithCornersSelf ℝ UnlinkNormalPlane)
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).prod
        (modelWithCornersSelf ℝ ℝ)) ∞
      (unlinkNormalPolarCoordinates i) :=
  (contMDiff_unlinkNormalPolarDirection i).prodMk
    (contMDiff_unlinkNormalPolarRadius i)

/-! ## Transport to the coordinate tubes in `S⁴` -/

/-- The exact part of the coordinate exterior lying in the `R`-tube about component `i`. -/
def standardUnlinkExteriorCollarSet (i : Fin 2) (r R : ℝ) : Set (Sphere 4) :=
  coordinateUnlinkExterior r ∩ standardUnlinkOpenTube i R

/-- The exact exterior collar as a topological subtype. -/
abbrev StandardUnlinkExteriorCollar (i : Fin 2) (r R : ℝ) :=
  standardUnlinkExteriorCollarSet i r R

/-- The two displayed exterior collars are disjoint whenever the outer tubes are disjoint. -/
theorem disjoint_standardUnlinkExteriorCollarSet_zero_one
    (r : ℝ) {R : ℝ} (hRhalf : R < 1 / 2) :
    Disjoint (standardUnlinkExteriorCollarSet 0 r R)
      (standardUnlinkExteriorCollarSet 1 r R) :=
  (disjoint_standardUnlinkOpenTube_zero_one hRhalf).mono
    inter_subset_right inter_subset_right

/-- Membership in a small exterior collar is exactly the half-open radial inequality. -/
theorem mem_standardUnlinkExteriorCollarSet_iff
    (i : Fin 2) {r R : ℝ} (hrR : r ≤ R) (hRhalf : R < 1 / 2)
    (q : Sphere 4) :
    q ∈ standardUnlinkExteriorCollarSet i r R ↔
      r ≤ ‖standardUnlinkNormalProjection q - standardUnlinkNormalCenter i‖ ∧
        ‖standardUnlinkNormalProjection q - standardUnlinkNormalCenter i‖ < R := by
  have hdisj := disjoint_standardUnlinkOpenTube_zero_one hRhalf
  constructor
  · rintro ⟨hext, htube⟩
    have hext' : q ∉ standardUnlinkOpenTubes r := by
      simpa only [coordinateUnlinkExterior, Set.mem_compl_iff] using hext
    refine ⟨?_, ?_⟩
    · apply le_of_not_gt
      intro hlt
      have hi : q ∈ standardUnlinkOpenTube i r := by
        change standardUnlinkNormalProjection q ∈
          ball (standardUnlinkNormalCenter i) r
        simpa only [mem_ball, dist_eq_norm] using hlt
      apply hext'
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · change standardUnlinkNormalProjection q ∈
        ball (standardUnlinkNormalCenter i) R at htube
      simpa only [mem_ball, dist_eq_norm] using htube
  · intro hradial
    have htube : q ∈ standardUnlinkOpenTube i R := by
      change standardUnlinkNormalProjection q ∈
        ball (standardUnlinkNormalCenter i) R
      simpa only [mem_ball, dist_eq_norm] using hradial.2
    have hnotOwn : q ∉ standardUnlinkOpenTube i r := by
      intro hi
      apply (not_lt_of_ge hradial.1)
      change standardUnlinkNormalProjection q ∈
        ball (standardUnlinkNormalCenter i) r at hi
      simpa only [mem_ball, dist_eq_norm] using hi
    refine ⟨?_, htube⟩
    rw [coordinateUnlinkExterior, Set.mem_compl_iff]
    rintro (hzero | hone)
    · fin_cases i
      · exact hnotOwn hzero
      · exact Set.disjoint_left.mp hdisj
          (standardUnlinkOpenTube_mono 0 hrR hzero) htube
    · fin_cases i
      · exact Set.disjoint_left.mp hdisj htube
          (standardUnlinkOpenTube_mono 1 hrR hone)
      · exact hnotOwn hone

/-- The tube diffeomorphism preserves the displayed normal coordinate exactly. -/
@[simp]
theorem standardUnlinkNormalProjection_openTubeDiffeomorph
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (p : Sphere 2 × UnlinkNormalDisk i R) :
    standardUnlinkNormalProjection
        (standardUnlinkOpenTubeDiffeomorph i hRhalf p).1 = p.2.1 := by
  change standardUnlinkNormalProjection
      (spherePolarForward (spherePolarTubeDomainInclusion i hRhalf p)).1 = p.2.1
  rw [standardUnlinkNormalProjection_spherePolarForward]
  rfl

/-- The normal coordinate recovered by the inverse tube diffeomorphism is literal projection. -/
@[simp]
theorem standardUnlinkOpenTubeDiffeomorph_symm_snd_coe
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (q : StandardUnlinkOpenTubeSpace i R) :
    ((standardUnlinkOpenTubeDiffeomorph i hRhalf).symm q).2.1 =
      standardUnlinkNormalProjection q.1 := by
  have h := standardUnlinkNormalProjection_openTubeDiffeomorph i hRhalf
    ((standardUnlinkOpenTubeDiffeomorph i hRhalf).symm q)
  simpa only [Diffeomorph.apply_symm_apply] using h.symm

/-- Homeomorphism spelling of exact preservation of the normal coordinate. -/
@[simp]
theorem standardUnlinkNormalProjection_openTubeHomeomorph
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (p : Sphere 2 × UnlinkNormalDisk i R) :
    standardUnlinkNormalProjection
        (standardUnlinkOpenTubeHomeomorph i hRhalf p).1 = p.2.1 := by
  rw [← standardUnlinkOpenTubeDiffeomorph_apply]
  exact standardUnlinkNormalProjection_openTubeDiffeomorph i hRhalf p

/-- Homeomorphism spelling of the recovered normal coordinate. -/
@[simp]
theorem standardUnlinkOpenTubeHomeomorph_symm_snd_coe
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (q : StandardUnlinkOpenTubeSpace i R) :
    ((standardUnlinkOpenTubeHomeomorph i hRhalf).symm q).2.1 =
      standardUnlinkNormalProjection q.1 := by
  have h := standardUnlinkNormalProjection_openTubeHomeomorph i hRhalf
    ((standardUnlinkOpenTubeHomeomorph i hRhalf).symm q)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

/-- Source subset in tube-product coordinates corresponding to the exterior collar. -/
def standardUnlinkTubeExteriorCollarSourceSet (i : Fin 2) (r R : ℝ) :
    Set (Sphere 2 × UnlinkNormalDisk i R) :=
  {p | p.2.1 ∈ unlinkNormalExteriorCollarSet i r R}

/-- The same collar, temporarily regarded as a subset of the bundled open tube. -/
def standardUnlinkExteriorCollarInTubeSet (i : Fin 2) (r R : ℝ) :
    Set (StandardUnlinkOpenTubeSpace i R) :=
  {q | q.1 ∈ coordinateUnlinkExterior r}

/-- Flatten `S² ×` the normal annulus to the corresponding subset of the tube-product
domain. -/
def standardUnlinkTubeExteriorCollarDomainHomeomorph
    (i : Fin 2) (r R : ℝ) :
    (Sphere 2 × UnlinkNormalExteriorCollar i r R) ≃ₜ
      standardUnlinkTubeExteriorCollarSourceSet i r R where
  toFun p := ⟨(p.1, ⟨p.2.1, by
    change dist p.2.1 (standardUnlinkNormalCenter i) < R
    simpa only [dist_eq_norm] using p.2.2.2⟩), p.2.2⟩
  invFun p := (p.1.1, ⟨p.1.2.1, p.2⟩)
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The restricted tube homeomorphism has exactly the exterior-collar image. -/
theorem image_standardUnlinkOpenTubeHomeomorph_collarSource
    (i : Fin 2) {r R : ℝ} (hrR : r ≤ R) (hRhalf : R < 1 / 2) :
    standardUnlinkOpenTubeHomeomorph i hRhalf ''
        standardUnlinkTubeExteriorCollarSourceSet i r R =
      standardUnlinkExteriorCollarInTubeSet i r R := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change (standardUnlinkOpenTubeHomeomorph i hRhalf p).1 ∈
      coordinateUnlinkExterior r
    have hradial :
        r ≤ ‖standardUnlinkNormalProjection
            (standardUnlinkOpenTubeHomeomorph i hRhalf p).1 -
              standardUnlinkNormalCenter i‖ ∧
          ‖standardUnlinkNormalProjection
            (standardUnlinkOpenTubeHomeomorph i hRhalf p).1 -
              standardUnlinkNormalCenter i‖ < R := by
      change r ≤ ‖p.2.1 - standardUnlinkNormalCenter i‖ ∧
        ‖p.2.1 - standardUnlinkNormalCenter i‖ < R at hp
      simpa only [standardUnlinkNormalProjection_openTubeHomeomorph] using hp
    exact (mem_standardUnlinkExteriorCollarSet_iff i hrR hRhalf _).2 hradial |>.1
  · intro hq
    let p := (standardUnlinkOpenTubeHomeomorph i hRhalf).symm q
    refine ⟨p, ?_, Homeomorph.apply_symm_apply _ q⟩
    have hradial := (mem_standardUnlinkExteriorCollarSet_iff i hrR hRhalf q.1).1
      ⟨hq, q.2⟩
    change p.2.1 ∈ unlinkNormalExteriorCollarSet i r R
    change r ≤ ‖p.2.1 - standardUnlinkNormalCenter i‖ ∧
      ‖p.2.1 - standardUnlinkNormalCenter i‖ < R
    simpa only [p, standardUnlinkOpenTubeHomeomorph_symm_snd_coe] using hradial

/-- Restrict the tube homeomorphism to the exact collar source and target subsets. -/
def standardUnlinkOpenTubeCollarRestrictionHomeomorph
    (i : Fin 2) {r R : ℝ} (hrR : r ≤ R) (hRhalf : R < 1 / 2) :
    standardUnlinkTubeExteriorCollarSourceSet i r R ≃ₜ
      standardUnlinkExteriorCollarInTubeSet i r R :=
  (standardUnlinkOpenTubeHomeomorph i hRhalf).toPartialHomeomorph
    |>.homeomorphOfImageSubsetSource (by simp)
      (image_standardUnlinkOpenTubeHomeomorph_collarSource i hrR hRhalf)

/-- Remove the redundant open-tube subtype from the collar target. -/
def standardUnlinkExteriorCollarTargetHomeomorph (i : Fin 2) (r R : ℝ) :
    standardUnlinkExteriorCollarInTubeSet i r R ≃ₜ
      StandardUnlinkExteriorCollar i r R where
  toFun q := ⟨q.1.1, q.2, q.1.2⟩
  invFun q := ⟨⟨q.1, q.2.2⟩, q.2.1⟩
  left_inv q := rfl
  right_inv q := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The coordinate exterior as a topological subtype.  No manifold structure is asserted. -/
abbrev CoordinateUnlinkExteriorSubtype (r : ℝ) := coordinateUnlinkExterior r

/-- A collar is relatively open in the coordinate exterior. -/
def standardUnlinkExteriorCollarOpens (i : Fin 2) (r R : ℝ) :
    Opens (CoordinateUnlinkExteriorSubtype r) :=
  ⟨{q | q.1 ∈ standardUnlinkOpenTube i R},
    (isOpen_standardUnlinkOpenTube i R).preimage continuous_subtype_val⟩

/-- The exterior collar bundled as a relatively open subspace of the exterior. -/
abbrev StandardUnlinkExteriorCollarOpenSpace (i : Fin 2) (r R : ℝ) :=
  standardUnlinkExteriorCollarOpens i r R

/-- Identify the literal ambient intersection with the same collar bundled as an open subset of
the exterior. -/
def standardUnlinkExteriorCollarToOpenHomeomorph (i : Fin 2) (r R : ℝ) :
    StandardUnlinkExteriorCollar i r R ≃ₜ
      StandardUnlinkExteriorCollarOpenSpace i r R where
  toFun q := ⟨⟨q.1, q.2.1⟩, q.2.2⟩
  invFun q := ⟨q.1.1, q.1.2, q.2⟩
  left_inv q := rfl
  right_inv q := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The boundary model for an exterior collar, parenthesized to match
`S² × (S¹ × [r,R))`. -/
abbrev standardUnlinkExteriorCollarModel :=
  (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
    unlinkNormalExteriorCollarModel

/-- The full collar domain `S² × S¹ × [r,R)` is an honest smooth manifold with boundary. -/
theorem isManifold_standardUnlinkExteriorCollarDomain
    (r R : ℝ) [Fact (r < R)] (n : ℕ∞ω) :
    IsManifold standardUnlinkExteriorCollarModel n
      (Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R)) :=
  inferInstance

/-- Its model boundary is exactly `S² × S¹ × {r}`. -/
theorem standardUnlinkExteriorCollarModel_boundary
    (r R : ℝ) [Fact (r < R)] :
    standardUnlinkExteriorCollarModel.boundary
        (Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R)) =
      (univ : Set (Sphere 2)) ×ˢ
        ((univ : Set (Sphere 1)) ×ˢ {unlinkExteriorCollarInnerRadius r R}) := by
  rw [ModelWithCorners.boundary_of_boundaryless_left,
    unlinkNormalExteriorCollarModel_boundary]
  ext p
  rfl

/-- A normal radial collar point, bundled into the outer normal disk. -/
def unlinkNormalExteriorCollarInDisk
    (i : Fin 2) {r R : ℝ} [Fact (r < R)] (hr : 0 < r)
    (p : Sphere 1 × UnlinkExteriorCollarRadius r R) :
    UnlinkNormalDisk i R :=
  ⟨unlinkNormalExteriorCollarForward i hr p, by
    change (unlinkNormalExteriorCollarForward i hr p : UnlinkNormalPlane) ∈
      ball (standardUnlinkNormalCenter i) R
    rw [mem_ball, dist_eq_norm,
      norm_unlinkNormalExteriorCollarForward_sub_center]
    exact unlinkExteriorCollarRadiusValue_lt_upper p.2⟩

@[simp]
theorem unlinkNormalExteriorCollarInDisk_coe
    (i : Fin 2) {r R : ℝ} [Fact (r < R)] (hr : 0 < r)
    (p : Sphere 1 × UnlinkExteriorCollarRadius r R) :
    (unlinkNormalExteriorCollarInDisk i hr p : UnlinkNormalPlane) =
      unlinkNormalExteriorCollarForward i hr p :=
  rfl

/-- The exact topological collar of the `i`th boundary component in the coordinate exterior. -/
def standardUnlinkExteriorCollarHomeomorph
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2) :
    (Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R)) ≃ₜ
      StandardUnlinkExteriorCollar i r R :=
  ((Homeomorph.refl (Sphere 2)).prodCongr
      (unlinkNormalExteriorCollarHomeomorph i hr)).trans
    ((standardUnlinkTubeExteriorCollarDomainHomeomorph i r R).trans
      ((standardUnlinkOpenTubeCollarRestrictionHomeomorph i
          (Fact.out : r < R).le hRhalf).trans
        (standardUnlinkExteriorCollarTargetHomeomorph i r R)))

/-- The same collar with its target bundled as a relatively open subset of the exterior. -/
def standardUnlinkExteriorCollarOpenHomeomorph
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2) :
    (Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R)) ≃ₜ
      StandardUnlinkExteriorCollarOpenSpace i r R :=
  (standardUnlinkExteriorCollarHomeomorph i hr hRhalf).trans
    (standardUnlinkExteriorCollarToOpenHomeomorph i r R)

@[simp]
theorem standardUnlinkExteriorCollarOpenHomeomorph_coe
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2)
    (p : Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R)) :
    (standardUnlinkExteriorCollarOpenHomeomorph i hr hRhalf p).1.1 =
      (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p).1 :=
  rfl

/-- The collar homeomorphism is literally the existing tube map applied to the radial normal
coordinate, after forgetting subtype proofs. -/
@[simp]
theorem standardUnlinkExteriorCollarHomeomorph_coe
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2)
    (p : Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R)) :
    (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p : Sphere 4) =
      (standardUnlinkOpenTubeDiffeomorph i hRhalf
        (p.1, unlinkNormalExteriorCollarInDisk (r := r) (R := R) i hr p.2)).1 := by
  apply Subtype.ext
  rfl

/-- In collar coordinates the normal projection is exactly `cᵢ + t u`. -/
@[simp]
theorem standardUnlinkNormalProjection_exteriorCollarHomeomorph
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2)
    (p : Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R)) :
    standardUnlinkNormalProjection
        (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p).1 =
      standardUnlinkNormalCenter i +
        unlinkExteriorCollarRadiusValue p.2.2 • p.2.1.1 := by
  rw [standardUnlinkExteriorCollarHomeomorph_coe,
    standardUnlinkNormalProjection_openTubeDiffeomorph]
  rfl

/-- The topological collar has exactly the displayed collar subset as its ambient range. -/
theorem range_standardUnlinkExteriorCollarHomeomorph
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2) :
    Set.range (fun p ↦
      (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p : Sphere 4)) =
        standardUnlinkExteriorCollarSet i r R := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p).2
  · intro hq
    obtain ⟨p, hp⟩ := (standardUnlinkExteriorCollarHomeomorph i hr hRhalf).surjective
      ⟨q, hq⟩
    exact ⟨p, congrArg Subtype.val hp⟩

/-- The inner boundary stratum of the displayed collar. -/
def standardUnlinkExteriorCollarBoundarySet (i : Fin 2) (r R : ℝ) : Set (Sphere 4) :=
  standardUnlinkExteriorCollarSet i r R ∩
    {q | ‖standardUnlinkNormalProjection q - standardUnlinkNormalCenter i‖ = r}

/-- The two inner boundary strata are disjoint. -/
theorem disjoint_standardUnlinkExteriorCollarBoundarySet_zero_one
    (r : ℝ) {R : ℝ} (hRhalf : R < 1 / 2) :
    Disjoint (standardUnlinkExteriorCollarBoundarySet 0 r R)
      (standardUnlinkExteriorCollarBoundarySet 1 r R) :=
  (disjoint_standardUnlinkExteriorCollarSet_zero_one r hRhalf).mono
    inter_subset_left inter_subset_left

/-- Parametrization of the inner collar boundary by `S² × S¹`. -/
def standardUnlinkExteriorCollarBoundaryMap
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2) (p : Sphere 2 × Sphere 1) : Sphere 4 :=
  (standardUnlinkExteriorCollarHomeomorph i hr hRhalf
    (p.1, (p.2, unlinkExteriorCollarInnerRadius r R))).1

/-- The boundary parametrization has exactly the radial boundary stratum as its range. -/
theorem range_standardUnlinkExteriorCollarBoundaryMap
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2) :
    Set.range (standardUnlinkExteriorCollarBoundaryMap i hr hRhalf) =
      standardUnlinkExteriorCollarBoundarySet i r R := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨(standardUnlinkExteriorCollarHomeomorph i hr hRhalf
      (p.1, (p.2, unlinkExteriorCollarInnerRadius r R))).2, ?_⟩
    change ‖standardUnlinkNormalProjection
      (standardUnlinkExteriorCollarHomeomorph i hr hRhalf
        (p.1, (p.2, unlinkExteriorCollarInnerRadius r R))).1 -
          standardUnlinkNormalCenter i‖ = r
    rw [standardUnlinkNormalProjection_exteriorCollarHomeomorph,
      unlinkExteriorCollarInnerRadius_value]
    have hu : ‖p.2.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.2.2
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]
  · rintro ⟨hqcollar, hqradial⟩
    let z : StandardUnlinkExteriorCollar i r R := ⟨q, hqcollar⟩
    obtain ⟨p, hp⟩ :=
      (standardUnlinkExteriorCollarHomeomorph i hr hRhalf).surjective z
    have hvalue : unlinkExteriorCollarRadiusValue p.2.2 = r := by
      calc
        unlinkExteriorCollarRadiusValue p.2.2 =
            ‖(unlinkNormalExteriorCollarForward i hr p.2 : UnlinkNormalPlane) -
              standardUnlinkNormalCenter i‖ :=
          (norm_unlinkNormalExteriorCollarForward_sub_center i hr p.2).symm
        _ = ‖standardUnlinkNormalProjection
              (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p).1 -
                standardUnlinkNormalCenter i‖ := by
          rw [standardUnlinkNormalProjection_exteriorCollarHomeomorph]
          rfl
        _ = ‖standardUnlinkNormalProjection q - standardUnlinkNormalCenter i‖ := by
          rw [congrArg Subtype.val hp]
        _ = r := hqradial
    let pboundary : Sphere 2 × Sphere 1 := (p.1, p.2.1)
    refine ⟨pboundary, ?_⟩
    have hinput :
        (pboundary.1, (pboundary.2, unlinkExteriorCollarInnerRadius r R)) = p := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Subtype.ext
          apply Subtype.ext
          exact hvalue.symm
    rw [standardUnlinkExteriorCollarBoundaryMap, hinput]
    exact congrArg Subtype.val hp

/-- The radial normal coordinate, bundled into the outer disk, is smooth. -/
theorem contMDiff_unlinkNormalExteriorCollarInDisk
    (i : Fin 2) {r R : ℝ} [Fact (r < R)] (hr : 0 < r) :
    ContMDiff unlinkNormalExteriorCollarModel
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
      (unlinkNormalExteriorCollarInDisk (r := r) (R := R) i hr) := by
  apply (ContMDiff.subtypeVal_comp_iff (unlinkNormalDisk i R) _).mp
  exact (contMDiff_unlinkNormalExteriorCollarForward_ambient i hr).congr fun _ ↦ rfl

/-- The exterior collar map is genuinely smooth as a map into the ambient four-sphere. -/
theorem contMDiff_standardUnlinkExteriorCollarHomeomorph_ambient
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2) :
    ContMDiff standardUnlinkExteriorCollarModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R) ↦
        (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p : Sphere 4)) := by
  have hnormal : ContMDiff standardUnlinkExteriorCollarModel
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
      (fun p : Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R) ↦
        unlinkNormalExteriorCollarInDisk (r := r) (R := R) i hr p.2) :=
    (contMDiff_unlinkNormalExteriorCollarInDisk (r := r) (R := R) i hr).comp
      contMDiff_snd
  have hproduct : ContMDiff standardUnlinkExteriorCollarModel
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ UnlinkNormalPlane)) ∞
      (fun p : Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R) ↦
        (p.1, unlinkNormalExteriorCollarInDisk (r := r) (R := R) i hr p.2)) :=
    contMDiff_fst.prodMk hnormal
  have htube := (standardUnlinkOpenTubeDiffeomorph i hRhalf).contMDiff.comp hproduct
  have hambient := contMDiff_subtype_val.comp htube
  exact hambient.congr fun p ↦
    standardUnlinkExteriorCollarHomeomorph_coe i hr hRhalf p

/-- The inner boundary parametrization is smooth into the ambient four-sphere. -/
theorem contMDiff_standardUnlinkExteriorCollarBoundaryMap
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2) :
    ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (standardUnlinkExteriorCollarBoundaryMap i hr hRhalf) := by
  have hinclusion : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))))
      standardUnlinkExteriorCollarModel ∞
      (fun p : Sphere 2 × Sphere 1 ↦
        (p.1, (p.2, unlinkExteriorCollarInnerRadius r R))) :=
    contMDiff_fst.prodMk (contMDiff_snd.prodMk contMDiff_const)
  exact ((contMDiff_standardUnlinkExteriorCollarHomeomorph_ambient
    i hr hRhalf).comp hinclusion).congr fun _ ↦ rfl

/-! ## Smooth inverse coordinates on an ambient punctured tube -/

/-- Remove the center section from an open coordinate tube.  This remains an open submanifold of
`S⁴`, so its inverse polar coordinates can be checked against the ordinary interior model. -/
def standardUnlinkPuncturedTubeOpens (i : Fin 2) (R : ℝ) :
    Opens (StandardUnlinkOpenTubeSpace i R) := by
  refine ⟨{q | standardUnlinkNormalProjection q.1 ≠ standardUnlinkNormalCenter i}, ?_⟩
  change IsOpen ((fun q : StandardUnlinkOpenTubeSpace i R ↦
    standardUnlinkNormalProjection q.1) ⁻¹' {standardUnlinkNormalCenter i}ᶜ)
  exact isOpen_compl_singleton.preimage
    (continuous_standardUnlinkNormalProjection.comp continuous_subtype_val)

/-- The punctured tube as an open manifold. -/
abbrev StandardUnlinkPuncturedTube (i : Fin 2) (R : ℝ) :=
  standardUnlinkPuncturedTubeOpens i R

/-- Regard an exterior collar point as a point of the surrounding punctured open tube. -/
def standardUnlinkExteriorCollarToPuncturedTube
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2)
    (q : StandardUnlinkExteriorCollar i r R) :
    StandardUnlinkPuncturedTube i R := by
  refine ⟨⟨q.1, q.2.2⟩, ?_⟩
  have hradial :=
    (mem_standardUnlinkExteriorCollarSet_iff i (Fact.out : r < R).le hRhalf q.1).1 q.2
  have hnorm : 0 <
      ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter i‖ :=
    lt_of_lt_of_le hr hradial.1
  exact sub_ne_zero.mp (norm_ne_zero_iff.mp hnorm.ne')

@[simp]
theorem standardUnlinkExteriorCollarToPuncturedTube_coe
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2)
    (q : StandardUnlinkExteriorCollar i r R) :
    (standardUnlinkExteriorCollarToPuncturedTube i hr hRhalf q).1.1 = q.1 :=
  rfl

/-- The normal coordinate of a punctured tube point, bundled into the punctured normal plane. -/
def standardUnlinkPuncturedTubeNormalCoordinate
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (q : StandardUnlinkPuncturedTube i R) : UnlinkPuncturedNormalPlane i := by
  refine ⟨((standardUnlinkOpenTubeDiffeomorph i hRhalf).symm q.1).2.1, ?_⟩
  change ((standardUnlinkOpenTubeDiffeomorph i hRhalf).symm q.1).2.1 ≠
    standardUnlinkNormalCenter i
  rw [standardUnlinkOpenTubeDiffeomorph_symm_snd_coe]
  exact q.2

@[simp]
theorem standardUnlinkPuncturedTubeNormalCoordinate_coe
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (q : StandardUnlinkPuncturedTube i R) :
    (standardUnlinkPuncturedTubeNormalCoordinate i hRhalf q : UnlinkNormalPlane) =
      standardUnlinkNormalProjection q.1.1 := by
  change ((standardUnlinkOpenTubeDiffeomorph i hRhalf).symm q.1).2.1 =
    standardUnlinkNormalProjection q.1.1
  exact standardUnlinkOpenTubeDiffeomorph_symm_snd_coe i hRhalf q.1

/-- Full inverse product-polar coordinates on the punctured tube. -/
def standardUnlinkPuncturedTubePolarCoordinates
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (q : StandardUnlinkPuncturedTube i R) :
    Sphere 2 × (Sphere 1 × ℝ) :=
  (((standardUnlinkOpenTubeDiffeomorph i hRhalf).symm q.1).1,
    unlinkNormalPolarCoordinates i
      (standardUnlinkPuncturedTubeNormalCoordinate i hRhalf q))

@[simp]
theorem standardUnlinkPuncturedTubePolarCoordinates_fst
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (q : StandardUnlinkPuncturedTube i R) :
    (standardUnlinkPuncturedTubePolarCoordinates i hRhalf q).1 =
      ((standardUnlinkOpenTubeDiffeomorph i hRhalf).symm q.1).1 :=
  rfl

@[simp]
theorem standardUnlinkPuncturedTubePolarCoordinates_direction_coe
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (q : StandardUnlinkPuncturedTube i R) :
    ((standardUnlinkPuncturedTubePolarCoordinates i hRhalf q).2.1 :
        UnlinkNormalPlane) =
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖⁻¹ •
        (standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i) := by
  rw [standardUnlinkPuncturedTubePolarCoordinates, unlinkNormalPolarCoordinates,
    unlinkNormalPolarDirection_coe,
    standardUnlinkPuncturedTubeNormalCoordinate_coe]

@[simp]
theorem standardUnlinkPuncturedTubePolarCoordinates_radius
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2)
    (q : StandardUnlinkPuncturedTube i R) :
    (standardUnlinkPuncturedTubePolarCoordinates i hRhalf q).2.2 =
      ‖standardUnlinkNormalProjection q.1.1 - standardUnlinkNormalCenter i‖ := by
  rw [standardUnlinkPuncturedTubePolarCoordinates, unlinkNormalPolarCoordinates,
    unlinkNormalPolarRadius, standardUnlinkPuncturedTubeNormalCoordinate_coe]

/-- On the exact collar, the ambient punctured-tube inverse coordinates recover the original
`S²`, `S¹`, and real radius coordinates.  This is the literal transition identity needed by a
future global atlas construction. -/
theorem standardUnlinkPuncturedTubePolarCoordinates_exteriorCollar
    (i : Fin 2) {r R : ℝ} [Fact (r < R)]
    (hr : 0 < r) (hRhalf : R < 1 / 2)
    (p : Sphere 2 × (Sphere 1 × UnlinkExteriorCollarRadius r R)) :
    standardUnlinkPuncturedTubePolarCoordinates i hRhalf
        (standardUnlinkExteriorCollarToPuncturedTube i hr hRhalf
          (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p)) =
      (p.1, (p.2.1, unlinkExteriorCollarRadiusValue p.2.2)) := by
  apply Prod.ext
  · change ((standardUnlinkOpenTubeDiffeomorph i hRhalf).symm
      (standardUnlinkExteriorCollarToPuncturedTube i hr hRhalf
        (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p)).1).1 = p.1
    have htube :
        (standardUnlinkExteriorCollarToPuncturedTube i hr hRhalf
          (standardUnlinkExteriorCollarHomeomorph i hr hRhalf p)).1 =
        standardUnlinkOpenTubeDiffeomorph i hRhalf
          (p.1, unlinkNormalExteriorCollarInDisk (r := r) (R := R) i hr p.2) := by
      apply Subtype.ext
      exact standardUnlinkExteriorCollarHomeomorph_coe i hr hRhalf p
    rw [htube, Diffeomorph.symm_apply_apply]
  · apply Prod.ext
    · apply Subtype.ext
      rw [standardUnlinkPuncturedTubePolarCoordinates_direction_coe,
        standardUnlinkExteriorCollarToPuncturedTube_coe,
        standardUnlinkNormalProjection_exteriorCollarHomeomorph]
      have hinverse := congrArg
        (fun z : Sphere 1 × UnlinkExteriorCollarRadius r R ↦ (z.1 : UnlinkNormalPlane))
        (unlinkNormalExteriorCollarInverse_forward i hr p.2)
      simpa only [unlinkNormalExteriorCollarInverse_fst_coe,
        unlinkNormalExteriorCollarForward_coe] using hinverse
    · rw [standardUnlinkPuncturedTubePolarCoordinates_radius,
        standardUnlinkExteriorCollarToPuncturedTube_coe,
        standardUnlinkNormalProjection_exteriorCollarHomeomorph]
      exact norm_unlinkNormalExteriorCollarForward_sub_center i hr p.2

/-- The punctured tube normal coordinate is smooth. -/
theorem contMDiff_standardUnlinkPuncturedTubeNormalCoordinate
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ UnlinkNormalPlane) ∞
      (standardUnlinkPuncturedTubeNormalCoordinate i hRhalf) := by
  apply (ContMDiff.subtypeVal_comp_iff (unlinkPuncturedNormalPlane i) _).mp
  have htube : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun q : StandardUnlinkPuncturedTube i R ↦ q.1) :=
    contMDiff_subtype_val
  have hinv := (standardUnlinkOpenTubeDiffeomorph i hRhalf).symm.contMDiff.comp htube
  have hnormal := contMDiff_subtype_val.comp (contMDiff_snd.comp hinv)
  exact hnormal.congr fun q ↦ by
    exact (standardUnlinkPuncturedTubeNormalCoordinate_coe i hRhalf q).trans
      (standardUnlinkOpenTubeDiffeomorph_symm_snd_coe i hRhalf q.1).symm

/-- The complete inverse product-polar coordinates are smooth on the punctured open tube.  This
is the transition-map input needed to compare the collar charts with ambient `S⁴` charts. -/
theorem contMDiff_standardUnlinkPuncturedTubePolarCoordinates
    (i : Fin 2) {R : ℝ} (hRhalf : R < 1 / 2) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))).prod
        ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).prod
          (modelWithCornersSelf ℝ ℝ))) ∞
      (standardUnlinkPuncturedTubePolarCoordinates i hRhalf) := by
  have htube : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun q : StandardUnlinkPuncturedTube i R ↦ q.1) :=
    contMDiff_subtype_val
  have hinv := (standardUnlinkOpenTubeDiffeomorph i hRhalf).symm.contMDiff.comp htube
  have hbase := contMDiff_fst.comp hinv
  have hpolar := (contMDiff_unlinkNormalPolarCoordinates i).comp
    (contMDiff_standardUnlinkPuncturedTubeNormalCoordinate i hRhalf)
  exact (hbase.prodMk hpolar).congr fun _ ↦ rfl

/-! ## The concrete collar used for `coordinateUnlinkExterior (1/8)` -/

/-- The chosen inner and outer collar radii satisfy `1/8 < 1/4`. -/
instance fact_coordinateUnlinkExterior_eighth_lt_quarter :
    Fact ((1 / 8 : ℝ) < 1 / 4) :=
  ⟨by norm_num⟩

/-- The concrete half-open radius `[1/8,1/4)`. -/
abbrev CoordinateUnlinkExteriorEighthCollarRadius :=
  UnlinkExteriorCollarRadius (1 / 8 : ℝ) (1 / 4 : ℝ)

/-- An exact boundary collar for either component of `coordinateUnlinkExterior (1/8)`, using
outer radius `1/4`. -/
def standardUnlinkExteriorEighthCollarHomeomorph (i : Fin 2) :
    (Sphere 2 × (Sphere 1 × CoordinateUnlinkExteriorEighthCollarRadius)) ≃ₜ
      StandardUnlinkExteriorCollar i (1 / 8 : ℝ) (1 / 4 : ℝ) :=
  standardUnlinkExteriorCollarHomeomorph i (by norm_num) (by norm_num)

/-- The concrete collar has exactly the part of `coordinateUnlinkExterior (1/8)` inside the
`1/4`-tube as its range. -/
theorem range_standardUnlinkExteriorEighthCollarHomeomorph (i : Fin 2) :
    Set.range (fun p ↦
      (standardUnlinkExteriorEighthCollarHomeomorph i p : Sphere 4)) =
      coordinateUnlinkExterior (1 / 8 : ℝ) ∩
        standardUnlinkOpenTube i (1 / 4 : ℝ) :=
  range_standardUnlinkExteriorCollarHomeomorph i (by norm_num) (by norm_num)

/-- The concrete `1/8` exterior collar is smooth into the ambient four-sphere. -/
theorem contMDiff_standardUnlinkExteriorEighthCollarHomeomorph_ambient
    (i : Fin 2) :
    ContMDiff standardUnlinkExteriorCollarModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun p : Sphere 2 × (Sphere 1 × CoordinateUnlinkExteriorEighthCollarRadius) ↦
        (standardUnlinkExteriorEighthCollarHomeomorph i p : Sphere 4)) :=
  contMDiff_standardUnlinkExteriorCollarHomeomorph_ambient i (by norm_num) (by norm_num)

end SplittingSpheres
