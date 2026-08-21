/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import SplittingSpheres.Statement
public import SplittingSpheres.Foundations.DiffeomorphOverLocalDiffeomorph
public import SplittingSpheres.Geometry.ClosedBallMaps

/-!
# A smooth one-sided collar of the Euclidean four-ball

The radial formula

`(s, t) ↦ (1 - t) • s`

identifies `S³ × [0, 1/2)` with the relative open shell of the literal closed Euclidean
four-ball on which `1/2 < ‖x‖`.  The half-open interval is implemented as an open submanifold of
`Set.Icc 0 (1/2)`, so its inherited model is the genuine half-space model `𝓡∂ 1`: zero is
its only model-boundary point and the omitted endpoint contributes no artificial boundary.

The target uses the existing convex-range model `euclideanClosedBallModel 4`.  Smoothness in
that model is proved through the literal ambient inclusion.  The inverse is the explicit polar
formula `x ↦ (‖x‖⁻¹ • x, 1 - ‖x‖)`, which is smooth on the displayed shell.  Thus this file
constructs an honest diffeomorphism onto that shell, and consequently an open smooth embedding
and a local diffeomorphism there.

No general boundary-flattening equivalence for the entire convex closed-ball model, and no
gluing or capping statement, is asserted.

The pinned immersion API only turns local diffeomorphisms into immersions when source and target
use the same literal `ModelWithCorners`.  Here the source model is
`(𝓡 3).prod (𝓡∂ 1)` while the target is the convex-range ball model, so this file does
not repackage the result as `Manifold.IsSmoothEmbedding`: doing so would additionally require an
explicit compatible local-normal-form equivalence between those two models.  The proved
`ContMDiff`, `IsOpenEmbedding`, `IsLocalDiffeomorph`, and diffeomorphism statements do not assume
such an equivalence.
-/

@[expose] public section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The strict endpoint inequality needed by the standard `Icc` manifold instance. -/
instance euclideanFourBallCollarIntervalFact :
    Fact ((0 : ℝ) < (1 / 2 : ℝ)) :=
  ⟨by norm_num⟩

/-- The half-open collar interval `[0, 1/2)`, installed as an open submanifold of
`Set.Icc 0 (1/2)`. -/
def euclideanFourBallCollarIntervalOpens :
    Opens (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :=
  ⟨{t | (t : ℝ) < 1 / 2},
    isOpen_lt continuous_subtype_val continuous_const⟩

/-- The honest half-open parameter space for the radial four-ball collar. -/
abbrev EuclideanFourBallCollarInterval :=
  euclideanFourBallCollarIntervalOpens

@[simp]
theorem euclideanFourBallCollarInterval_mem_iff
    (t : Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :
    t ∈ euclideanFourBallCollarIntervalOpens ↔ (t : ℝ) < 1 / 2 :=
  Iff.rfl

/-- The included endpoint of the half-open collar interval. -/
def euclideanFourBallCollarZero : EuclideanFourBallCollarInterval :=
  ⟨⟨0, by norm_num⟩, by norm_num [euclideanFourBallCollarIntervalOpens]⟩

@[simp]
theorem euclideanFourBallCollarZero_value :
    ((euclideanFourBallCollarZero.1 : Set.Icc (0 : ℝ) (1 / 2 : ℝ)) : ℝ) = 0 :=
  rfl

/-- The source model `ℝ³ × ℝ_{≥0}` for the one-sided radial collar. -/
abbrev euclideanFourBallCollarModel := (𝓡 3).prod (𝓡∂ 1)

/-- The source `S³ × [0,1/2)` of the one-sided radial collar. -/
abbrev EuclideanFourBallCollarDomain :=
  Sphere 3 × EuclideanFourBallCollarInterval

/-- The half-open collar interval has precisely its included zero endpoint as model boundary. -/
theorem euclideanFourBallCollarInterval_boundary :
    (𝓡∂ 1).boundary EuclideanFourBallCollarInterval =
      {euclideanFourBallCollarZero} := by
  rw [ModelWithCorners.boundary_open, boundary_Icc]
  ext t
  constructor
  · intro ht
    rcases ht with ht | ht
    · apply Subtype.ext
      apply Subtype.ext
      change (t.1 : ℝ) = 0
      simpa only [Set.Icc.coe_bot] using congrArg Subtype.val ht
    · have htop : (t.1 : ℝ) = 1 / 2 := by
        simpa using congrArg Subtype.val ht
      exact False.elim (not_lt_of_ge htop.ge t.2)
  · rintro rfl
    exact Or.inl (by rfl)

/-- The source boundary is exactly `S³ × {0}`. -/
theorem euclideanFourBallCollarModel_boundary :
    euclideanFourBallCollarModel.boundary EuclideanFourBallCollarDomain =
      (univ : Set (Sphere 3)) ×ˢ {euclideanFourBallCollarZero} := by
  rw [ModelWithCorners.boundary_of_boundaryless_left,
    euclideanFourBallCollarInterval_boundary]
  ext p
  rfl

/-- `S³ × [0,1/2)` is a smooth manifold with boundary to every regularity. -/
theorem isManifold_euclideanFourBallCollarDomain (n : ℕ∞ω) :
    IsManifold euclideanFourBallCollarModel n EuclideanFourBallCollarDomain :=
  inferInstance

private theorem euclideanFourBallCollar_scale_pos
    (t : EuclideanFourBallCollarInterval) :
    0 < 1 - (t.1.1 : ℝ) := by
  have ht : (t.1.1 : ℝ) < 1 / 2 := t.2
  linarith

private theorem euclideanFourBallCollar_scale_le_one
    (t : EuclideanFourBallCollarInterval) :
    1 - (t.1.1 : ℝ) ≤ 1 := by
  linarith [t.1.2.1]

/-- The radial one-sided collar of the literal Euclidean closed four-ball. -/
def euclideanFourBallSmoothCollar
    (p : EuclideanFourBallCollarDomain) : EuclideanFourBall :=
  ⟨(1 - (p.2.1.1 : ℝ)) • p.1.1, by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (euclideanFourBallCollar_scale_pos p.2),
      mem_sphere_zero_iff_norm.mp p.1.2, mul_one]
    exact euclideanFourBallCollar_scale_le_one p.2⟩

@[simp]
theorem euclideanFourBallSmoothCollar_coe
    (p : EuclideanFourBallCollarDomain) :
    (euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4)) =
      (1 - (p.2.1.1 : ℝ)) • p.1.1 :=
  rfl

/-- The collar parameter is exactly inward radial distance from the unit sphere. -/
@[simp]
theorem norm_euclideanFourBallSmoothCollar
    (p : EuclideanFourBallCollarDomain) :
    ‖(euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4))‖ =
      1 - (p.2.1.1 : ℝ) := by
  rw [euclideanFourBallSmoothCollar_coe, norm_smul, Real.norm_eq_abs,
    abs_of_pos (euclideanFourBallCollar_scale_pos p.2),
    mem_sphere_zero_iff_norm.mp p.1.2, mul_one]

/-- The zero slice is literally the unit-sphere inclusion into the closed four-ball. -/
@[simp]
theorem euclideanFourBallSmoothCollar_zero_coe (s : Sphere 3) :
    (euclideanFourBallSmoothCollar (s, euclideanFourBallCollarZero) :
      EuclideanSpace ℝ (Fin 4)) = s.1 := by
  simp

/-- The zero slice agrees exactly with the inverse of the canonical boundary homeomorphism. -/
theorem euclideanFourBallSmoothCollar_zero_eq_boundaryHomeomorph_symm
    (s : Sphere 3) :
    euclideanFourBallSmoothCollar (s, euclideanFourBallCollarZero) =
      (euclideanFourBallBoundaryHomeomorphSphereThree.symm s).1 := by
  apply Subtype.ext
  rw [euclideanFourBallSmoothCollar_zero_coe]
  exact (closedUnitBallBoundaryHomeomorph_symm_apply_val
    (EuclideanSpace ℝ (Fin 4)) s).symm

/-- The relative open shell covered by the radial collar. -/
def euclideanFourBallSmoothCollarImage : Opens EuclideanFourBall :=
  ⟨{x | (1 / 2 : ℝ) < ‖(x.1 : EuclideanSpace ℝ (Fin 4))‖},
    isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)⟩

/-- The open shell, viewed as its inherited smooth open submanifold. -/
abbrev EuclideanFourBallSmoothCollarImage :=
  euclideanFourBallSmoothCollarImage

private theorem euclideanFourBallSmoothCollar_mem_image
    (p : EuclideanFourBallCollarDomain) :
    euclideanFourBallSmoothCollar p ∈ euclideanFourBallSmoothCollarImage := by
  change (1 / 2 : ℝ) <
    ‖(euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4))‖
  rw [norm_euclideanFourBallSmoothCollar]
  have ht : (p.2.1.1 : ℝ) < 1 / 2 := p.2.2
  linarith

private def euclideanFourBallSmoothCollarForward
    (p : EuclideanFourBallCollarDomain) :
    EuclideanFourBallSmoothCollarImage :=
  ⟨euclideanFourBallSmoothCollar p,
    euclideanFourBallSmoothCollar_mem_image p⟩

private theorem euclideanFourBallSmoothCollarImage_norm_pos
    (x : EuclideanFourBallSmoothCollarImage) :
    0 < ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖ := by
  have hx : (1 / 2 : ℝ) <
      ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖ := x.2
  linarith

private def euclideanFourBallSmoothCollarInverseSphere
    (x : EuclideanFourBallSmoothCollarImage) : Sphere 3 :=
  ⟨‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖⁻¹ • x.1.1, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (euclideanFourBallSmoothCollarImage_norm_pos x),
      inv_mul_cancel₀
        (euclideanFourBallSmoothCollarImage_norm_pos x).ne']⟩

private def euclideanFourBallSmoothCollarInverseInterval
    (x : EuclideanFourBallSmoothCollarImage) :
    EuclideanFourBallCollarInterval :=
  ⟨⟨1 - ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖, by
      constructor
      · have hx := mem_closedBall_zero_iff.mp x.1.2
        linarith
      · have hx : (1 / 2 : ℝ) <
            ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖ := x.2
        linarith⟩,
    by
      change 1 - ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖ < 1 / 2
      have hx : (1 / 2 : ℝ) <
          ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖ := x.2
      linarith⟩

private def euclideanFourBallSmoothCollarInverse
    (x : EuclideanFourBallSmoothCollarImage) :
    EuclideanFourBallCollarDomain :=
  (euclideanFourBallSmoothCollarInverseSphere x,
    euclideanFourBallSmoothCollarInverseInterval x)

private theorem euclideanFourBallSmoothCollarInverse_forward
    (p : EuclideanFourBallCollarDomain) :
    euclideanFourBallSmoothCollarInverse
        (euclideanFourBallSmoothCollarForward p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    change (euclideanFourBallSmoothCollarInverseSphere
      (euclideanFourBallSmoothCollarForward p) :
        EuclideanSpace ℝ (Fin 4)) = p.1.1
    rw [euclideanFourBallSmoothCollarInverseSphere]
    change ‖(euclideanFourBallSmoothCollar p :
      EuclideanSpace ℝ (Fin 4))‖⁻¹ •
        (euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4)) = p.1.1
    rw [norm_euclideanFourBallSmoothCollar,
      euclideanFourBallSmoothCollar_coe]
    change (1 - (p.2.1.1 : ℝ))⁻¹ •
        ((1 - (p.2.1.1 : ℝ)) • p.1.1) = p.1.1
    rw [smul_smul, inv_mul_cancel₀
      (euclideanFourBallCollar_scale_pos p.2).ne']
    simp
  · apply Subtype.ext
    apply Subtype.ext
    change ((euclideanFourBallSmoothCollarInverseInterval
      (euclideanFourBallSmoothCollarForward p)).1.1 : ℝ) = p.2.1.1
    rw [euclideanFourBallSmoothCollarInverseInterval]
    change 1 - ‖(euclideanFourBallSmoothCollar p :
      EuclideanSpace ℝ (Fin 4))‖ = p.2.1.1
    rw [norm_euclideanFourBallSmoothCollar]
    ring

private theorem euclideanFourBallSmoothCollar_forward_inverse
    (x : EuclideanFourBallSmoothCollarImage) :
    euclideanFourBallSmoothCollarForward
        (euclideanFourBallSmoothCollarInverse x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  change (euclideanFourBallSmoothCollar
    (euclideanFourBallSmoothCollarInverse x) :
      EuclideanSpace ℝ (Fin 4)) = x.1.1
  rw [euclideanFourBallSmoothCollar_coe]
  change (1 - (1 - ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖)) •
      (‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖⁻¹ • x.1.1) = x.1.1
  have hsub : 1 - (1 - ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖) =
      ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖ := by ring
  rw [hsub]
  change ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖ •
      (‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖⁻¹ • x.1.1) = x.1.1
  rw [smul_smul, mul_inv_cancel₀
    (euclideanFourBallSmoothCollarImage_norm_pos x).ne']
  simp

private def euclideanFourBallSmoothCollarEquiv :
    EuclideanFourBallCollarDomain ≃ EuclideanFourBallSmoothCollarImage where
  toFun := euclideanFourBallSmoothCollarForward
  invFun := euclideanFourBallSmoothCollarInverse
  left_inv := euclideanFourBallSmoothCollarInverse_forward
  right_inv := euclideanFourBallSmoothCollar_forward_inverse

private theorem continuous_euclideanFourBallSmoothCollarForward :
    Continuous euclideanFourBallSmoothCollarForward := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact
    (continuous_const.sub
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd))).smul
      (continuous_subtype_val.comp continuous_fst)

private theorem continuous_euclideanFourBallSmoothCollarInverse :
    Continuous euclideanFourBallSmoothCollarInverse := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact
      ((continuous_norm.comp
        (continuous_subtype_val.comp continuous_subtype_val)).inv₀
          (fun x ↦ (euclideanFourBallSmoothCollarImage_norm_pos x).ne')).smul
        (continuous_subtype_val.comp continuous_subtype_val)
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_const.sub
      (continuous_norm.comp
        (continuous_subtype_val.comp continuous_subtype_val))

private def euclideanFourBallSmoothCollarHomeomorph :
    EuclideanFourBallCollarDomain ≃ₜ EuclideanFourBallSmoothCollarImage where
  toEquiv := euclideanFourBallSmoothCollarEquiv
  continuous_toFun := continuous_euclideanFourBallSmoothCollarForward
  continuous_invFun := continuous_euclideanFourBallSmoothCollarInverse

/-- The radial collar has exactly the relative open shell `1/2 < ‖x‖` as its range. -/
theorem range_euclideanFourBallSmoothCollar :
    range euclideanFourBallSmoothCollar =
      (euclideanFourBallSmoothCollarImage : Set EuclideanFourBall) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact euclideanFourBallSmoothCollar_mem_image p
  · intro hx
    let y : EuclideanFourBallSmoothCollarImage := ⟨x, hx⟩
    refine ⟨euclideanFourBallSmoothCollarInverse y, ?_⟩
    exact congrArg Subtype.val (euclideanFourBallSmoothCollar_forward_inverse y)

private theorem contMDiff_euclideanFourBallSmoothCollarForward :
    ContMDiff euclideanFourBallCollarModel euclideanFourBallModel ∞
      euclideanFourBallSmoothCollarForward := by
  rw [← ContMDiff.subtypeVal_comp_iff euclideanFourBallSmoothCollarImage]
  apply contMDiff_euclideanClosedBall_of_contMDiff_val
  let _ : Fact
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  have hs : ContMDiff euclideanFourBallCollarModel (𝓡 4) ∞
      (fun p : EuclideanFourBallCollarDomain ↦ p.1.1) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  have htIcc : ContMDiff euclideanFourBallCollarModel (𝓡∂ 1) ∞
      (fun p : EuclideanFourBallCollarDomain ↦ p.2.1) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have ht : ContMDiff euclideanFourBallCollarModel (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : EuclideanFourBallCollarDomain ↦ (p.2.1 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp htIcc
  exact ((contMDiff_const.sub ht).smul hs).congr fun _ ↦ rfl

/-- The literal radial collar map is smooth into the convex-range closed-ball model. -/
theorem contMDiff_euclideanFourBallSmoothCollar :
    ContMDiff euclideanFourBallCollarModel euclideanFourBallModel ∞
      euclideanFourBallSmoothCollar := by
  exact contMDiff_subtype_val.comp
    contMDiff_euclideanFourBallSmoothCollarForward

private theorem contMDiff_euclideanFourBallSmoothCollarImage_val :
    ContMDiff euclideanFourBallModel (𝓡 4) ∞
      (fun x : EuclideanFourBallSmoothCollarImage ↦
        (x.1.1 : EuclideanSpace ℝ (Fin 4))) := by
  exact contMDiff_closedUnitBall_inclusion
    (EuclideanSpace ℝ (Fin 4)) |>.comp contMDiff_subtype_val

private theorem contMDiff_euclideanFourBallSmoothCollarImage_norm :
    ContMDiff euclideanFourBallModel (modelWithCornersSelf ℝ ℝ) ∞
      (fun x : EuclideanFourBallSmoothCollarImage ↦
        ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖) := by
  intro x
  have hxne : (x.1.1 : EuclideanSpace ℝ (Fin 4)) ≠ 0 :=
    norm_ne_zero_iff.mp
      (euclideanFourBallSmoothCollarImage_norm_pos x).ne'
  have hnorm :=
    (contDiffAt_norm ℝ hxne).contMDiffAt.comp x
      contMDiff_euclideanFourBallSmoothCollarImage_val.contMDiffAt
  exact hnorm.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ rfl)

private theorem contMDiff_euclideanFourBallSmoothCollarInverseSphere :
    ContMDiff euclideanFourBallModel (𝓡 3) ∞
      euclideanFourBallSmoothCollarInverseSphere := by
  let _ : Fact
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  have hraw : ContMDiff euclideanFourBallModel (𝓡 4) ∞
      (fun x : EuclideanFourBallSmoothCollarImage ↦
        ‖(x.1.1 : EuclideanSpace ℝ (Fin 4))‖⁻¹ • x.1.1) :=
    (contMDiff_euclideanFourBallSmoothCollarImage_norm.inv₀
      (fun x ↦ (euclideanFourBallSmoothCollarImage_norm_pos x).ne')).smul
        contMDiff_euclideanFourBallSmoothCollarImage_val
  exact (hraw.codRestrict_sphere (n := 3)
    (fun x ↦ (euclideanFourBallSmoothCollarInverseSphere x).2)).congr
      fun _ ↦ rfl

private theorem contMDiff_euclideanFourBallSmoothCollarInverseInterval :
    ContMDiff euclideanFourBallModel (𝓡∂ 1) ∞
      euclideanFourBallSmoothCollarInverseInterval := by
  rw [← ContMDiff.subtypeVal_comp_iff euclideanFourBallCollarIntervalOpens]
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  constructor
  · exact
      (continuous_const.sub
        (continuous_norm.comp
          (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _
  · exact
      (contMDiff_const.sub
        contMDiff_euclideanFourBallSmoothCollarImage_norm).congr fun _ ↦ rfl

private theorem contMDiff_euclideanFourBallSmoothCollarInverse :
    ContMDiff euclideanFourBallModel euclideanFourBallCollarModel ∞
      euclideanFourBallSmoothCollarInverse :=
  contMDiff_euclideanFourBallSmoothCollarInverseSphere.prodMk
    contMDiff_euclideanFourBallSmoothCollarInverseInterval

/-- Existence of the radial diffeomorphism with its literal underlying collar map. -/
theorem exists_euclideanFourBallSmoothCollarDiffeomorph :
    ∃ e : EuclideanFourBallCollarDomain ≃ₘ^∞⟮
        euclideanFourBallCollarModel, euclideanFourBallModel⟯
        EuclideanFourBallSmoothCollarImage,
      ∀ p, (e p : EuclideanFourBall) = euclideanFourBallSmoothCollar p := by
  let e : EuclideanFourBallCollarDomain ≃ₘ^∞⟮
      euclideanFourBallCollarModel, euclideanFourBallModel⟯
      EuclideanFourBallSmoothCollarImage :=
    { toEquiv := euclideanFourBallSmoothCollarEquiv
      contMDiff_toFun := contMDiff_euclideanFourBallSmoothCollarForward
      contMDiff_invFun := contMDiff_euclideanFourBallSmoothCollarInverse }
  exact ⟨e, fun _ ↦ rfl⟩

/-- The radial formula is a diffeomorphism from `S³ × [0,1/2)` onto the relative open
shell `1/2 < ‖x‖` in the convex-range Euclidean closed-ball model. -/
def euclideanFourBallSmoothCollarDiffeomorph :
    EuclideanFourBallCollarDomain ≃ₘ^∞⟮
      euclideanFourBallCollarModel, euclideanFourBallModel⟯
      EuclideanFourBallSmoothCollarImage :=
  Classical.choose exists_euclideanFourBallSmoothCollarDiffeomorph

@[simp]
theorem euclideanFourBallSmoothCollarDiffeomorph_apply_coe
    (p : EuclideanFourBallCollarDomain) :
    (euclideanFourBallSmoothCollarDiffeomorph p : EuclideanFourBall) =
      euclideanFourBallSmoothCollar p :=
  Classical.choose_spec exists_euclideanFourBallSmoothCollarDiffeomorph p

/-- The literal radial collar is an open topological embedding into the closed four-ball. -/
theorem isOpenEmbedding_euclideanFourBallSmoothCollar :
    IsOpenEmbedding euclideanFourBallSmoothCollar := by
  have h := euclideanFourBallSmoothCollarImage.2.isOpenEmbedding_subtypeVal.comp
    euclideanFourBallSmoothCollarHomeomorph.isOpenEmbedding
  simpa [euclideanFourBallSmoothCollarHomeomorph,
    euclideanFourBallSmoothCollarEquiv,
    euclideanFourBallSmoothCollarForward, Function.comp_def] using h

/-- The image of the radial collar is relatively open in the closed four-ball. -/
theorem isOpen_range_euclideanFourBallSmoothCollar :
    IsOpen (range euclideanFourBallSmoothCollar) :=
  isOpenEmbedding_euclideanFourBallSmoothCollar.isOpen_range

/-- The radial collar is a local diffeomorphism from the standard one-sided source model into
the convex-range closed-ball model. -/
theorem isLocalDiffeomorph_euclideanFourBallSmoothCollar :
    IsLocalDiffeomorph euclideanFourBallCollarModel euclideanFourBallModel ∞
      euclideanFourBallSmoothCollar := by
  have hsub : IsLocalDiffeomorph euclideanFourBallModel euclideanFourBallModel ∞
      (Subtype.val : EuclideanFourBallSmoothCollarImage → EuclideanFourBall) :=
    isLocalDiffeomorph_opensSubtypeVal euclideanFourBallModel
      euclideanFourBallSmoothCollarImage
  let e : EuclideanFourBallCollarDomain ≃ₘ^∞⟮
      euclideanFourBallCollarModel, euclideanFourBallModel⟯
      EuclideanFourBallSmoothCollarImage :=
    { toEquiv := euclideanFourBallSmoothCollarEquiv
      contMDiff_toFun := contMDiff_euclideanFourBallSmoothCollarForward
      contMDiff_invFun := contMDiff_euclideanFourBallSmoothCollarInverse }
  intro p
  have h := (e.isLocalDiffeomorph p).comp
    euclideanFourBallModel EuclideanFourBall
      (hsub (e p))
  change IsLocalDiffeomorphAt euclideanFourBallCollarModel
    euclideanFourBallModel ∞ euclideanFourBallSmoothCollar p at h
  exact h

/-- The radial collar preserves the model boundary exactly. -/
theorem preimage_euclideanFourBallSmoothCollar_boundary :
    euclideanFourBallSmoothCollar ⁻¹'
        euclideanFourBallModel.boundary EuclideanFourBall =
      euclideanFourBallCollarModel.boundary EuclideanFourBallCollarDomain :=
  isLocalDiffeomorph_euclideanFourBallSmoothCollar.preimage_boundary (by simp)

/-- The zero slice has exactly the model boundary of the literal Euclidean four-ball as its
range. -/
theorem range_euclideanFourBallSmoothCollar_zero :
    range (fun s : Sphere 3 ↦
      euclideanFourBallSmoothCollar (s, euclideanFourBallCollarZero)) =
      euclideanFourBallModel.boundary EuclideanFourBall := by
  rw [closedUnitBallModel_boundary]
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    change (euclideanFourBallSmoothCollar
      (s, euclideanFourBallCollarZero) : EuclideanSpace ℝ (Fin 4)) ∈
        sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
    simp
  · intro hx
    change (x.1 : EuclideanSpace ℝ (Fin 4)) ∈
      sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 at hx
    rw [mem_sphere_zero_iff_norm] at hx
    let s : Sphere 3 := ⟨x.1, by simpa [mem_sphere_zero_iff_norm] using hx⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact euclideanFourBallSmoothCollar_zero_coe s

end SplittingSpheres

end
