/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.LocalDiffeomorphismRecognition
public import SplittingSpheres.Handlebody.CoordinateExteriorOneHandleCover
public import SplittingSpheres.Handlebody.CoordinateExteriorOneHandleSmoothCover
public import TauCeti.Geometry.Lie.Exponential.Circle
public import TauCeti.Geometry.Lie.Exponential.LocalInverse

/-!
# The smooth trivialization of the one-handle power pullback

The degree-`m` power map on the project's literal unit circle is a local diffeomorphism for
`m ≠ 0`.  The proof identifies that circle smoothly with `Circle` and uses the intrinsic
Lie-group exponential, whose local inverse at zero gives the required local normal form for
`z ↦ z ^ m`.  Taking its product with the identity on the closed three-ball proves that the base
map displayed by the existing one-handle trivialization is a local diffeomorphism.

The one-handle pullback already carries the atlas pulled back along its covering projection.
Smoothness of the topological trivialization and its inverse can therefore be detected after
composition with the two local-diffeomorphic projections.  In particular, this construction does
not differentiate the selected residual-root branch and does not transport an atlas along the
trivialization.
-/

@[expose] public section

open Function Filter Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

private theorem isLocalDiffeomorphAt_circleExp_zero :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp 0 := by
  let e : ℝ ≃L[ℝ] LeftInvariantDerivation (𝓡 1) Circle :=
    circleLieAlgebraEquiv.symm.toContinuousLinearEquiv
  have he : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ)
      𝓘(ℝ, LeftInvariantDerivation (𝓡 1) Circle) ∞ e 0 :=
    e.toDiffeomorph.isLocalDiffeomorph 0
  have hexp : IsLocalDiffeomorphAt
      𝓘(ℝ, LeftInvariantDerivation (𝓡 1) Circle) (𝓡 1) ∞
      (lieExp (I := 𝓡 1) (G := Circle)) (e 0) := by
    simpa only [e, map_zero] using
      (isLocalDiffeomorphAt_lieExp_zero (I := 𝓡 1) (G := Circle))
  have hcomp := he.comp (𝓡 1) Circle hexp
  change IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞
    ((lieExp (I := 𝓡 1) (G := Circle)) ∘ circleLieAlgebraEquiv.symm) 0 at hcomp
  rw [show (lieExp (I := 𝓡 1) (G := Circle)) ∘ circleLieAlgebraEquiv.symm =
      Circle.exp by
    funext t
    exact lieExp_circle t] at hcomp
  exact hcomp

private theorem isLocalDiffeomorph_circleExp :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp := by
  intro t
  let dsub : ℝ ≃ₘ^∞⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ :=
    { toFun := fun s => s - t
      invFun := fun s => s + t
      left_inv := by intro s; ring
      right_inv := by intro s; ring
      contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  have hsub : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ dsub t :=
    dsub.isLocalDiffeomorph t
  have hexp : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞
      Circle.exp (dsub t) := by
    rw [show dsub t = 0 by change t - t = 0; ring]
    exact isLocalDiffeomorphAt_circleExp_zero
  have hfirst := hsub.comp (𝓡 1) Circle hexp
  let dmul : Circle ≃ₘ^∞⟮𝓡 1, 𝓡 1⟯ Circle :=
    Diffeomorph.smul (𝓡 1) (𝓡 1) ∞ (Circle.exp t)
  have hmul : IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ dmul
      (Circle.exp (dsub t)) := dmul.isLocalDiffeomorph _
  have hcomp := hfirst.comp (𝓡 1) Circle hmul
  change IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞
    (dmul ∘ Circle.exp ∘ dsub) t at hcomp
  rw [show dmul ∘ Circle.exp ∘ dsub = Circle.exp by
    funext s
    change Circle.exp t * Circle.exp (s - t) = Circle.exp s
    rw [← Circle.exp_add]
    congr 1
    ring] at hcomp
  exact hcomp

private noncomputable def euclideanLineEquivReal :
    EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans
    ((LinearEquiv.funUnique (Fin 1) ℝ ℝ).toContinuousLinearEquiv)

private def circleExpParam (v : EuclideanSpace ℝ (Fin 1)) : Circle :=
  Circle.exp (euclideanLineEquivReal v)

private theorem isLocalDiffeomorph_circleExpParam :
    IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞ circleExpParam := by
  have he : IsLocalDiffeomorph (𝓡 1) 𝓘(ℝ, ℝ) ∞ euclideanLineEquivReal :=
    euclideanLineEquivReal.toDiffeomorph.isLocalDiffeomorph
  intro v
  have h := (he v).comp (𝓡 1) Circle
    (isLocalDiffeomorph_circleExp (euclideanLineEquivReal v))
  change IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞
    (fun x => Circle.exp (euclideanLineEquivReal x)) v
  simpa only [Function.comp_def] using h

private noncomputable def realNatScaleDiffeomorph (m : ℕ) [NeZero m] :
    ℝ ≃ₘ^∞⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toFun t := (m : ℝ) * t
  invFun t := (m : ℝ)⁻¹ * t
  left_inv t := by
    change (m : ℝ)⁻¹ * ((m : ℝ) * t) = t
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
    simp [hm]
  right_inv t := by
    change (m : ℝ) * ((m : ℝ)⁻¹ * t) = t
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
    simp [hm]
  contMDiff_toFun := (contDiff_const.mul contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_const.mul contDiff_id).contMDiff

private theorem isLocalDiffeomorph_circlePow (m : ℕ) [NeZero m] :
    IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z ^ m) := by
  have he : IsLocalDiffeomorph (𝓡 1) 𝓘(ℝ, ℝ) ∞ euclideanLineEquivReal :=
    euclideanLineEquivReal.toDiffeomorph.isLocalDiffeomorph
  have hscale : IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (realNatScaleDiffeomorph m) :=
    (realNatScaleDiffeomorph m).isLocalDiffeomorph
  have hparamPow : IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞
      ((fun z : Circle => z ^ m) ∘ circleExpParam) := by
    intro v
    have hfirst := (he v).comp 𝓘(ℝ, ℝ) ℝ
      (hscale (euclideanLineEquivReal v))
    have h := hfirst.comp (𝓡 1) Circle
      (isLocalDiffeomorph_circleExp
        (realNatScaleDiffeomorph m (euclideanLineEquivReal v)))
    change IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞
      (Circle.exp ∘ realNatScaleDiffeomorph m ∘ euclideanLineEquivReal) v at h
    rw [show Circle.exp ∘ realNatScaleDiffeomorph m ∘ euclideanLineEquivReal =
        (fun z : Circle => z ^ m) ∘ circleExpParam by
      funext w
      change Circle.exp ((m : ℝ) * euclideanLineEquivReal w) =
        Circle.exp (euclideanLineEquivReal w) ^ m
      rw [← nsmul_eq_mul, Circle.exp_nsmul]] at h
    exact h
  apply isLocalDiffeomorph_of_localDiffeomorph_parametrized_cover
    (𝓡 1) (𝓡 1) (fun z : Circle => z ^ m) circleExpParam
    isLocalDiffeomorph_circleExpParam hparamPow
  intro z
  obtain ⟨t, ht⟩ := Circle.exp_surjective z
  refine ⟨euclideanLineEquivReal.symm t, ?_⟩
  simpa only [circleExpParam, ContinuousLinearEquiv.apply_symm_apply] using ht

private def unlinkNormalPlaneComplexLinearEquiv :
    UnlinkNormalPlane ≃ₗ[ℝ] ℂ where
  toFun := unlinkNormalPlaneToComplex
  invFun := complexToUnlinkNormalPlane
  left_inv v := by
    ext j
    fin_cases j <;>
      simp [complexToUnlinkNormalPlane, unlinkNormalPlaneToComplex,
        Complex.equivRealProdCLM_symm_apply]
  right_inv z := unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane z
  map_add' v w := by
    apply Complex.ext <;>
      simp [unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]
  map_smul' c v := by
    apply Complex.ext <;>
      simp [unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]

private def unlinkNormalPlaneComplexLinearIsometryEquiv :
    UnlinkNormalPlane ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv := unlinkNormalPlaneComplexLinearEquiv
  norm_map' := norm_unlinkNormalPlaneToComplex

private def unlinkUnitCircleDiffeomorph :
    Sphere 1 ≃ₘ^∞⟮𝓡 1, 𝓡 1⟯ Circle where
  toEquiv :=
    { toFun := fun u => ⟨unlinkNormalPlaneComplexLinearIsometryEquiv u.1, by
          change unlinkNormalPlaneComplexLinearIsometryEquiv u.1 ∈
            Metric.sphere (0 : ℂ) 1
          rw [mem_sphere_zero_iff_norm,
            unlinkNormalPlaneComplexLinearIsometryEquiv.norm_map]
          exact mem_sphere_zero_iff_norm.mp u.2⟩
      invFun := fun z => ⟨unlinkNormalPlaneComplexLinearIsometryEquiv.symm z.1, by
          rw [mem_sphere_zero_iff_norm,
            unlinkNormalPlaneComplexLinearIsometryEquiv.symm.norm_map]
          exact mem_sphere_zero_iff_norm.mp z.2⟩
      left_inv := by
        intro u
        apply Subtype.ext
        exact unlinkNormalPlaneComplexLinearIsometryEquiv.symm_apply_apply u.1
      right_inv := by
        intro z
        apply Subtype.ext
        exact unlinkNormalPlaneComplexLinearIsometryEquiv.apply_symm_apply z.1 }
  contMDiff_toFun := by
    let _ : Fact (Module.finrank ℝ UnlinkNormalPlane = 1 + 1) :=
      ⟨by simp [UnlinkNormalPlane]⟩
    let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
      Complex.finrank_real_complex_fact
    apply ContMDiff.codRestrict_sphere
    let e := unlinkNormalPlaneComplexLinearIsometryEquiv.toContinuousLinearEquiv
    exact e.contDiff.contMDiff.comp contMDiff_coe_sphere
  contMDiff_invFun := by
    let _ : Fact (Module.finrank ℝ UnlinkNormalPlane = 1 + 1) :=
      ⟨by simp [UnlinkNormalPlane]⟩
    let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
      Complex.finrank_real_complex_fact
    apply ContMDiff.codRestrict_sphere
    let e := unlinkNormalPlaneComplexLinearIsometryEquiv.symm.toContinuousLinearEquiv
    exact e.contDiff.contMDiff.comp contMDiff_coe_sphere

private theorem unlinkUnitCircleDiffeomorph_coe (u : Sphere 1) :
    ((unlinkUnitCircleDiffeomorph u : Circle) : ℂ) =
      unlinkUnitCircleComplex u := by
  rfl

/-- The positive-degree power map on the project's literal unit circle is a smooth local
diffeomorphism for its natural sphere atlas. -/
theorem isLocalDiffeomorph_unlinkUnitCirclePow (m : ℕ) [NeZero m] :
    IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞ (unlinkUnitCirclePow m) := by
  have hd : IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞
      unlinkUnitCircleDiffeomorph :=
    unlinkUnitCircleDiffeomorph.isLocalDiffeomorph
  have hdsymm : IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞
      unlinkUnitCircleDiffeomorph.symm :=
    unlinkUnitCircleDiffeomorph.symm.isLocalDiffeomorph
  intro u
  have hfirst := (hd u).comp (𝓡 1) Circle
    (isLocalDiffeomorph_circlePow m (unlinkUnitCircleDiffeomorph u))
  have h := hfirst.comp (𝓡 1) (Sphere 1)
    (hdsymm ((unlinkUnitCircleDiffeomorph u) ^ m))
  change IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞
    (unlinkUnitCircleDiffeomorph.symm ∘
      (fun z : Circle => z ^ m) ∘ unlinkUnitCircleDiffeomorph) u at h
  rw [show unlinkUnitCircleDiffeomorph.symm ∘
      (fun z : Circle => z ^ m) ∘ unlinkUnitCircleDiffeomorph =
      unlinkUnitCirclePow m by
    funext v
    apply Subtype.ext
    apply unlinkNormalPlaneComplexLinearEquiv.injective
    change unlinkNormalPlaneToComplex
        ((unlinkUnitCircleDiffeomorph.symm
          (unlinkUnitCircleDiffeomorph v ^ m) : Sphere 1) : UnlinkNormalPlane) =
      unlinkNormalPlaneToComplex ((unlinkUnitCirclePow m v : Sphere 1) : UnlinkNormalPlane)
    rw [show unlinkNormalPlaneToComplex
          ((unlinkUnitCircleDiffeomorph.symm
            (unlinkUnitCircleDiffeomorph v ^ m) : Sphere 1) : UnlinkNormalPlane) =
        ((unlinkUnitCircleDiffeomorph v ^ m : Circle) : ℂ) by
      calc
        unlinkNormalPlaneToComplex
            ((unlinkUnitCircleDiffeomorph.symm
              (unlinkUnitCircleDiffeomorph v ^ m) : Sphere 1) : UnlinkNormalPlane) =
            ((unlinkUnitCircleDiffeomorph
              (unlinkUnitCircleDiffeomorph.symm
                (unlinkUnitCircleDiffeomorph v ^ m)) : Circle) : ℂ) :=
          (unlinkUnitCircleDiffeomorph_coe _).symm
        _ = ((unlinkUnitCircleDiffeomorph v ^ m : Circle) : ℂ) :=
          congrArg (fun z : Circle => (z : ℂ))
            (unlinkUnitCircleDiffeomorph.apply_symm_apply
              (unlinkUnitCircleDiffeomorph v ^ m))]
    rw [Circle.coe_pow, unlinkUnitCircleDiffeomorph_coe]
    change unlinkUnitCircleComplex v ^ m =
      unlinkUnitCircleComplex (unlinkUnitCirclePow m v)
    exact (unlinkUnitCircleComplex_pow m v).symm] at h
  exact h

/-- The base map displayed by the one-handle power trivialization is a local diffeomorphism of
`S¹ × B³`. -/
theorem isLocalDiffeomorph_coordinateUnlinkExteriorOneHandleBasePowerMap
    (m : ℕ) [NeZero m] :
    IsLocalDiffeomorph oneHandlePieceModel oneHandlePieceModel ∞
      (coordinateUnlinkExteriorOneHandleBasePowerMap m) := by
  intro x
  have hlocal := isLocalDiffeomorph_unlinkUnitCirclePow m x.1
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp <|
    hlocal.contMDiffAt.continuousAt.preimage_mem_nhds <|
      hlocal.localInverse.open_source.mem_nhds hlocal.localInverse_mem_source
  let Ψ := hlocal.localInverse.symm
  let qCircle := Ψ.toOpenPartialHomeomorph.restrOpen V hVopen
  have hEq : EqOn (unlinkUnitCirclePow m) qCircle qCircle.source := by
    intro y hy
    change y ∈ Ψ.source ∩ V at hy
    have hyTarget : y ∈ hlocal.localInverse.target := hy.1
    have hfySource : unlinkUnitCirclePow m y ∈ hlocal.localInverse.source :=
      hVsub hy.2
    change unlinkUnitCirclePow m y = hlocal.localInverse.symm y
    calc
      unlinkUnitCirclePow m y =
          hlocal.localInverse.symm (hlocal.localInverse (unlinkUnitCirclePow m y)) :=
        (hlocal.localInverse.left_inv hfySource).symm
      _ = hlocal.localInverse.symm y :=
        congrArg hlocal.localInverse.symm
          (hlocal.localInverse_left_inv hyTarget)
  let phi : PartialDiffeomorph (𝓡 1) (𝓡 1) (Sphere 1) (Sphere 1) ∞ :=
    { toPartialEquiv :=
        { toFun := unlinkUnitCirclePow m
          invFun := qCircle.toPartialEquiv.invFun
          source := qCircle.source
          target := qCircle.target
          map_source' := by
            intro y hy
            rw [hEq hy]
            exact qCircle.map_source hy
          map_target' := by
            intro y hy
            exact qCircle.map_target hy
          left_inv' := by
            intro y hy
            rw [hEq hy]
            exact qCircle.left_inv hy
          right_inv' := by
            intro y hy
            exact (hEq (qCircle.toPartialEquiv.map_target hy)).trans
              (qCircle.toPartialEquiv.right_inv hy) }
      open_source := qCircle.open_source
      open_target := qCircle.open_target
      contMDiffOn_toFun := by
        apply (Ψ.contMDiffOn_toFun.mono ?_).congr hEq
        intro y hy
        change y ∈ Ψ.source ∩ V at hy
        exact hy.1
      contMDiffOn_invFun := by
        apply Ψ.contMDiffOn_invFun.mono
        intro y hy
        change y ∈ Ψ.target ∩ Ψ.symm ⁻¹' V at hy
        exact hy.1 }
  have hxphi : x.1 ∈ phi.source := by
    change x.1 ∈ Ψ.source ∩ V
    exact ⟨hlocal.localInverse_mem_target, hxV⟩
  let psi : PartialDiffeomorph (euclideanClosedBallModel 3)
      (euclideanClosedBallModel 3) (EuclideanClosedBall 3)
      (EuclideanClosedBall 3) ∞ :=
    { toPartialEquiv :=
        { toFun := id
          invFun := id
          source := univ
          target := univ
          map_source' := by simp
          map_target' := by simp
          left_inv' := by simp
          right_inv' := by simp }
      open_source := isOpen_univ
      open_target := isOpen_univ
      contMDiffOn_toFun := contMDiff_id.contMDiffOn
      contMDiffOn_invFun := contMDiff_id.contMDiffOn }
  let q := phi.toOpenPartialHomeomorph.prod psi.toOpenPartialHomeomorph
  let p : PartialDiffeomorph oneHandlePieceModel oneHandlePieceModel
      OneHandlePiece OneHandlePiece ∞ :=
    { toPartialEquiv := q.toPartialEquiv
      open_source := q.open_source
      open_target := q.open_target
      contMDiffOn_toFun := by
        exact phi.contMDiffOn_toFun.prodMap psi.contMDiffOn_toFun
      contMDiffOn_invFun := by
        exact phi.contMDiffOn_invFun.prodMap psi.contMDiffOn_invFun }
  have hp : (p : OneHandlePiece → OneHandlePiece) =
      coordinateUnlinkExteriorOneHandleBasePowerMap m := by
    funext y
    change (phi y.1, psi y.2) =
      coordinateUnlinkExteriorOneHandleBasePowerMap m y
    apply Prod.ext
    · rfl
    · rfl
  rw [← hp]
  apply p.isLocalDiffeomorphAt
  change x.1 ∈ phi.source ∧ x.2 ∈ psi.source
  exact ⟨hxphi, trivial⟩

/-- The existing topological trivialization of the one-handle power pullback is a diffeomorphism
for the atlas pulled back along the covering projection. -/
def coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    OneHandlePiece ≃ₘ^∞⟮oneHandlePieceModel, oneHandlePieceModel⟯
      CoordinateUnlinkExteriorOneHandlePowerPullback m := by
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  let _ : IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
  let H := coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m
  let p := coordinateUnlinkExteriorOneHandlePowerPullbackProj m
  let b := coordinateUnlinkExteriorOneHandleBasePowerMap m
  have hp : IsLocalDiffeomorph oneHandlePieceModel oneHandlePieceModel ∞ p :=
    isLocalDiffeomorph_coordinateUnlinkExteriorOneHandlePowerPullbackProj m
  have hpH : p ∘ H = b := by
    funext x
    exact coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_proj m x
  have hbHsymm : b ∘ H.symm = p := by
    funext z
    rw [← hpH]
    exact congrArg p (H.apply_symm_apply z)
  exact
    { toEquiv := H.toEquiv
      contMDiff_toFun := by
        apply contMDiff_of_comp_isLocalDiffeomorph
          oneHandlePieceModel oneHandlePieceModel oneHandlePieceModel hp H.continuous
        rw [hpH]
        exact
          (isLocalDiffeomorph_coordinateUnlinkExteriorOneHandleBasePowerMap m).contMDiff
      contMDiff_invFun := by
        apply contMDiff_of_comp_isLocalDiffeomorph
          oneHandlePieceModel oneHandlePieceModel oneHandlePieceModel
          (isLocalDiffeomorph_coordinateUnlinkExteriorOneHandleBasePowerMap m)
          H.symm.continuous
        rw [hbHsymm]
        exact hp.contMDiff }

/-- Forgetting smoothness recovers the original one-handle pullback homeomorphism exactly. -/
@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    (coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m).toHomeomorph =
      coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m :=
  rfl

/-- The smooth forward map is exactly the existing topological trivialization. -/
@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph_apply
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m x =
      coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m x :=
  rfl

/-- The smooth inverse is exactly the inverse of the existing topological trivialization. -/
@[simp]
theorem coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph_symm_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    (coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m).symm z =
      (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm z :=
  rfl

/-- The smooth trivialization lies over the displayed base power map. -/
theorem coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph_proj
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    coordinateUnlinkExteriorOneHandlePowerPullbackProj m
        (coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m x) =
      coordinateUnlinkExteriorOneHandleBasePowerMap m x :=
  rfl

end SplittingSpheres
