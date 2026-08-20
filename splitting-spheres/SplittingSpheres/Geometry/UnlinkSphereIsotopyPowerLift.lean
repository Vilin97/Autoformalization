/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothIsotopyConcat
public import SplittingSpheres.Geometry.UnlinkEquatorPowerLift

/-!
# Lifting unlink-avoiding sphere isotopies to cyclic power covers

An isotopy beginning at the standard splitting sphere is specified only up to its time-zero
source parametrization.  This file first uses the canonical source diffeomorphism between smooth
embeddings with equal ranges to make that slice pointwise equal to `equatorSphereMap`.  An isotopy
which avoids the frozen standard unlink then gives a complement-valued homotopy, whose lift from
any explicit `equatorUnlinkPowerLift m a` is supplied by the covering homotopy property.

The resulting lift is continuous, jointly smooth for the explicit pulled-back atlas on
`StandardUnlinkPowerPullback m`, and a smooth embedding on every time slice.  Deck translation
adds labels, so labels and source points remain jointly injective and distinct labelled slice
ranges remain disjoint at every time.

No preservation of complement components, ambient isotopy extension, identification of a final
label, or smooth structure on a neck-star model is asserted here.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold unitInterval

namespace SplittingSpheres

variable {S : SmoothSphereEmbedding 3 4}

/-! ## Pointwise normalization at time zero -/

/-- The time-zero slice, bundled using the smooth-embedding hypothesis carried by the isotopy. -/
def standardUnlinkSphereIsotopyZeroSliceEmbedding
    (H : SmoothSphereIsotopy standardSplittingSphere S) :
    SmoothSphereEmbedding 3 4 :=
  TauCeti.SmoothEmbedding.ofIsSmoothEmbedding
    (fun x ↦ H.toFun (0, x)) (H.isSmoothEmbedding_slice 0)

/-- The standard sphere and the bundled time-zero slice have exactly the same range. -/
theorem range_standardUnlinkSphereIsotopyZeroSliceEmbedding
    (H : SmoothSphereIsotopy standardSplittingSphere S) :
    range standardSplittingSphere =
      range (standardUnlinkSphereIsotopyZeroSliceEmbedding H) := by
  simpa only [standardUnlinkSphereIsotopyZeroSliceEmbedding,
    TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_coe] using H.range_zero.symm

/-- The canonical source diffeomorphism which identifies the time-zero slice pointwise with the
standard equatorial sphere. -/
def standardUnlinkSphereIsotopyZeroSourceDiffeomorph
    (H : SmoothSphereIsotopy standardSplittingSphere S) :
    Sphere 3 ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ Sphere 3 :=
  TauCeti.SmoothEmbedding.sourceDiffeomorphOfRangeEq
    standardSplittingSphere
    (standardUnlinkSphereIsotopyZeroSliceEmbedding H)
    (range_standardUnlinkSphereIsotopyZeroSliceEmbedding H)

/-- Reparametrize every slice so that time zero has the standard pointwise parametrization. -/
def standardUnlinkNormalizedSphereIsotopy
    (H : SmoothSphereIsotopy standardSplittingSphere S) :
    SmoothSphereIsotopy standardSplittingSphere S :=
  H.precompDiffeomorph (standardUnlinkSphereIsotopyZeroSourceDiffeomorph H)

/-- The normalized isotopy is pointwise `equatorSphereMap` at time zero. -/
@[simp]
theorem standardUnlinkNormalizedSphereIsotopy_zero
    (H : SmoothSphereIsotopy standardSplittingSphere S) (x : Sphere 3) :
    (standardUnlinkNormalizedSphereIsotopy H).toFun (0, x) =
      equatorSphereMap x := by
  change H.toFun
      (0, standardUnlinkSphereIsotopyZeroSourceDiffeomorph H x) =
    equatorSphereMap x
  have h := TauCeti.SmoothEmbedding.sourceDiffeomorphOfRangeEq_apply
    standardSplittingSphere
    (standardUnlinkSphereIsotopyZeroSliceEmbedding H)
    (range_standardUnlinkSphereIsotopyZeroSliceEmbedding H) x
  calc
    H.toFun (0, standardUnlinkSphereIsotopyZeroSourceDiffeomorph H x) =
        standardUnlinkSphereIsotopyZeroSliceEmbedding H
          (standardUnlinkSphereIsotopyZeroSourceDiffeomorph H x) := by
            exact (TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_apply
              (fun y ↦ H.toFun (0, y)) (H.isSmoothEmbedding_slice 0) _).symm
    _ = standardSplittingSphere x := h
    _ = equatorSphereMap x := standardSplittingSphere_apply x

/-- Source normalization preserves pointwise avoidance of the frozen standard unlink. -/
theorem standardUnlinkNormalizedSphereIsotopy_avoids
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ∀ p, (standardUnlinkNormalizedSphereIsotopy H).toFun p ∉
      standardUnlinkCarrier :=
  H.precompDiffeomorph_avoids
    (standardUnlinkSphereIsotopyZeroSourceDiffeomorph H) havoid

/-! ## The normalized complement homotopy and its lift -/

/-- The normalized isotopy as a continuous homotopy in the strict standard-unlink complement. -/
def standardUnlinkNormalizedComplementHomotopy
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    C(I × Sphere 3, StandardUnlinkComplement) :=
  ⟨(standardUnlinkNormalizedSphereIsotopy H).toUnlinkComplement
      (standardUnlinkNormalizedSphereIsotopy_avoids H havoid),
    ((standardUnlinkNormalizedSphereIsotopy H).toUnlinkComplement
      (standardUnlinkNormalizedSphereIsotopy_avoids H havoid)).contMDiff.continuous⟩

/-- The complement homotopy has the explicit equator lift base map at time zero. -/
@[simp]
theorem standardUnlinkNormalizedComplementHomotopy_zero
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (x : Sphere 3) :
    standardUnlinkNormalizedComplementHomotopy H havoid (0, x) =
      equatorUnlinkComplementMap x := by
  apply Subtype.ext
  exact standardUnlinkNormalizedSphereIsotopy_zero H x

/-- Forgetting the complement proof recovers the normalized sphere isotopy pointwise. -/
@[simp]
theorem standardUnlinkNormalizedComplementHomotopy_coe
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier)
    (p : I × Sphere 3) :
    (standardUnlinkNormalizedComplementHomotopy H havoid p : Sphere 4) =
      (standardUnlinkNormalizedSphereIsotopy H).toFun p :=
  rfl

/-- Lift the normalized complement isotopy from the explicit equator lift with label `a`. -/
def standardUnlinkPowerIsotopyLift
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    C(I × Sphere 3, StandardUnlinkPowerPullback m) :=
  (isCoveringMap_standardUnlinkPowerPullbackProj m).liftHomotopy
    (standardUnlinkNormalizedComplementHomotopy H havoid)
    ⟨equatorUnlinkPowerLift m a, continuous_equatorUnlinkPowerLift m a⟩
    (fun x ↦ by
      rw [standardUnlinkNormalizedComplementHomotopy_zero]
      exact (equatorUnlinkPowerLift_proj m a x).symm)

/-- The lifted isotopy begins pointwise at the requested explicit labelled equator. -/
@[simp]
theorem standardUnlinkPowerIsotopyLift_zero
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (x : Sphere 3) :
    standardUnlinkPowerIsotopyLift m a H havoid (0, x) =
      equatorUnlinkPowerLift m a x :=
  isCoveringMap_standardUnlinkPowerPullbackProj m |>.liftHomotopy_zero
    (standardUnlinkNormalizedComplementHomotopy H havoid)
    ⟨equatorUnlinkPowerLift m a, continuous_equatorUnlinkPowerLift m a⟩
    (fun x ↦ by
      rw [standardUnlinkNormalizedComplementHomotopy_zero]
      exact (equatorUnlinkPowerLift_proj m a x).symm) x

/-- Projection of the lifted isotopy is exactly the normalized complement homotopy. -/
theorem standardUnlinkPowerIsotopyLift_proj
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier)
    (p : I × Sphere 3) :
    standardUnlinkPowerPullbackProj m
        (standardUnlinkPowerIsotopyLift m a H havoid p) =
      standardUnlinkNormalizedComplementHomotopy H havoid p :=
  congrFun (isCoveringMap_standardUnlinkPowerPullbackProj m |>.liftHomotopy_lifts
    (standardUnlinkNormalizedComplementHomotopy H havoid)
    ⟨equatorUnlinkPowerLift m a, continuous_equatorUnlinkPowerLift m a⟩
    (fun x ↦ by
      rw [standardUnlinkNormalizedComplementHomotopy_zero]
      exact (equatorUnlinkPowerLift_proj m a x).symm)) p

/-- Projection followed by inclusion in `Sphere 4` is the normalized sphere isotopy itself. -/
theorem standardUnlinkPowerIsotopyLift_proj_coe
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier)
    (p : I × Sphere 3) :
    (standardUnlinkPowerPullbackProj m
        (standardUnlinkPowerIsotopyLift m a H havoid p) : Sphere 4) =
      (standardUnlinkNormalizedSphereIsotopy H).toFun p := by
  rw [standardUnlinkPowerIsotopyLift_proj,
    standardUnlinkNormalizedComplementHomotopy_coe]

/-- Continuity of the jointly defined lifted isotopy. -/
theorem continuous_standardUnlinkPowerIsotopyLift
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    Continuous (standardUnlinkPowerIsotopyLift m a H havoid) :=
  (standardUnlinkPowerIsotopyLift m a H havoid).continuous

/-! ## Smoothness and embedded slices -/

/-- The lifted isotopy is jointly smooth for the explicit atlas pulled back along the smooth
covering projection. -/
theorem contMDiff_standardUnlinkPowerIsotopyLift
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 4) ∞
      (standardUnlinkPowerIsotopyLift m a H havoid) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply contMDiff_of_comp_isLocalDiffeomorph
    ((𝓡∂ 1).prod (𝓡 3)) (𝓡 4) (𝓡 4)
    (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
    (standardUnlinkPowerIsotopyLift m a H havoid).continuous
  exact ((standardUnlinkNormalizedSphereIsotopy H).toUnlinkComplement
    (standardUnlinkNormalizedSphereIsotopy_avoids H havoid)).contMDiff.congr
      fun p ↦ by
        simpa [Function.comp_apply, standardUnlinkNormalizedComplementHomotopy] using
          standardUnlinkPowerIsotopyLift_proj m a H havoid p

private theorem isSmoothEmbedding_standardUnlinkNormalizedComplementHomotopy_slice
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (t : I) :
    Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 4) ∞
      (fun x ↦ standardUnlinkNormalizedComplementHomotopy H havoid (t, x)) := by
  let f := fun x ↦ standardUnlinkNormalizedComplementHomotopy H havoid (t, x)
  have hf : ContMDiff (𝓡 3) (𝓡 4) ∞ f :=
    ((standardUnlinkNormalizedSphereIsotopy H).toUnlinkComplement
      (standardUnlinkNormalizedSphereIsotopy_avoids H havoid)).contMDiff.comp
        (contMDiff_const.prodMk contMDiff_id)
  apply Manifold.IsSmoothEmbedding.reflect_isLocalDiffeomorph
    isLocalDiffeomorph_standardUnlinkComplement_subtypeVal hf.continuous
  simpa [f, standardUnlinkNormalizedComplementHomotopy, Function.comp_def] using
    (standardUnlinkNormalizedSphereIsotopy H).isSmoothEmbedding_slice t

/-- Every fixed-time slice of the lifted isotopy is a smooth embedding. -/
theorem isSmoothEmbedding_standardUnlinkPowerIsotopyLift_slice
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (t : I) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 4) ∞
      (fun x ↦ standardUnlinkPowerIsotopyLift m a H havoid (t, x)) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let f := fun x ↦ standardUnlinkPowerIsotopyLift m a H havoid (t, x)
  have hf : ContMDiff (𝓡 3) (𝓡 4) ∞ f :=
    (contMDiff_standardUnlinkPowerIsotopyLift m a H havoid).comp
      (contMDiff_const.prodMk contMDiff_id)
  apply Manifold.IsSmoothEmbedding.reflect_isLocalDiffeomorph
    (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
    hf.continuous
  convert isSmoothEmbedding_standardUnlinkNormalizedComplementHomotopy_slice
    H havoid t using 1
  funext x
  exact standardUnlinkPowerIsotopyLift_proj m a H havoid (t, x)

/-- A fixed-time lifted slice, bundled as a smooth embedding in the pulled-back atlas. -/
def standardUnlinkPowerIsotopyLiftSliceEmbedding
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (t : I) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    TauCeti.SmoothEmbedding (𝓡 3) (𝓡 4) ∞
      (Sphere 3) (StandardUnlinkPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact TauCeti.SmoothEmbedding.ofIsSmoothEmbedding
    (fun x ↦ standardUnlinkPowerIsotopyLift m a H havoid (t, x))
    (isSmoothEmbedding_standardUnlinkPowerIsotopyLift_slice m a H havoid t)

/-- The bundled slice has the expected underlying lifted map. -/
@[simp]
theorem standardUnlinkPowerIsotopyLiftSliceEmbedding_apply
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier)
    (t : I) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerIsotopyLiftSliceEmbedding m a H havoid t x =
      standardUnlinkPowerIsotopyLift m a H havoid (t, x) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  simp [standardUnlinkPowerIsotopyLiftSliceEmbedding]

/-! ## Deck covariance and disjoint labelled slices -/

private theorem standardUnlinkPowerDeck_equatorUnlinkPowerLift_add
    (m : ℕ) [NeZero m] (b a : ZMod m) (x : Sphere 3) :
    standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd b)
        (equatorUnlinkPowerLift m a x) =
      equatorUnlinkPowerLift m (b + a) x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change
      (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd b)).1 : ℂˣ) : ℂ) *
          ((((standardRootsOfUnityZModMulEquiv m
            (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
            equatorUnlinkPowerRoot m x) =
        (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd (b + a))).1 : ℂˣ) : ℂ) *
          equatorUnlinkPowerRoot m x
    rw [← mul_assoc]
    congr 1
    simpa using congrArg (fun u : rootsOfUnity m ℂ ↦ ((u.1 : ℂˣ) : ℂ))
      ((standardRootsOfUnityZModMulEquiv m).map_mul
        (Multiplicative.ofAdd b) (Multiplicative.ofAdd a)).symm

/-- Apply deck label `b` pointwise to the lifted isotopy with initial label `a`. -/
def standardUnlinkPowerIsotopyLiftDeckTranslate
    (m : ℕ) [NeZero m] (b a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    C(I × Sphere 3, StandardUnlinkPowerPullback m) where
  toFun p := standardUnlinkPowerDeckHomeomorph m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b))
    (standardUnlinkPowerIsotopyLift m a H havoid p)
  continuous_toFun :=
    (standardUnlinkPowerDeckHomeomorph m
      (standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd b))).continuous.comp
      (standardUnlinkPowerIsotopyLift m a H havoid).continuous

/-- Deck translation by `b` changes the initial lift label from `a` to `b + a`. -/
theorem standardUnlinkPowerIsotopyLiftDeckTranslate_eq
    (m : ℕ) [NeZero m] (b a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    standardUnlinkPowerIsotopyLiftDeckTranslate m b a H havoid =
      standardUnlinkPowerIsotopyLift m (b + a) H havoid := by
  apply (isCoveringMap_standardUnlinkPowerPullbackProj m).eq_liftHomotopy_iff'
    (H := standardUnlinkNormalizedComplementHomotopy H havoid)
    (f := ⟨equatorUnlinkPowerLift m (b + a),
      continuous_equatorUnlinkPowerLift m (b + a)⟩)
    (fun x ↦ by
      rw [standardUnlinkNormalizedComplementHomotopy_zero]
      exact (equatorUnlinkPowerLift_proj m (b + a) x).symm)
    (standardUnlinkPowerIsotopyLiftDeckTranslate m b a H havoid) |>.mpr
  constructor
  · funext p
    change standardUnlinkPowerPullbackProj m
        (standardUnlinkPowerDeckHomeomorph m _
          (standardUnlinkPowerIsotopyLift m a H havoid p)) = _
    rw [standardUnlinkPowerPullbackProj_deck,
      standardUnlinkPowerIsotopyLift_proj]
  · intro x
    change standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd b)
        (standardUnlinkPowerIsotopyLift m a H havoid (0, x)) =
      equatorUnlinkPowerLift m (b + a) x
    rw [standardUnlinkPowerIsotopyLift_zero]
    exact standardUnlinkPowerDeck_equatorUnlinkPowerLift_add m b a x

/-- Pointwise form of deck covariance for the lifted isotopy. -/
theorem standardUnlinkPowerIsotopyLift_deck_add
    (m : ℕ) [NeZero m] (b a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier)
    (p : I × Sphere 3) :
    standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd b)
        (standardUnlinkPowerIsotopyLift m a H havoid p) =
      standardUnlinkPowerIsotopyLift m (b + a) H havoid p := by
  change standardUnlinkPowerIsotopyLiftDeckTranslate m b a H havoid p = _
  exact congrArg
    (fun F : C(I × Sphere 3, StandardUnlinkPowerPullback m) ↦ F p)
    (standardUnlinkPowerIsotopyLiftDeckTranslate_eq m b a H havoid)

/-- At every time, a lifted point determines both its deck label and its sphere source point. -/
theorem injective_standardUnlinkPowerIsotopyLift_family
    (m : ℕ) [NeZero m]
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (t : I) :
    Injective (fun p : ZMod m × Sphere 3 ↦
      standardUnlinkPowerIsotopyLift m p.1 H havoid (t, p.2)) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ hab
  have hbase := congrArg (standardUnlinkPowerPullbackProj m) hab
  have hcomp : standardUnlinkNormalizedComplementHomotopy H havoid (t, x) =
      standardUnlinkNormalizedComplementHomotopy H havoid (t, y) := by
    simpa only [standardUnlinkPowerIsotopyLift_proj] using hbase
  have hxy : x = y :=
    ((standardUnlinkNormalizedSphereIsotopy H).isSmoothEmbedding_slice t).isEmbedding.injective
      (congrArg Subtype.val hcomp)
  subst y
  let z := standardUnlinkPowerIsotopyLift m 0 H havoid (t, x)
  have ha : standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd a) z =
      standardUnlinkPowerIsotopyLift m a H havoid (t, x) := by
    simpa [z] using
      standardUnlinkPowerIsotopyLift_deck_add m a 0 H havoid (t, x)
  have hb : standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd b) z =
      standardUnlinkPowerIsotopyLift m b H havoid (t, x) := by
    simpa [z] using
      standardUnlinkPowerIsotopyLift_deck_add m b 0 H havoid (t, x)
  have hlabel : a = b := standardUnlinkPowerDeckZModHom_injective m z
    (ha.trans (hab.trans hb.symm))
  exact Prod.ext hlabel rfl

/-- At every time, the ranges of slices with distinct deck labels are pairwise disjoint. -/
theorem pairwise_disjoint_range_standardUnlinkPowerIsotopyLift_slice
    (m : ℕ) [NeZero m]
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (t : I) :
    Pairwise fun a b : ZMod m ↦
      Disjoint
        (range fun x ↦ standardUnlinkPowerIsotopyLift m a H havoid (t, x))
        (range fun x ↦ standardUnlinkPowerIsotopyLift m b H havoid (t, x)) := by
  intro a b hab
  rw [Set.disjoint_left]
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have hpair : (a, x) = (b, y) :=
    injective_standardUnlinkPowerIsotopyLift_family m H havoid t hy.symm
  exact hab (congrArg Prod.fst hpair)

/-! ## Relation-level lift family -/

/-- A complement-isotopy witness from the standard splitting sphere supplies one normalized
isotopy and its entire labelled family of jointly smooth lifted embeddings. -/
theorem SmoothlyIsotopicInComplement.exists_standardUnlinkPowerIsotopyLiftFamily
    (h : SmoothlyIsotopicInComplement standardSplittingSphere S)
    (m : ℕ) [NeZero m] :
    ∃ H' : SmoothSphereIsotopy standardSplittingSphere S,
      ∃ havoid' : ∀ p, H'.toFun p ∉ standardUnlinkCarrier,
        ∃ F : ZMod m → C(I × Sphere 3, StandardUnlinkPowerPullback m),
          (∀ x, H'.toFun (0, x) = equatorSphereMap x) ∧
          (∀ a x, F a (0, x) = equatorUnlinkPowerLift m a x) ∧
          (∀ a p, standardUnlinkPowerPullbackProj m (F a p) =
            H'.toUnlinkComplement havoid' p) ∧
          letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
              (StandardUnlinkPowerPullback m) :=
            standardUnlinkPowerPullbackChartedSpace m
          letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
            isManifold_standardUnlinkPowerPullback m
          (∀ a, ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 4) ∞ (F a)) ∧
            (∀ a t, Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 4) ∞
              (fun x ↦ F a (t, x))) ∧
            ∀ t, Injective (fun p : ZMod m × Sphere 3 ↦ F p.1 (t, p.2)) := by
  obtain ⟨H, havoid⟩ := h
  let H' := standardUnlinkNormalizedSphereIsotopy H
  let havoid' : ∀ p, H'.toFun p ∉ standardUnlinkCarrier :=
    standardUnlinkNormalizedSphereIsotopy_avoids H havoid
  let F := fun a ↦ standardUnlinkPowerIsotopyLift m a H havoid
  refine ⟨H', havoid', F, ?_, ?_, ?_, ?_⟩
  · exact standardUnlinkNormalizedSphereIsotopy_zero H
  · intro a
    exact standardUnlinkPowerIsotopyLift_zero m a H havoid
  · intro a p
    change standardUnlinkPowerPullbackProj m
        (standardUnlinkPowerIsotopyLift m a H havoid p) =
      standardUnlinkNormalizedComplementHomotopy H havoid p
    exact standardUnlinkPowerIsotopyLift_proj m a H havoid p
  · let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    refine ⟨fun a ↦ contMDiff_standardUnlinkPowerIsotopyLift m a H havoid, ?_, ?_⟩
    · exact fun a t ↦
        isSmoothEmbedding_standardUnlinkPowerIsotopyLift_slice m a H havoid t
    · exact injective_standardUnlinkPowerIsotopyLift_family m H havoid

end SplittingSpheres

end
