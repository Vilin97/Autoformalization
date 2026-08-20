/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import SplittingSpheres.Foundations.SmoothLocalDiffeomorphLift
public import SplittingSpheres.Geometry.UnlinkDeckZMod

/-!
# Smooth deck transformations of the unlink power pullback

The explicit roots-of-unity action on the standard unlink power pullback is already known to be
a deck action by homeomorphisms.  With the pulled-back smooth atlas on the nonzero-degree cover,
each action map is smooth because its composite with the smooth covering projection is the
projection itself.  Applying the same argument to the inverse action bundles these maps as
genuine diffeomorphisms and gives the corresponding roots-of-unity and `ZMod`-indexed
homomorphisms into the smooth diffeomorphism group.

These are the displayed algebraic deck transformations only.  This file does not classify all
deck transformations and does not put a smooth structure on the compact exterior or any planar
pushout model.
-/

@[expose] public section

noncomputable section

open Function
open scoped ContDiff Manifold

namespace SplittingSpheres

/-! ## The roots-of-unity action by diffeomorphisms -/

/-- The displayed deck transformation by an `m`th root of unity, as a diffeomorphism for the
pulled-back smooth atlas on the standard unlink power cover. -/
noncomputable def standardUnlinkPowerDeckDiffeomorph
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    StandardUnlinkPowerPullback m ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯
      StandardUnlinkPowerPullback m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  refine
    { toEquiv := (standardUnlinkPowerDeckHomeomorph m u).toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply contMDiff_of_comp_isLocalDiffeomorph
      (𝓡 4) (𝓡 4) (𝓡 4)
      (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
      (continuous_standardUnlinkPowerDeckMap m u)
    exact (smoothCover_standardUnlinkPowerPullbackProj m).contMDiff.congr
      (fun _ ↦ rfl)
  · apply contMDiff_of_comp_isLocalDiffeomorph
      (𝓡 4) (𝓡 4) (𝓡 4)
      (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
      (continuous_standardUnlinkPowerDeckMap m u⁻¹)
    exact (smoothCover_standardUnlinkPowerPullbackProj m).contMDiff.congr
      (fun _ ↦ rfl)

/-- The smooth deck transformation acts by the original roots-of-unity action. -/
@[simp]
theorem standardUnlinkPowerDeckDiffeomorph_apply
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerDeckDiffeomorph m u z = u • z :=
  rfl

/-- Forgetting smoothness recovers the previously defined deck homeomorphism exactly. -/
@[simp]
theorem standardUnlinkPowerDeckDiffeomorph_toHomeomorph
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    (standardUnlinkPowerDeckDiffeomorph m u).toHomeomorph =
      standardUnlinkPowerDeckHomeomorph m u :=
  rfl

/-- Every displayed smooth deck transformation lies over the identity of the strict unlink
complement. -/
@[simp]
theorem standardUnlinkPowerPullbackProj_deckDiffeomorph
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerPullbackProj m
        (standardUnlinkPowerDeckDiffeomorph m u z) =
      standardUnlinkPowerPullbackProj m z :=
  rfl

/-- The unit root gives the identity smooth diffeomorphism. -/
@[simp]
theorem standardUnlinkPowerDeckDiffeomorph_one
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerDeckDiffeomorph m 1 = 1 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply Diffeomorph.ext
  exact standardUnlinkPowerDeckMap_one m

/-- Multiplication of roots agrees with composition in the smooth diffeomorphism group. -/
theorem standardUnlinkPowerDeckDiffeomorph_mul
    (m : ℕ) [NeZero m] (u v : rootsOfUnity m ℂ) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerDeckDiffeomorph m (u * v) =
      standardUnlinkPowerDeckDiffeomorph m u *
        standardUnlinkPowerDeckDiffeomorph m v := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply Diffeomorph.ext
  exact standardUnlinkPowerDeckMap_mul m u v

/-- Inversion of the root agrees with inversion of the smooth deck transformation. -/
@[simp]
theorem standardUnlinkPowerDeckDiffeomorph_inv
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerDeckDiffeomorph m u⁻¹ =
      (standardUnlinkPowerDeckDiffeomorph m u)⁻¹ := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply Diffeomorph.ext
  intro z
  rfl

/-- The explicit roots-of-unity deck action as a homomorphism into the smooth diffeomorphism
group of the power pullback. -/
noncomputable def standardUnlinkPowerDeckDiffeomorphHom
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    rootsOfUnity m ℂ →*
      TauCeti.Diff (𝓡 4) (StandardUnlinkPowerPullback m) ∞ := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact
    { toFun := standardUnlinkPowerDeckDiffeomorph m
      map_one' := standardUnlinkPowerDeckDiffeomorph_one m
      map_mul' := standardUnlinkPowerDeckDiffeomorph_mul m }

/-- Evaluation of the roots-of-unity smooth deck-action homomorphism. -/
@[simp]
theorem standardUnlinkPowerDeckDiffeomorphHom_apply
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerDeckDiffeomorphHom m u z = u • z :=
  rfl

/-! ## The `ZMod`-indexed smooth deck action -/

/-- The canonical multiplicative `ZMod m` indexing of the displayed smooth deck action. -/
noncomputable def standardUnlinkPowerDeckZModDiffeomorphHom
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    Multiplicative (ZMod m) →*
      TauCeti.Diff (𝓡 4) (StandardUnlinkPowerPullback m) ∞ := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact (standardUnlinkPowerDeckDiffeomorphHom m).comp
    (standardRootsOfUnityZModMulEquiv m).toMonoidHom

/-- Evaluation of the `ZMod`-indexed smooth deck-action homomorphism. -/
@[simp]
theorem standardUnlinkPowerDeckZModDiffeomorphHom_apply
    (m : ℕ) [NeZero m] (a : ZMod m)
    (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerDeckZModDiffeomorphHom m
        (Multiplicative.ofAdd a) z =
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) • z :=
  rfl

/-- Forgetting smoothness recovers the canonical `ZMod`-indexed deck homeomorphism exactly. -/
@[simp]
theorem standardUnlinkPowerDeckZModDiffeomorphHom_toHomeomorph
    (m : ℕ) [NeZero m] (a : Multiplicative (ZMod m)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    (standardUnlinkPowerDeckZModDiffeomorphHom m a).toHomeomorph =
      standardUnlinkPowerDeckZModHom m a :=
  rfl

end SplittingSpheres
