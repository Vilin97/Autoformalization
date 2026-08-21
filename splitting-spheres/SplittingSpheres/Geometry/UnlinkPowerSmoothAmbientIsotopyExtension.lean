/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkComplementSmoothAmbientIsotopyExtension

/-!
# Smooth ambient-isotopy slices on standard unlink power covers

A smooth family of downstairs diffeomorphism slices lifts slice by slice through the standard
unlink power covering.  The underlying equivalence is the time-slice homeomorphism of the
canonical lifted ambient isotopy.  Smoothness of the forward map is reflected through the smooth
covering projection.  For the inverse, its projection law follows from the forward square and
injectivity of the downstairs diffeomorphism, after which smoothness is reflected in the same way.

Applying this construction to the normalized endpoint-flattened complement extension gives a
continuous ambient isotopy in every finite power cover whose individual slices are genuine `C∞`
diffeomorphisms.  The lifted isotopy agrees exactly with the existing labelled sphere lift after
endpoint flattening.  No joint smoothness in the time parameter is asserted.
-/

@[expose] public section

open Function Topology
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace SplittingSpheres

variable {S : SmoothSphereEmbedding 3 4}

/-- The time slice of the lifted ambient isotopy, bundled as a smooth diffeomorphism for the
pulled-back smooth structure on the standard unlink power cover. -/
noncomputable def standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph
    (m : ℕ) [NeZero m]
    (Phi : TauCeti.AmbientIsotopy StandardUnlinkComplement)
    (Psi : I →
      StandardUnlinkComplement
        ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
        StandardUnlinkComplement)
    (hPhi : ∀ (t : I) (y : StandardUnlinkComplement),
      Phi.toContinuousMap (t, y) = Psi t y)
    (t : I) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    StandardUnlinkPowerPullback m ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
      StandardUnlinkPowerPullback m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let PhiLift := IsCoveringMap.liftAmbientIsotopy
    (isCoveringMap_standardUnlinkPowerPullbackProj m) Phi
  refine
    { toEquiv := (PhiLift.homeomorph t).toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply contMDiff_of_comp_isLocalDiffeomorph (𝓡 4) (𝓡 4) (𝓡 4)
      (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
      (PhiLift.homeomorph t).continuous
    have hsmooth := (Psi t).contMDiff.comp
      (smoothCover_standardUnlinkPowerPullbackProj m).contMDiff
    have hcomp : standardUnlinkPowerPullbackProj m ∘ (PhiLift.homeomorph t) =
        (Psi t) ∘ standardUnlinkPowerPullbackProj m := by
      funext z
      simp only [Function.comp_apply, TauCeti.AmbientIsotopy.homeomorph_apply]
      rw [IsCoveringMap.proj_liftAmbientIsotopy
        (isCoveringMap_standardUnlinkPowerPullbackProj m) Phi (t, z), hPhi]
    rw [hcomp]
    exact hsmooth
  · apply contMDiff_of_comp_isLocalDiffeomorph (𝓡 4) (𝓡 4) (𝓡 4)
      (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
      (PhiLift.homeomorph t).symm.continuous
    have hsmooth := (Psi t).symm.contMDiff.comp
      (smoothCover_standardUnlinkPowerPullbackProj m).contMDiff
    have hcomp : standardUnlinkPowerPullbackProj m ∘ (PhiLift.homeomorph t).symm =
        (Psi t).symm ∘ standardUnlinkPowerPullbackProj m := by
      funext z
      change standardUnlinkPowerPullbackProj m ((PhiLift.homeomorph t).symm z) =
        (Psi t).symm (standardUnlinkPowerPullbackProj m z)
      apply (Psi t).injective
      change Psi t
          (standardUnlinkPowerPullbackProj m ((PhiLift.homeomorph t).symm z)) =
        Psi t ((Psi t).symm (standardUnlinkPowerPullbackProj m z))
      rw [(Psi t).apply_symm_apply]
      rw [← hPhi]
      rw [← IsCoveringMap.proj_liftAmbientIsotopy
        (isCoveringMap_standardUnlinkPowerPullbackProj m) Phi
        (t, (PhiLift.homeomorph t).symm z)]
      rw [← TauCeti.AmbientIsotopy.homeomorph_apply]
      rw [(PhiLift.homeomorph t).apply_symm_apply]
    rw [hcomp]
    exact hsmooth

@[simp]
theorem standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (Phi : TauCeti.AmbientIsotopy StandardUnlinkComplement)
    (Psi : I →
      StandardUnlinkComplement
        ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
        StandardUnlinkComplement)
    (hPhi : ∀ (t : I) (y : StandardUnlinkComplement),
      Phi.toContinuousMap (t, y) = Psi t y)
    (t : I) (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph m Phi Psi hPhi t z =
      (IsCoveringMap.liftAmbientIsotopy
        (isCoveringMap_standardUnlinkPowerPullbackProj m) Phi).toContinuousMap (t, z) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  rw [standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph]
  exact TauCeti.AmbientIsotopy.homeomorph_apply
    (IsCoveringMap.liftAmbientIsotopy
      (isCoveringMap_standardUnlinkPowerPullbackProj m) Phi) t z

@[simp]
theorem standardUnlinkPowerPullbackProj_liftAmbientIsotopySliceDiffeomorph
    (m : ℕ) [NeZero m]
    (Phi : TauCeti.AmbientIsotopy StandardUnlinkComplement)
    (Psi : I →
      StandardUnlinkComplement
        ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
        StandardUnlinkComplement)
    (hPhi : ∀ (t : I) (y : StandardUnlinkComplement),
      Phi.toContinuousMap (t, y) = Psi t y)
    (t : I) (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerPullbackProj m
        (standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph
          m Phi Psi hPhi t z) =
      Psi t (standardUnlinkPowerPullbackProj m z) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  calc
    standardUnlinkPowerPullbackProj m
        (standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph
          m Phi Psi hPhi t z) =
      standardUnlinkPowerPullbackProj m
        ((IsCoveringMap.liftAmbientIsotopy
          (isCoveringMap_standardUnlinkPowerPullbackProj m) Phi).toContinuousMap
            (t, z)) := by
              rw [standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph_apply]
    _ = Phi.toContinuousMap
        (t, standardUnlinkPowerPullbackProj m z) :=
      IsCoveringMap.proj_liftAmbientIsotopy
        (isCoveringMap_standardUnlinkPowerPullbackProj m) Phi (t, z)
    _ = Psi t (standardUnlinkPowerPullbackProj m z) := hPhi t _

@[simp]
theorem standardUnlinkPowerPullbackProj_liftAmbientIsotopySliceDiffeomorph_symm
    (m : ℕ) [NeZero m]
    (Phi : TauCeti.AmbientIsotopy StandardUnlinkComplement)
    (Psi : I →
      StandardUnlinkComplement
        ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
        StandardUnlinkComplement)
    (hPhi : ∀ (t : I) (y : StandardUnlinkComplement),
      Phi.toContinuousMap (t, y) = Psi t y)
    (t : I) (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    standardUnlinkPowerPullbackProj m
        ((standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph
          m Phi Psi hPhi t).symm z) =
      (Psi t).symm (standardUnlinkPowerPullbackProj m z) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply (Psi t).injective
  change Psi t
      (standardUnlinkPowerPullbackProj m
        ((standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph
          m Phi Psi hPhi t).symm z)) =
    Psi t ((Psi t).symm (standardUnlinkPowerPullbackProj m z))
  rw [(Psi t).apply_symm_apply]
  rw [← standardUnlinkPowerPullbackProj_liftAmbientIsotopySliceDiffeomorph
    m Phi Psi hPhi t
    ((standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph
      m Phi Psi hPhi t).symm z)]
  rw [(standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph
    m Phi Psi hPhi t).apply_symm_apply]

/-- The endpoint-flattened normalized sphere isotopy has a lifted ambient extension whose every
time slice is exactly a smooth diffeomorphism of the standard unlink power cover. -/
theorem exists_standardUnlinkNormalizedFlattenedPowerSmoothAmbientIsotopy
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ∃ (Phi : TauCeti.AmbientIsotopy StandardUnlinkComplement)
        (Psi : I →
          StandardUnlinkComplement
            ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
            StandardUnlinkComplement)
        (PhiLift : TauCeti.AmbientIsotopy (StandardUnlinkPowerPullback m))
        (PsiLift : I →
          StandardUnlinkPowerPullback m
            ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
            StandardUnlinkPowerPullback m),
      PhiLift = IsCoveringMap.liftAmbientIsotopy
        (isCoveringMap_standardUnlinkPowerPullbackProj m) Phi ∧
      (∀ (t : I) (y : StandardUnlinkComplement),
        Phi.toContinuousMap (t, y) = Psi t y) ∧
      (∀ (t : I) (x : Sphere 3),
        Phi.toContinuousMap (t, equatorUnlinkComplementMap x) =
          standardUnlinkNormalizedComplementHomotopy H havoid
            (unitInterval.endpointFlatTime t, x)) ∧
      (∀ (t : I) (z : StandardUnlinkPowerPullback m),
        PhiLift.toContinuousMap (t, z) = PsiLift t z) ∧
      (∀ (t : I) (z : StandardUnlinkPowerPullback m),
        standardUnlinkPowerPullbackProj m (PsiLift t z) =
          Psi t (standardUnlinkPowerPullbackProj m z)) ∧
      ∀ (t : I) (x : Sphere 3),
        PhiLift.toContinuousMap (t, equatorUnlinkPowerLift m a x) =
          standardUnlinkPowerIsotopyLift m a H havoid
            (unitInterval.endpointFlatTime t, x) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  obtain ⟨Phi, Psi, hPhi, htrace⟩ :=
    exists_standardUnlinkNormalizedFlattenedComplementSmoothAmbientIsotopy H havoid
  let PhiLift : TauCeti.AmbientIsotopy (StandardUnlinkPowerPullback m) :=
    IsCoveringMap.liftAmbientIsotopy
      (isCoveringMap_standardUnlinkPowerPullbackProj m) Phi
  let PsiLift : I →
      StandardUnlinkPowerPullback m
        ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
        StandardUnlinkPowerPullback m := fun t ↦
    standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph m Phi Psi hPhi t
  refine ⟨Phi, Psi, PhiLift, PsiLift, rfl, hPhi, htrace, ?_, ?_, ?_⟩
  · intro t z
    exact (standardUnlinkPowerLiftAmbientIsotopySliceDiffeomorph_apply
      m Phi Psi hPhi t z).symm
  · intro t z
    exact standardUnlinkPowerPullbackProj_liftAmbientIsotopySliceDiffeomorph
      m Phi Psi hPhi t z
  · intro t x
    exact liftAmbientIsotopy_agrees_standardUnlinkPowerIsotopyLift_endpointFlatTime
      m a H havoid Phi htrace t x

end SplittingSpheres

end
