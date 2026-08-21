/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckEquatorComparison
public import TauCeti.Geometry.Manifold.LocallyFlat.Smooth

/-!
# Local flatness of the transported planar neck spheres

This file proves that the topologically parametrized neck spheres transported from the planar
flower model are locally flat in the smooth unlink power pullback.  The proof first obtains an
explicit complementary direction for the coordinate equator, lifts that immersion through the
smooth power cover, and then uses the exact source homeomorphism comparing the transported neck
with the smooth equatorial lift.

The resulting slice charts flatten the range of the transported neck.  No smoothness claim is
made for its original topological parametrization, and no global collar or gluing construction is
provided here.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace SplittingSpheres

universe uE uE' uM uQ uR uH uH'

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {Q : Type uQ} [TopologicalSpace Q] [ChartedSpace H' Q]
variable {R : Type uR} [TopologicalSpace R] [ChartedSpace H' R]
variable {n : ℕ∞ω}

/-- A complementary immersion can be reflected through a local diffeomorphism while preserving
the displayed complementary direction. -/
theorem isImmersionOfComplement_reflect_isLocalDiffeomorph
    [IsManifold I n M] [IsManifold J n Q] [IsManifold J n R]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : Q → R} {f : M → Q}
    (hp : IsLocalDiffeomorph J J n p)
    (hf : Continuous f)
    (hpf : Manifold.IsImmersionOfComplement F I J n (p ∘ f)) :
    Manifold.IsImmersionOfComplement F I J n f := by
  intro x
  let hpx := hp (f x)
  have hpost : Manifold.IsImmersionAtOfComplement F I J n
      (hpx.localInverse ∘ (p ∘ f)) x :=
    Manifold.IsImmersionAtOfComplement.postcomp_partialDiffeomorph
      (hpf x) hpx.localInverse hpx.localInverse_mem_source
  apply hpost.congr_of_eventuallyEq
  filter_upwards [hpx.localInverse_eventuallyEq_left.comp_tendsto
    hf.continuousAt] with y hy
  simpa only [Function.comp_apply, id_eq] using hy

/-- The coordinate equator in the strict unlink complement has its normal line as an explicit
complementary direction. -/
theorem isImmersionOfComplement_equatorUnlinkComplementMap :
    Manifold.IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      equatorUnlinkComplementMap := by
  apply isImmersionOfComplement_reflect_isLocalDiffeomorph
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
    (F := ℝ) isLocalDiffeomorph_standardUnlinkComplement_subtypeVal
      continuous_equatorUnlinkComplementMap
  simpa [Function.comp_def] using isImmersionOfComplement_equatorSphereMap

/-- Every lifted coordinate equator is a smooth immersion with an explicit complementary line in
the pulled-back smooth atlas. -/
theorem isImmersionOfComplement_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    Manifold.IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (equatorUnlinkPowerLift m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  apply isImmersionOfComplement_reflect_isLocalDiffeomorph
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
    (F := ℝ)
      (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
      (continuous_equatorUnlinkPowerLift m a)
  exact isImmersionOfComplement_equatorUnlinkComplementMap.congr <| by
    funext x
    exact equatorUnlinkPowerLift_proj m a x

/-- The transported old neck sphere is locally flat in the strict unlink power pullback.

This is a topological local-flatness statement.  In particular, it does not assert that the old
source parametrization is smooth. -/
theorem isLocallyFlat_coordinateUnlinkExteriorPlanarTransportedNeckSphereMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    TauCeti.IsLocallyFlat (EuclideanSpace ℝ (Fin 3)) ℝ
      (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let b := a - coordinateUnlinkExteriorPlanarSmoothNeckShift m
  have hsmooth : TauCeti.IsLocallyFlat (EuclideanSpace ℝ (Fin 3)) ℝ
      (equatorUnlinkPowerLift m b) :=
    TauCeti.IsLocallyFlat.of_isImmersionOfComplement_of_isEmbedding
      (isImmersionOfComplement_equatorUnlinkPowerLift m b)
      (isSmoothEmbedding_equatorUnlinkPowerLift m b).isEmbedding
  have hcomp := hsmooth.comp_homeomorph
    (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m a)
  have heq : coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a =
      equatorUnlinkPowerLift m b ∘
        coordinateUnlinkExteriorPlanarNeckEquatorReparam m a := by
    simpa only [b, sub_add_cancel] using
      transportedNeckSphereMap_eq_equatorPowerLift_comp_reparam m b
  rw [heq]
  exact hcomp

/-- A slice chart flattening the range of the transported neck sphere at any chosen source
point. -/
theorem exists_isSliceChart_coordinateUnlinkExteriorPlanarTransportedNeckSphereMap
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ∃ φ : OpenPartialHomeomorph (StandardUnlinkPowerPullback m)
        (EuclideanSpace ℝ (Fin 3) × ℝ),
      coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a x ∈ φ.source ∧
      TauCeti.IsSliceChart φ
        ((Set.univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ ({0} : Set ℝ))
        (Set.range (coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a)) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact
    (isLocallyFlat_coordinateUnlinkExteriorPlanarTransportedNeckSphereMap m a).exists_isSliceChart x

end SplittingSpheres

end
