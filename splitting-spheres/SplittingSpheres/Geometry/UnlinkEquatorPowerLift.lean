/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import SplittingSpheres.Foundations.SmoothLocalDiffeomorphLift
public import SplittingSpheres.Geometry.EquatorImmersion
public import SplittingSpheres.Geometry.UnlinkCyclicCover
public import SplittingSpheres.Geometry.UnlinkDeckZMod

/-!
# Smooth equatorial lifts in the unlink power cover

This file regards the standard coordinate equator as a smooth embedding in the strict unlink
complement and constructs all of its explicitly labelled lifts to the nonzero-degree power
pullback.  The branch is given by a rotated complex logarithm: the negative of the right-normal
character has real part one half and therefore lies in the standard slit plane.

The pulled-back smooth atlas is kept explicit in every theorem whose target is the power
pullback.  No ambient isotopy, separation by a lifted sphere, or smooth structure on a compact
exterior is asserted here.
-/

@[expose] public section

open Function Metric Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- The coordinate equator, regarded as a map into the strict unlink complement. -/
def equatorUnlinkComplementMap (x : Sphere 3) : StandardUnlinkComplement :=
  ⟨equatorSphereMap x, by
    intro hx
    exact Set.disjoint_left.1 disjoint_coordinateEquator_standardUnlinkCarrier
      (by rw [← range_equatorSphereMap]; exact mem_range_self x) hx⟩

@[simp]
theorem equatorUnlinkComplementMap_coe (x : Sphere 3) :
    (equatorUnlinkComplementMap x : Sphere 4) = equatorSphereMap x :=
  rfl

theorem contMDiff_equatorUnlinkComplementMap :
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      equatorUnlinkComplementMap := by
  rw [← ContMDiff.subtypeVal_comp_iff standardUnlinkComplementOpens]
  exact contMDiff_equatorSphereMap

theorem continuous_equatorUnlinkComplementMap :
    Continuous equatorUnlinkComplementMap :=
  contMDiff_equatorUnlinkComplementMap.continuous

/-- The inherited-open-submanifold inclusion is a same-model local diffeomorphism. -/
theorem isLocalDiffeomorph_standardUnlinkComplement_subtypeVal :
    IsLocalDiffeomorph
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (Subtype.val : StandardUnlinkComplement → Sphere 4) := by
  intro x
  let _ : Nonempty StandardUnlinkComplement := ⟨x⟩
  let hOpen : IsOpenEmbedding
      (Subtype.val : StandardUnlinkComplement → Sphere 4) :=
    standardUnlinkComplementOpens.2.isOpenEmbedding_subtypeVal
  let oph : OpenPartialHomeomorph StandardUnlinkComplement (Sphere 4) :=
    hOpen.toOpenPartialHomeomorph Subtype.val
  let phi : PartialDiffeomorph
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      StandardUnlinkComplement (Sphere 4) ∞ := {
    toPartialEquiv := oph.toPartialEquiv
    open_source := oph.open_source
    open_target := oph.open_target
    contMDiffOn_toFun := by
      simpa [oph] using
        (contMDiff_subtype_val : ContMDiff
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
          (Subtype.val : StandardUnlinkComplement → Sphere 4)).contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff
        standardUnlinkComplementOpens oph.symm oph.target y).mp
      apply contMDiffWithinAt_id.congr
      · intro z hz
        exact oph.right_inv hz
      · exact oph.right_inv hy
  }
  have hx : x ∈ phi.source := by
    change x ∈ oph.source
    simp [oph]
  simpa [phi, oph] using
    (phi.isLocalDiffeomorphAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ hx)

theorem isSmoothEmbedding_equatorUnlinkComplementMap :
    Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      equatorUnlinkComplementMap := by
  apply Manifold.IsSmoothEmbedding.reflect_isLocalDiffeomorph
    isLocalDiffeomorph_standardUnlinkComplement_subtypeVal
    continuous_equatorUnlinkComplementMap
  simpa [Function.comp_def] using
    (show Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      equatorSphereMap from
        ⟨isImmersion_equatorSphereMap, isEmbedding_equatorSphereMap⟩)

/-- The right-normal character of the equator. -/
def equatorUnlinkCharacter (x : Sphere 3) : ℂ :=
  -(1 / 2 : ℂ) + (x.1 3 : ℂ) * Complex.I

@[simp]
theorem standardUnlinkRightDisplacementComplex_equatorSphereMap
    (x : Sphere 3) :
    standardUnlinkRightDisplacementComplex (equatorSphereMap x) =
      equatorUnlinkCharacter x := by
  simp [standardUnlinkRightDisplacementComplex,
    standardUnlinkNormalProjection, standardUnlinkNormalCenter,
    standardUnlinkHeight, unlinkNormalPlaneToComplex,
    Complex.equivRealProdCLM_symm_apply, equatorUnlinkCharacter]

@[simp]
theorem standardUnlinkRightNormalMap_equatorUnlinkComplementMap
    (x : Sphere 3) :
    (standardUnlinkRightNormalMap (equatorUnlinkComplementMap x) : ℂ) =
      equatorUnlinkCharacter x := by
  exact standardUnlinkRightDisplacementComplex_equatorSphereMap x

/-- The negative equatorial character lies in the standard slit plane. -/
theorem neg_equatorUnlinkCharacter_mem_slitPlane (x : Sphere 3) :
    -equatorUnlinkCharacter x ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp [equatorUnlinkCharacter]

/-- A rotated-log branch of the `m`-th root of the equatorial character. -/
def equatorUnlinkPowerRoot (m : ℕ) (x : Sphere 3) : ℂ :=
  Complex.exp
    ((Complex.log (-equatorUnlinkCharacter x) +
      (Real.pi : ℂ) * Complex.I) / (m : ℂ))

@[simp]
theorem equatorUnlinkPowerRoot_pow (m : ℕ) [NeZero m]
    (x : Sphere 3) :
    equatorUnlinkPowerRoot m x ^ m = equatorUnlinkCharacter x := by
  unfold equatorUnlinkPowerRoot
  rw [← Complex.exp_nat_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [show (m : ℂ) *
      ((Complex.log (-equatorUnlinkCharacter x) +
        (Real.pi : ℂ) * Complex.I) / (m : ℂ)) =
      Complex.log (-equatorUnlinkCharacter x) +
        (Real.pi : ℂ) * Complex.I by field_simp]
  rw [Complex.exp_add, Complex.exp_log
    (Complex.slitPlane_ne_zero (neg_equatorUnlinkCharacter_mem_slitPlane x)),
    Complex.exp_pi_mul_I]
  ring

theorem equatorUnlinkPowerRoot_ne_zero (m : ℕ) (x : Sphere 3) :
    equatorUnlinkPowerRoot m x ≠ 0 :=
  Complex.exp_ne_zero _

theorem contMDiff_equatorUnlinkCharacter :
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ ℂ) ∞
      equatorUnlinkCharacter := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
    ⟨by simp⟩
  have hcoord : ContDiff ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 3) := by
    fun_prop
  have hofReal : ContDiff ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 4) ↦ (x 3 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hcoord
  have hambient : ContDiff ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 4) ↦
        -(1 / 2 : ℂ) + (x 3 : ℂ) * Complex.I) :=
    contDiff_const.add (hofReal.mul contDiff_const)
  exact hambient.comp_contMDiff contMDiff_coe_sphere

theorem contMDiff_equatorUnlinkPowerRoot (m : ℕ) :
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ ℂ) ∞
      (equatorUnlinkPowerRoot m) := by
  intro x
  have hneg : ContDiffAt ℝ ∞ (fun z : ℂ ↦ -z)
      (equatorUnlinkCharacter x) := contDiffAt_id.neg
  have hlog : ContDiffAt ℝ ∞
      (fun z : ℂ ↦ Complex.log (-z)) (equatorUnlinkCharacter x) :=
    (Complex.contDiffAt_log (neg_equatorUnlinkCharacter_mem_slitPlane x))
      |>.restrict_scalars ℝ |>.comp _ hneg
  have harg : ContDiffAt ℝ ∞
      (fun z : ℂ ↦
        (Complex.log (-z) + (Real.pi : ℂ) * Complex.I) / (m : ℂ))
      (equatorUnlinkCharacter x) :=
    (hlog.add contDiffAt_const).div_const _
  have hbranch : ContMDiffAt
      (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : ℂ ↦ Complex.exp
        ((Complex.log (-z) + (Real.pi : ℂ) * Complex.I) / (m : ℂ)))
      (equatorUnlinkCharacter x) :=
    contMDiffAt_iff_contDiffAt.mpr
      ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp _ harg)
  exact hbranch.comp x contMDiff_equatorUnlinkCharacter.contMDiffAt

/-- A fixed roots-of-unity translate of the explicit equatorial root. -/
def equatorUnlinkPowerRootTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) : ℂ :=
  (((standardRootsOfUnityZModMulEquiv m
    (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
      equatorUnlinkPowerRoot m x

@[simp]
theorem equatorUnlinkPowerRootTranslate_pow
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    equatorUnlinkPowerRootTranslate m a x ^ m =
      equatorUnlinkCharacter x := by
  rw [equatorUnlinkPowerRootTranslate, mul_pow,
    (mem_rootsOfUnity' m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1).mp
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).2,
    one_mul, equatorUnlinkPowerRoot_pow]

theorem equatorUnlinkPowerRootTranslate_ne_zero
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    equatorUnlinkPowerRootTranslate m a x ≠ 0 :=
  mul_ne_zero
    (Units.ne_zero
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1)
    (equatorUnlinkPowerRoot_ne_zero m x)

theorem contMDiff_equatorUnlinkPowerRootTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ ℂ) ∞
      (equatorUnlinkPowerRootTranslate m a) := by
  let c : ℂ :=
    (((standardRootsOfUnityZModMulEquiv m
      (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ)
  have hmul : ContMDiff
      (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : ℂ ↦ c * z) :=
    contMDiff_iff_contDiff.mpr (contDiff_const.mul contDiff_id)
  exact hmul.comp (contMDiff_equatorUnlinkPowerRoot m)

/-- The punctured-complex coordinate of a fixed equatorial lift. -/
def equatorUnlinkPowerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    {z : ℂ // z ≠ 0} :=
  ⟨equatorUnlinkPowerRootTranslate m a x,
    equatorUnlinkPowerRootTranslate_ne_zero m a x⟩

@[simp]
theorem equatorUnlinkPowerCoordinate_coe
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    (equatorUnlinkPowerCoordinate m a x : ℂ) =
      equatorUnlinkPowerRootTranslate m a x :=
  rfl

/-- The explicit fixed-label lift of the equator into the power pullback. -/
def equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    StandardUnlinkPowerPullback m :=
  ⟨(equatorUnlinkComplementMap x, equatorUnlinkPowerCoordinate m a x), by
    apply Subtype.ext
    change standardUnlinkRightDisplacementComplex
        (equatorUnlinkComplementMap x).1 =
      equatorUnlinkPowerRootTranslate m a x ^ m
    rw [equatorUnlinkComplementMap_coe,
      standardUnlinkRightDisplacementComplex_equatorSphereMap,
      equatorUnlinkPowerRootTranslate_pow]⟩

@[simp]
theorem equatorUnlinkPowerLift_proj
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    standardUnlinkPowerPullbackProj m (equatorUnlinkPowerLift m a x) =
      equatorUnlinkComplementMap x :=
  rfl

@[simp]
theorem equatorUnlinkPowerLift_powerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    (equatorUnlinkPowerLift m a x).1.2.1 =
      equatorUnlinkPowerRootTranslate m a x :=
  rfl

@[simp]
theorem equatorUnlinkPowerLift_power
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    (equatorUnlinkPowerLift m a x).1.2.1 ^ m =
      equatorUnlinkCharacter x :=
  equatorUnlinkPowerRootTranslate_pow m a x

theorem continuous_equatorUnlinkPowerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (equatorUnlinkPowerCoordinate m a) := by
  apply Continuous.subtype_mk
  exact (contMDiff_equatorUnlinkPowerRootTranslate m a).continuous

theorem continuous_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (equatorUnlinkPowerLift m a) := by
  apply Continuous.subtype_mk
  exact continuous_equatorUnlinkComplementMap.prodMk
    (continuous_equatorUnlinkPowerCoordinate m a)

theorem contMDiff_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    ContMDiff
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
  apply contMDiff_of_comp_isLocalDiffeomorph
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
    (continuous_equatorUnlinkPowerLift m a)
  exact contMDiff_equatorUnlinkComplementMap.congr fun _ ↦ rfl

theorem isSmoothEmbedding_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    Manifold.IsSmoothEmbedding
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
  apply Manifold.IsSmoothEmbedding.reflect_isLocalDiffeomorph
    (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
    (continuous_equatorUnlinkPowerLift m a)
  rw [show standardUnlinkPowerPullbackProj m ∘
      equatorUnlinkPowerLift m a = equatorUnlinkComplementMap by
    funext x
    rfl]
  exact isSmoothEmbedding_equatorUnlinkComplementMap

/-- The fixed-label lift, bundled as a smooth embedding in the pulled-back atlas. -/
def equatorUnlinkPowerLiftEmbedding
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    TauCeti.SmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (Sphere 3) (StandardUnlinkPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  exact TauCeti.SmoothEmbedding.ofIsSmoothEmbedding
    (equatorUnlinkPowerLift m a)
    (isSmoothEmbedding_equatorUnlinkPowerLift m a)

@[simp]
theorem equatorUnlinkPowerLiftEmbedding_apply
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    equatorUnlinkPowerLiftEmbedding m a x =
      equatorUnlinkPowerLift m a x := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  simp [equatorUnlinkPowerLiftEmbedding]

theorem injective_equatorUnlinkComplementMap :
    Function.Injective equatorUnlinkComplementMap := by
  intro x y hxy
  apply isEmbedding_equatorSphereMap.injective
  exact congrArg Subtype.val hxy

/-- Labels and source points are jointly detected by the explicit lifts. -/
theorem injective_equatorUnlinkPowerLift_family
    (m : ℕ) [NeZero m] :
    Function.Injective (fun p : ZMod m × Sphere 3 ↦
      equatorUnlinkPowerLift m p.1 p.2) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ hab
  have hbase := congrArg (standardUnlinkPowerPullbackProj m) hab
  have hxy : x = y := injective_equatorUnlinkComplementMap <| by
    simpa only [equatorUnlinkPowerLift_proj] using hbase
  subst y
  have hval := congrArg
    (fun z : StandardUnlinkPowerPullback m ↦ z.1.2.1) hab
  have hroot :
      (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) =
        (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd b)).1 : ℂˣ) : ℂ) := by
    apply mul_right_cancel₀ (equatorUnlinkPowerRoot_ne_zero m x)
    exact hval
  have hroots :
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) =
        standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b) := by
    apply Subtype.ext
    apply Units.ext
    exact hroot
  have hindex : a = b := Multiplicative.ofAdd.injective <|
    (standardRootsOfUnityZModMulEquiv m).injective hroots
  exact Prod.ext hindex rfl

/-- Different labels give disjoint embedded equatorial lifts. -/
theorem pairwise_disjoint_range_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] :
    Pairwise fun a b : ZMod m ↦
      Disjoint (range (equatorUnlinkPowerLift m a))
        (range (equatorUnlinkPowerLift m b)) := by
  intro a b hab
  rw [Set.disjoint_left]
  intro z hza hzb
  obtain ⟨x, rfl⟩ := hza
  obtain ⟨y, hy⟩ := hzb
  have hpair : (a, x) = (b, y) :=
    injective_equatorUnlinkPowerLift_family m hy.symm
  exact hab (congrArg Prod.fst hpair)

end SplittingSpheres
