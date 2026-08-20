/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothCoverLift
public import SplittingSpheres.Foundations.RelativeDiffeomorph
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Jointly smooth lifts of one-parameter families

This file applies the smooth covering-space lifting criterion to the whole product
`unitInterval × E`.  This is stronger than separately lifting every time slice: the resulting
lift is smooth jointly in time and the manifold variable.

The product lift is based only at `(0, e₀)`.  If every base slice fixes `p e₀`, uniqueness of the
lift of the resulting constant path then proves that every lifted slice fixes `e₀`; this is a
conclusion, not an extra pointwise choice of sheets.
-/

@[expose] public section

open Function
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

universe uE uX uHE uHX

variable {EE EX : Type*}
  [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX]
variable {HE : Type uHE} [TopologicalSpace HE]
  {HX : Type uHX} [TopologicalSpace HX]
variable {IE : ModelWithCorners ℝ EE HE} {IX : ModelWithCorners ℝ EX HX}
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E]
  {X : Type uX} [TopologicalSpace X] [ChartedSpace HX X]
variable {n : ℕ∞ω} {p : E → X}

namespace SmoothCover

/-- Evaluate a family on the projection of the total-space variable. -/
def familyAfterProjection (F : unitInterval × X → X) (p : E → X) :
    unitInterval × E → X :=
  fun q ↦ F (q.1, p q.2)

/-- Joint smoothness is preserved when the space variable is first projected through a smooth
cover. -/
theorem contMDiff_familyAfterProjection (hp : SmoothCover IE IX n p)
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) :
    ContMDiff ((𝓡∂ 1).prod IE) IX n (familyAfterProjection F p) :=
  hF.comp (contMDiff_fst.prodMk (hp.contMDiff.comp contMDiff_snd))

/-- Every time slice of a jointly smooth base family is smooth. -/
theorem contMDiff_familySlice (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (t : unitInterval) :
    ContMDiff IX IX n (fun x ↦ F (t, x)) :=
  hF.comp (contMDiff_const.prodMk contMDiff_id)

/-- The exact product-domain lifting criterion for a jointly smooth based family. -/
def FamilyLiftingCriterion (hp : SmoothCover IE IX n p)
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hbase : p e₀ = F ((0 : unitInterval), p e₀)) : Prop :=
  (_root_.FundamentalGroup.map
      ⟨familyAfterProjection F p,
        (hp.contMDiff_familyAfterProjection F hF).continuous⟩
      ((0 : unitInterval), e₀)).range ≤
    (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩
      (show p e₀ = familyAfterProjection F p ((0 : unitInterval), e₀) from hbase)).range

/-- A jointly smooth family fixing `p e₀` has a unique jointly smooth product lift based at
`(0, e₀)`, provided the honest fundamental-group lifting criterion holds on the whole product
domain. -/
theorem existsUnique_basedFamilyLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm) :
    ∃! L : unitInterval × E → E,
      ContMDiff ((𝓡∂ 1).prod IE) IE n L ∧
        L ((0 : unitInterval), e₀) = e₀ ∧
        p ∘ L = familyAfterProjection F p := by
  let _ : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace ℝ
  let _ : PathConnectedSpace unitInterval :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  exact hp.existsUnique_contMDiff_lift_of_range_le
    (hp.contMDiff_familyAfterProjection F hF) (hfix 0).symm hle

/-- The canonical jointly smooth lift selected by `existsUnique_basedFamilyLift`. -/
noncomputable def basedFamilyLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm) :
    unitInterval × E → E :=
  Classical.choose (hp.existsUnique_basedFamilyLift F hF e₀ hfix hle)

/-- The defining properties of the canonical jointly smooth family lift. -/
theorem basedFamilyLift_spec (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm) :
    ContMDiff ((𝓡∂ 1).prod IE) IE n (hp.basedFamilyLift F hF e₀ hfix hle) ∧
      hp.basedFamilyLift F hF e₀ hfix hle ((0 : unitInterval), e₀) = e₀ ∧
      p ∘ hp.basedFamilyLift F hF e₀ hfix hle = familyAfterProjection F p :=
  (Classical.choose_spec (hp.existsUnique_basedFamilyLift F hF e₀ hfix hle)).1

/-- The canonical family lift is smooth jointly in time and the total-space variable. -/
theorem basedFamilyLift_contMDiff (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm) :
    ContMDiff ((𝓡∂ 1).prod IE) IE n (hp.basedFamilyLift F hF e₀ hfix hle) :=
  (hp.basedFamilyLift_spec F hF e₀ hfix hle).1

/-- Pointwise projection formula for every time slice of the family lift. -/
theorem proj_basedFamilyLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm)
    (t : unitInterval) (z : E) :
    p (hp.basedFamilyLift F hF e₀ hfix hle (t, z)) = F (t, p z) :=
  congrFun (hp.basedFamilyLift_spec F hF e₀ hfix hle).2.2 (t, z)

/-- The selected lift starts at the prescribed point over time `0`. -/
@[simp]
theorem basedFamilyLift_zero_basepoint (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm) :
    hp.basedFamilyLift F hF e₀ hfix hle ((0 : unitInterval), e₀) = e₀ :=
  (hp.basedFamilyLift_spec F hF e₀ hfix hle).2.1

/-- The path traced by the selected point in the lifted family. -/
def basedFamilyLiftPointPath (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm) : unitInterval → E :=
  fun t ↦ hp.basedFamilyLift F hF e₀ hfix hle (t, e₀)

/-- The selected lift path is smooth. -/
theorem basedFamilyLiftPointPath_contMDiff (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm) :
    ContMDiff (𝓡∂ 1) IE n (hp.basedFamilyLiftPointPath F hF e₀ hfix hle) :=
  (hp.basedFamilyLift_contMDiff F hF e₀ hfix hle).comp
    (contMDiff_id.prodMk contMDiff_const)

/-- The selected lift path projects to the fixed basepoint. -/
theorem proj_basedFamilyLiftPointPath (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm)
    (t : unitInterval) :
    p (hp.basedFamilyLiftPointPath F hF e₀ hfix hle t) = p e₀ := by
  rw [basedFamilyLiftPointPath, hp.proj_basedFamilyLift F hF e₀ hfix hle, hfix]

/-- Because the downstairs point is fixed at every time, uniqueness of path lifting forces the
selected point upstairs to remain `e₀`.  No independent choice of a lift at each time is used. -/
@[simp]
theorem basedFamilyLift_basepoint (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm)
    (t : unitInterval) :
    hp.basedFamilyLift F hF e₀ hfix hle (t, e₀) = e₀ := by
  have hpath : hp.basedFamilyLiftPointPath F hF e₀ hfix hle = fun _ ↦ e₀ := by
    apply hp.isCoveringMap.eq_of_comp_eq
      (hp.basedFamilyLiftPointPath_contMDiff F hF e₀ hfix hle).continuous
      continuous_const
    · funext u
      exact hp.proj_basedFamilyLiftPointPath F hF e₀ hfix hle u
    · exact (hp.basedFamilyLift_zero_basepoint F hF e₀ hfix hle)
  exact congrFun hpath t

/-- Each time slice of a jointly smooth family lift is smooth. -/
theorem basedFamilyLift_slice_contMDiff (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm)
    (t : unitInterval) :
    ContMDiff IE IE n (fun z ↦ hp.basedFamilyLift F hF e₀ hfix hle (t, z)) :=
  (hp.basedFamilyLift_contMDiff F hF e₀ hfix hle).comp
    (contMDiff_const.prodMk contMDiff_id)

/-- Whenever a time slice preserves the recovered subgroup, the slice of the joint product lift
is the existing canonical `basedLift` of that base self-map. -/
theorem basedFamilyLift_slice_eq_basedLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm)
    (t : unitInterval)
    (hpres : hp.PreservesRecoveredSubgroup (fun x ↦ F (t, x))
      (contMDiff_familySlice F hF t).continuous e₀ (hfix t)) :
    (fun z ↦ hp.basedFamilyLift F hF e₀ hfix hle (t, z)) =
      hp.basedLift (fun x ↦ F (t, x)) (contMDiff_familySlice F hF t)
        e₀ (hfix t) hpres := by
  apply hp.eq_basedLift (fun x ↦ F (t, x)) (contMDiff_familySlice F hF t)
    e₀ (hfix t) hpres
  · exact hp.basedFamilyLift_slice_contMDiff F hF e₀ hfix hle t
  · exact hp.basedFamilyLift_basepoint F hF e₀ hfix hle t
  · funext z
    exact hp.proj_basedFamilyLift F hF e₀ hfix hle t z

/-- Initial-slice specialization of `basedFamilyLift_slice_eq_basedLift`. -/
theorem basedFamilyLift_zero_eq_basedLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm)
    (hpres : hp.PreservesRecoveredSubgroup (fun x ↦ F ((0 : unitInterval), x))
      (contMDiff_familySlice F hF 0).continuous e₀ (hfix 0)) :
    (fun z ↦ hp.basedFamilyLift F hF e₀ hfix hle ((0 : unitInterval), z)) =
      hp.basedLift (fun x ↦ F ((0 : unitInterval), x))
        (contMDiff_familySlice F hF 0) e₀ (hfix 0) hpres :=
  hp.basedFamilyLift_slice_eq_basedLift F hF e₀ hfix hle 0 hpres

/-- Final-slice specialization of `basedFamilyLift_slice_eq_basedLift`. -/
theorem basedFamilyLift_one_eq_basedLift (hp : SmoothCover IE IX n p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F) (e₀ : E)
    (hfix : ∀ t : unitInterval, F (t, p e₀) = p e₀)
    (hle : hp.FamilyLiftingCriterion F hF e₀ (hfix 0).symm)
    (hpres : hp.PreservesRecoveredSubgroup (fun x ↦ F ((1 : unitInterval), x))
      (contMDiff_familySlice F hF 1).continuous e₀ (hfix 1)) :
    (fun z ↦ hp.basedFamilyLift F hF e₀ hfix hle ((1 : unitInterval), z)) =
      hp.basedLift (fun x ↦ F ((1 : unitInterval), x))
        (contMDiff_familySlice F hF 1) e₀ (hfix 1) hpres :=
  hp.basedFamilyLift_slice_eq_basedLift F hF e₀ hfix hle 1 hpres

end SmoothCover

namespace RelativeDiffeotopy

variable {s : Set X}
  {f g : TauCeti.RelativeDiff (I := IX) X ∞ s}

/-- Every slice of a relative diffeotopy fixes every point of its relative set. -/
theorem apply_eq_of_mem (K : RelativeDiffeotopy s f g) {x : X} (hx : x ∈ s)
    (t : unitInterval) : K.toFun (t, x) = x := by
  obtain ⟨φ, hφ⟩ := K.slice t
  rw [hφ]
  exact TauCeti.RelativeDiff.apply_eq φ hx

/-- Product-domain lift existence specialized to a relative diffeotopy and a chosen total-space
point whose projection lies in the fixed relative set. -/
theorem existsUnique_basedLiftThrough (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (K : RelativeDiffeotopy s f g) (e₀ : E) (he₀ : p e₀ ∈ s)
    (hle : hp.FamilyLiftingCriterion K.toFun K.contMDiff_toFun e₀
      (K.apply_eq_of_mem he₀ 0).symm) :
    ∃! L : unitInterval × E → E,
      ContMDiff ((𝓡∂ 1).prod IE) IE ∞ L ∧
        L ((0 : unitInterval), e₀) = e₀ ∧
        p ∘ L = SmoothCover.familyAfterProjection K.toFun p :=
  hp.existsUnique_basedFamilyLift K.toFun K.contMDiff_toFun e₀
    (K.apply_eq_of_mem he₀) hle

/-- For a relative diffeotopy, the initial slice of the joint lift agrees with the canonical
based lift of the initial relative diffeomorphism. -/
theorem basedFamilyLift_zero_eq_initialBasedLift (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (K : RelativeDiffeotopy s f g) (e₀ : E) (he₀ : p e₀ ∈ s)
    (hle : hp.FamilyLiftingCriterion K.toFun K.contMDiff_toFun e₀
      (K.apply_eq_of_mem he₀ 0).symm)
    (hpres : hp.PreservesRecoveredSubgroup f.1 f.1.continuous e₀
      (TauCeti.RelativeDiff.apply_eq f he₀)) :
    (fun z ↦ hp.basedFamilyLift K.toFun K.contMDiff_toFun e₀
      (K.apply_eq_of_mem he₀) hle ((0 : unitInterval), z)) =
      hp.basedLift f.1 f.1.contMDiff e₀ (TauCeti.RelativeDiff.apply_eq f he₀) hpres := by
  apply hp.eq_basedLift f.1 f.1.contMDiff e₀ (TauCeti.RelativeDiff.apply_eq f he₀) hpres
  · exact hp.basedFamilyLift_slice_contMDiff K.toFun K.contMDiff_toFun e₀
      (K.apply_eq_of_mem he₀) hle 0
  · exact hp.basedFamilyLift_basepoint K.toFun K.contMDiff_toFun e₀
      (K.apply_eq_of_mem he₀) hle 0
  · funext z
    calc
      p (hp.basedFamilyLift K.toFun K.contMDiff_toFun e₀
          (K.apply_eq_of_mem he₀) hle ((0 : unitInterval), z)) =
          K.toFun ((0 : unitInterval), p z) :=
        hp.proj_basedFamilyLift K.toFun K.contMDiff_toFun e₀
          (K.apply_eq_of_mem he₀) hle 0 z
      _ = f.1 (p z) := K.zero (p z)

/-- For a relative diffeotopy, the final slice of the joint lift agrees with the canonical based
lift of the final relative diffeomorphism. -/
theorem basedFamilyLift_one_eq_finalBasedLift (hp : SmoothCover IE IX ∞ p)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (K : RelativeDiffeotopy s f g) (e₀ : E) (he₀ : p e₀ ∈ s)
    (hle : hp.FamilyLiftingCriterion K.toFun K.contMDiff_toFun e₀
      (K.apply_eq_of_mem he₀ 0).symm)
    (hpres : hp.PreservesRecoveredSubgroup g.1 g.1.continuous e₀
      (TauCeti.RelativeDiff.apply_eq g he₀)) :
    (fun z ↦ hp.basedFamilyLift K.toFun K.contMDiff_toFun e₀
      (K.apply_eq_of_mem he₀) hle ((1 : unitInterval), z)) =
      hp.basedLift g.1 g.1.contMDiff e₀ (TauCeti.RelativeDiff.apply_eq g he₀) hpres := by
  apply hp.eq_basedLift g.1 g.1.contMDiff e₀ (TauCeti.RelativeDiff.apply_eq g he₀) hpres
  · exact hp.basedFamilyLift_slice_contMDiff K.toFun K.contMDiff_toFun e₀
      (K.apply_eq_of_mem he₀) hle 1
  · exact hp.basedFamilyLift_basepoint K.toFun K.contMDiff_toFun e₀
      (K.apply_eq_of_mem he₀) hle 1
  · funext z
    calc
      p (hp.basedFamilyLift K.toFun K.contMDiff_toFun e₀
          (K.apply_eq_of_mem he₀) hle ((1 : unitInterval), z)) =
          K.toFun ((1 : unitInterval), p z) :=
        hp.proj_basedFamilyLift K.toFun K.contMDiff_toFun e₀
          (K.apply_eq_of_mem he₀) hle 1 z
      _ = g.1 (p z) := K.one (p z)

end RelativeDiffeotopy

end SplittingSpheres
