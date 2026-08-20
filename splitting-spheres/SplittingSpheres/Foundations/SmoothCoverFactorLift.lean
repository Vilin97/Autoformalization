/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothCoverMappingClassLift

/-!
# Naturality of canonical lifts along a factor of smooth covers

Let `pₘ : Eₘ → X` and `pₖ : Eₖ → X` be pointed smooth covers and let
`q : Eₘ → Eₖ` be a supplied smooth map over `X` which carries the selected point of `Eₘ` to
the selected point of `Eₖ`.  Whenever a base self-map has canonical based lifts through both
covers, uniqueness of lifting through `pₖ` gives

`q ∘ liftₘ = liftₖ ∘ q`.

No covering, local-diffeomorphism, injectivity, or surjectivity property of `q` is inferred in
this file.  In particular, an arbitrary such factor does not induce a homomorphism between the
two groups of total-space diffeomorphisms or their mapping-class groups.  The group-level result
below is therefore an equivariance law on a common subgroup of base diffeomorphisms, rather than
a fictitious homomorphism in the upstairs direction.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

universe uM uK uX uHM uHK uHX

variable {EM EK EX : Type*}
  [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [NormedAddCommGroup EK] [NormedSpace ℝ EK]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX]
variable {HM : Type uHM} [TopologicalSpace HM]
  {HK : Type uHK} [TopologicalSpace HK]
  {HX : Type uHX} [TopologicalSpace HX]
variable {IM : ModelWithCorners ℝ EM HM} {IK : ModelWithCorners ℝ EK HK}
  {IX : ModelWithCorners ℝ EX HX}
variable {Eₘ : Type uM} [TopologicalSpace Eₘ] [ChartedSpace HM Eₘ]
  {Eₖ : Type uK} [TopologicalSpace Eₖ] [ChartedSpace HK Eₖ]
  {X : Type uX} [TopologicalSpace X] [ChartedSpace HX X]
variable {n : ℕ∞ω} {pₘ : Eₘ → X} {pₖ : Eₖ → X} {q : Eₘ → Eₖ}

namespace SmoothCover

omit [TopologicalSpace Eₘ] [TopologicalSpace Eₖ] [TopologicalSpace X] in
/-- The selected points of two factored covers project to the same basepoint. -/
theorem factor_basepoint_eq (htriangle : pₖ ∘ q = pₘ) {eₘ : Eₘ} {eₖ : Eₖ}
    (hq_base : q eₘ = eₖ) :
    pₖ eₖ = pₘ eₘ := by
  calc
    pₖ eₖ = pₖ (q eₘ) := congrArg pₖ hq_base.symm
    _ = pₘ eₘ := congrFun htriangle eₘ

omit [TopologicalSpace Eₘ] [TopologicalSpace Eₖ] [TopologicalSpace X] in
/-- A fixed-point equation at the lower selected point transports across a pointed factor. -/
theorem factor_fixedPoint (htriangle : pₖ ∘ q = pₘ) {eₘ : Eₘ} {eₖ : Eₖ}
    (hq_base : q eₘ = eₖ) {f : X → X} (hfix : f (pₘ eₘ) = pₘ eₘ) :
    f (pₖ eₖ) = pₖ eₖ := by
  rw [factor_basepoint_eq htriangle hq_base]
  exact hfix

/-- Naturality of canonical based lifts along a supplied smooth pointed factor of covers.

Preservation of the recovered subgroup is required separately for the two covers.  It is not
deduced from the existence of `q`. -/
theorem factor_comp_basedLift
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK n q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (f : X → X) (hf : ContMDiff IX IX n f)
    (hfixₘ : f (pₘ eₘ) = pₘ eₘ)
    (hpresₘ : hₘ.PreservesRecoveredSubgroup f hf.continuous eₘ hfixₘ)
    (hpresₖ : hₖ.PreservesRecoveredSubgroup f hf.continuous eₖ
      (factor_fixedPoint htriangle hq_base hfixₘ)) :
    q ∘ hₘ.basedLift f hf eₘ hfixₘ hpresₘ =
      hₖ.basedLift f hf eₖ (factor_fixedPoint htriangle hq_base hfixₘ) hpresₖ ∘ q := by
  apply hₖ.isCoveringMap.eq_of_comp_eq
    (hq.comp (hₘ.basedLift_contMDiff f hf eₘ hfixₘ hpresₘ)).continuous
    ((hₖ.basedLift_contMDiff f hf eₖ
      (factor_fixedPoint htriangle hq_base hfixₘ) hpresₖ).comp hq).continuous
  · funext z
    change pₖ (q (hₘ.basedLift f hf eₘ hfixₘ hpresₘ z)) =
      pₖ (hₖ.basedLift f hf eₖ
        (factor_fixedPoint htriangle hq_base hfixₘ) hpresₖ (q z))
    calc
      pₖ (q (hₘ.basedLift f hf eₘ hfixₘ hpresₘ z)) =
          pₘ (hₘ.basedLift f hf eₘ hfixₘ hpresₘ z) :=
        congrFun htriangle (hₘ.basedLift f hf eₘ hfixₘ hpresₘ z)
      _ = f (pₘ z) := hₘ.proj_basedLift f hf eₘ z hfixₘ hpresₘ
      _ = f (pₖ (q z)) := congrArg f (congrFun htriangle z).symm
      _ = pₖ (hₖ.basedLift f hf eₖ
          (factor_fixedPoint htriangle hq_base hfixₘ) hpresₖ (q z)) :=
        (hₖ.proj_basedLift f hf eₖ (q z)
          (factor_fixedPoint htriangle hq_base hfixₘ) hpresₖ).symm
  · change q (hₘ.basedLift f hf eₘ hfixₘ hpresₘ eₘ) =
      hₖ.basedLift f hf eₖ
        (factor_fixedPoint htriangle hq_base hfixₘ) hpresₖ (q eₘ)
    rw [hₘ.basedLift_basepoint, hq_base, hₖ.basedLift_basepoint]

/-- Pointwise form of `factor_comp_basedLift`. -/
theorem factor_basedLift_apply
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK n q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (f : X → X) (hf : ContMDiff IX IX n f)
    (hfixₘ : f (pₘ eₘ) = pₘ eₘ)
    (hpresₘ : hₘ.PreservesRecoveredSubgroup f hf.continuous eₘ hfixₘ)
    (hpresₖ : hₖ.PreservesRecoveredSubgroup f hf.continuous eₖ
      (factor_fixedPoint htriangle hq_base hfixₘ)) (z : Eₘ) :
    q (hₘ.basedLift f hf eₘ hfixₘ hpresₘ z) =
      hₖ.basedLift f hf eₖ (factor_fixedPoint htriangle hq_base hfixₘ) hpresₖ (q z) :=
  congrFun (factor_comp_basedLift hₘ hₖ hq htriangle eₘ eₖ hq_base
    f hf hfixₘ hpresₘ hpresₖ) z

/-- Naturality for the bundled lifted diffeomorphisms.  Forward and inverse preservation are
assumptions for each cover; no preservation statement is transported through `q`. -/
theorem factor_basedLiftDiffeomorph_apply
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK n q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (f : X ≃ₘ^n⟮IX, IX⟯ X)
    (hfixₘ : f (pₘ eₘ) = pₘ eₘ)
    (hfixInvₘ : f.symm (pₘ eₘ) = pₘ eₘ)
    (hpresₘ : hₘ.PreservesRecoveredSubgroup f f.continuous eₘ hfixₘ)
    (hpresInvₘ : hₘ.PreservesRecoveredSubgroup f.symm f.symm.continuous eₘ hfixInvₘ)
    (hpresₖ : hₖ.PreservesRecoveredSubgroup f f.continuous eₖ
      (factor_fixedPoint htriangle hq_base hfixₘ))
    (hpresInvₖ : hₖ.PreservesRecoveredSubgroup f.symm f.symm.continuous eₖ
      (factor_fixedPoint htriangle hq_base hfixInvₘ)) (z : Eₘ) :
    q (hₘ.basedLiftDiffeomorph f eₘ hfixₘ hfixInvₘ hpresₘ hpresInvₘ z) =
      hₖ.basedLiftDiffeomorph f eₖ
        (factor_fixedPoint htriangle hq_base hfixₘ)
        (factor_fixedPoint htriangle hq_base hfixInvₘ)
        hpresₖ hpresInvₖ (q z) := by
  rw [hₘ.basedLiftDiffeomorph_apply, hₖ.basedLiftDiffeomorph_apply]
  exact hₘ.factor_basedLift_apply hₖ hq htriangle eₘ eₖ hq_base
    f f.contMDiff hfixₘ hpresₘ hpresₖ z

/-- The inverse lifted diffeomorphisms obey the same factor-naturality equation. -/
theorem factor_basedLiftDiffeomorph_symm_apply
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK n q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (f : X ≃ₘ^n⟮IX, IX⟯ X)
    (hfixₘ : f (pₘ eₘ) = pₘ eₘ)
    (hfixInvₘ : f.symm (pₘ eₘ) = pₘ eₘ)
    (hpresₘ : hₘ.PreservesRecoveredSubgroup f f.continuous eₘ hfixₘ)
    (hpresInvₘ : hₘ.PreservesRecoveredSubgroup f.symm f.symm.continuous eₘ hfixInvₘ)
    (hpresₖ : hₖ.PreservesRecoveredSubgroup f f.continuous eₖ
      (factor_fixedPoint htriangle hq_base hfixₘ))
    (hpresInvₖ : hₖ.PreservesRecoveredSubgroup f.symm f.symm.continuous eₖ
      (factor_fixedPoint htriangle hq_base hfixInvₘ)) (z : Eₘ) :
    q ((hₘ.basedLiftDiffeomorph f eₘ hfixₘ hfixInvₘ hpresₘ hpresInvₘ).symm z) =
      (hₖ.basedLiftDiffeomorph f eₖ
        (factor_fixedPoint htriangle hq_base hfixₘ)
        (factor_fixedPoint htriangle hq_base hfixInvₘ)
        hpresₖ hpresInvₖ).symm (q z) := by
  rw [hₘ.basedLiftDiffeomorph_symm_apply, hₖ.basedLiftDiffeomorph_symm_apply]
  exact hₘ.factor_basedLift_apply hₖ hq htriangle eₘ eₖ hq_base
    f.symm f.symm.contMDiff hfixInvₘ hpresInvₘ hpresInvₖ z

/-- Base diffeomorphisms which are two-sided liftable through both pointed covers. -/
def commonTwoSidedLiftableSubgroup
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) : Subgroup (X ≃ₘ^n⟮IX, IX⟯ X) :=
  hₘ.twoSidedLiftableSubgroup eₘ ⊓ hₖ.twoSidedLiftableSubgroup eₖ

/-- Forget a common-liftability witness to the witness for the first cover. -/
def commonLiftableToFirst
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ →*
      hₘ.twoSidedLiftableSubgroup eₘ where
  toFun f := ⟨f.1, f.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Forget a common-liftability witness to the witness for the second cover. -/
def commonLiftableToSecond
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ →*
      hₖ.twoSidedLiftableSubgroup eₖ where
  toFun f := ⟨f.1, f.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Canonical lifting through the first cover, restricted to the common liftable subgroup. -/
noncomputable def commonLiftableDiffeomorphLiftHomFirst
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ →*
      TauCeti.RelativeDiff (I := IM) Eₘ n ({eₘ} : Set Eₘ) :=
  (hₘ.liftableDiffeomorphLiftHom eₘ).comp
    (hₘ.commonLiftableToFirst hₖ eₘ eₖ)

/-- Canonical lifting through the second cover, restricted to the common liftable subgroup. -/
noncomputable def commonLiftableDiffeomorphLiftHomSecond
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ →*
      TauCeti.RelativeDiff (I := IK) Eₖ n ({eₖ} : Set Eₖ) :=
  (hₖ.liftableDiffeomorphLiftHom eₖ).comp
    (hₘ.commonLiftableToSecond hₖ eₘ eₖ)

/-- Application formula for the common lift homomorphism through the first cover. -/
@[simp]
theorem commonLiftableDiffeomorphLiftHomFirst_apply
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ)
    (f : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) (z : Eₘ) :
    (hₘ.commonLiftableDiffeomorphLiftHomFirst hₖ eₘ eₖ f).1 z =
      (hₘ.liftableDiffeomorphLiftHom eₘ
        (hₘ.commonLiftableToFirst hₖ eₘ eₖ f)).1 z :=
  rfl

/-- Application formula for the common lift homomorphism through the second cover. -/
@[simp]
theorem commonLiftableDiffeomorphLiftHomSecond_apply
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ)
    (f : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) (z : Eₖ) :
    (hₘ.commonLiftableDiffeomorphLiftHomSecond hₖ eₘ eₖ f).1 z =
      (hₖ.liftableDiffeomorphLiftHom eₖ
        (hₘ.commonLiftableToSecond hₖ eₘ eₖ f)).1 z :=
  rfl

/-- On the common two-sided-liftable subgroup, the two canonical lift homomorphisms are
`q`-equivariant.  This is the correct group-level statement when `q` is only a smooth factor
map, rather than a diffeomorphism. -/
theorem factor_liftableDiffeomorphLiftHom_apply
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK n q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (f : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) (z : Eₘ) :
    q ((hₘ.liftableDiffeomorphLiftHom eₘ
      (hₘ.commonLiftableToFirst hₖ eₘ eₖ f)).1 z) =
      (hₖ.liftableDiffeomorphLiftHom eₖ
        (hₘ.commonLiftableToSecond hₖ eₘ eₖ f)).1 (q z) := by
  let fₘ := hₘ.commonLiftableToFirst hₖ eₘ eₖ f
  let fₖ := hₘ.commonLiftableToSecond hₖ eₘ eₖ f
  change q (hₘ.basedLift f.1 f.1.contMDiff eₘ
      (hₘ.twoSidedLiftable_fixed eₘ fₘ)
      (hₘ.twoSidedLiftable_preserves eₘ fₘ) z) =
    hₖ.basedLift f.1 f.1.contMDiff eₖ
      (hₖ.twoSidedLiftable_fixed eₖ fₖ)
      (hₖ.twoSidedLiftable_preserves eₖ fₖ) (q z)
  exact hₘ.factor_basedLift_apply hₖ hq htriangle eₘ eₖ hq_base
    f.1 f.1.contMDiff (hₘ.twoSidedLiftable_fixed eₘ fₘ)
    (hₘ.twoSidedLiftable_preserves eₘ fₘ)
    (hₖ.twoSidedLiftable_preserves eₖ fₖ) z

/-- Inverse law corresponding to `factor_liftableDiffeomorphLiftHom_apply`. -/
theorem factor_liftableDiffeomorphLiftHom_inv_apply
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK n q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (f : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) (z : Eₘ) :
    q (((hₘ.liftableDiffeomorphLiftHom eₘ
      (hₘ.commonLiftableToFirst hₖ eₘ eₖ f)).1).symm z) =
      ((hₖ.liftableDiffeomorphLiftHom eₖ
        (hₘ.commonLiftableToSecond hₖ eₘ eₖ f)).1).symm (q z) := by
  let fₘ := hₘ.commonLiftableToFirst hₖ eₘ eₖ f
  let fₖ := hₘ.commonLiftableToSecond hₖ eₘ eₖ f
  change q (hₘ.basedLift f.1.symm f.1.symm.contMDiff eₘ
      (fixedPoint_symm_diffeomorph f.1 (hₘ.twoSidedLiftable_fixed eₘ fₘ))
      (hₘ.twoSidedLiftable_preserves_symm eₘ fₘ) z) =
    hₖ.basedLift f.1.symm f.1.symm.contMDiff eₖ
      (fixedPoint_symm_diffeomorph f.1 (hₖ.twoSidedLiftable_fixed eₖ fₖ))
      (hₖ.twoSidedLiftable_preserves_symm eₖ fₖ) (q z)
  exact hₘ.factor_basedLift_apply hₖ hq htriangle eₘ eₖ hq_base
    f.1.symm f.1.symm.contMDiff
    (fixedPoint_symm_diffeomorph f.1 (hₘ.twoSidedLiftable_fixed eₘ fₘ))
    (hₘ.twoSidedLiftable_preserves_symm eₘ fₘ)
    (hₖ.twoSidedLiftable_preserves_symm eₖ fₖ) z

/-- Equivariance in terms of the two lift homomorphisms already restricted to the common
subgroup. -/
theorem factor_commonLiftableDiffeomorphLiftHom_apply
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK n q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (f : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) (z : Eₘ) :
    q ((hₘ.commonLiftableDiffeomorphLiftHomFirst hₖ eₘ eₖ f).1 z) =
      (hₘ.commonLiftableDiffeomorphLiftHomSecond hₖ eₘ eₖ f).1 (q z) :=
  factor_liftableDiffeomorphLiftHom_apply hₘ hₖ hq htriangle eₘ eₖ hq_base f z

/-- The product-domain map induced by a factor on the total-space coordinate. -/
def factorFamilyDomain (q : Eₘ → Eₖ) : unitInterval × Eₘ → unitInterval × Eₖ :=
  fun z ↦ (z.1, q z.2)

/-- A smooth factor induces a jointly smooth map on the time/total-space product. -/
theorem contMDiff_factorFamilyDomain (hq : ContMDiff IM IK n q) :
    ContMDiff ((𝓡∂ 1).prod IM) ((𝓡∂ 1).prod IK) n (factorFamilyDomain q) :=
  contMDiff_fst.prodMk (hq.comp contMDiff_snd)

omit [TopologicalSpace Eₘ] [TopologicalSpace Eₖ] [TopologicalSpace X] in
/-- Fixedness of a base family transports across the equality of the two projected selected
points. -/
theorem factor_family_fixed (htriangle : pₖ ∘ q = pₘ) {eₘ : Eₘ} {eₖ : Eₖ}
    (hq_base : q eₘ = eₖ) {F : unitInterval × X → X}
    (hfix : ∀ t, F (t, pₘ eₘ) = pₘ eₘ) :
    ∀ t, F (t, pₖ eₖ) = pₖ eₖ := by
  intro t
  rw [factor_basepoint_eq htriangle hq_base]
  exact hfix t

/-- Naturality of canonical jointly smooth family lifts along a smooth pointed factor.

The product lifting criterion is supplied independently for each cover.  In particular, this
theorem does not claim that a slice-wise preservation hypothesis implies a product lift. -/
theorem factor_comp_basedFamilyLift
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK n q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F)
    (hfixₘ : ∀ t, F (t, pₘ eₘ) = pₘ eₘ)
    (hleₘ : hₘ.FamilyLiftingCriterion F hF eₘ (hfixₘ 0).symm)
    (hleₖ : hₖ.FamilyLiftingCriterion F hF eₖ
      ((factor_family_fixed htriangle hq_base hfixₘ) 0).symm) :
    q ∘ hₘ.basedFamilyLift F hF eₘ hfixₘ hleₘ =
      hₖ.basedFamilyLift F hF eₖ
        (factor_family_fixed htriangle hq_base hfixₘ) hleₖ ∘ factorFamilyDomain q := by
  let _ : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace ℝ
  let _ : PathConnectedSpace unitInterval :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  apply hₖ.isCoveringMap.eq_of_comp_eq
    (hq.comp (hₘ.basedFamilyLift_contMDiff F hF eₘ hfixₘ hleₘ)).continuous
    ((hₖ.basedFamilyLift_contMDiff F hF eₖ
      (factor_family_fixed htriangle hq_base hfixₘ) hleₖ).comp
      (contMDiff_factorFamilyDomain hq)).continuous
  · funext z
    change pₖ (q (hₘ.basedFamilyLift F hF eₘ hfixₘ hleₘ z)) =
      pₖ (hₖ.basedFamilyLift F hF eₖ
        (factor_family_fixed htriangle hq_base hfixₘ) hleₖ (z.1, q z.2))
    calc
      pₖ (q (hₘ.basedFamilyLift F hF eₘ hfixₘ hleₘ z)) =
          pₘ (hₘ.basedFamilyLift F hF eₘ hfixₘ hleₘ z) :=
        congrFun htriangle (hₘ.basedFamilyLift F hF eₘ hfixₘ hleₘ z)
      _ = F (z.1, pₘ z.2) := hₘ.proj_basedFamilyLift F hF eₘ hfixₘ hleₘ z.1 z.2
      _ = F (z.1, pₖ (q z.2)) := congrArg (fun x ↦ F (z.1, x)) (congrFun htriangle z.2).symm
      _ = pₖ (hₖ.basedFamilyLift F hF eₖ
          (factor_family_fixed htriangle hq_base hfixₘ) hleₖ (z.1, q z.2)) :=
        (hₖ.proj_basedFamilyLift F hF eₖ
          (factor_family_fixed htriangle hq_base hfixₘ) hleₖ z.1 (q z.2)).symm
  · change q (hₘ.basedFamilyLift F hF eₘ hfixₘ hleₘ ((0 : unitInterval), eₘ)) =
      hₖ.basedFamilyLift F hF eₖ
        (factor_family_fixed htriangle hq_base hfixₘ) hleₖ
        ((0 : unitInterval), q eₘ)
    rw [hₘ.basedFamilyLift_zero_basepoint, hq_base,
      hₖ.basedFamilyLift_zero_basepoint]

/-- Pointwise form of `factor_comp_basedFamilyLift`. -/
theorem factor_basedFamilyLift_apply
    (hₘ : SmoothCover IM IX n pₘ) (hₖ : SmoothCover IK IX n pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK n q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (F : unitInterval × X → X)
    (hF : ContMDiff ((𝓡∂ 1).prod IX) IX n F)
    (hfixₘ : ∀ t, F (t, pₘ eₘ) = pₘ eₘ)
    (hleₘ : hₘ.FamilyLiftingCriterion F hF eₘ (hfixₘ 0).symm)
    (hleₖ : hₖ.FamilyLiftingCriterion F hF eₖ
      ((factor_family_fixed htriangle hq_base hfixₘ) 0).symm)
    (t : unitInterval) (z : Eₘ) :
    q (hₘ.basedFamilyLift F hF eₘ hfixₘ hleₘ (t, z)) =
      hₖ.basedFamilyLift F hF eₖ
        (factor_family_fixed htriangle hq_base hfixₘ) hleₖ (t, q z) :=
  congrFun (factor_comp_basedFamilyLift hₘ hₖ hq htriangle eₘ eₖ hq_base
    F hF hfixₘ hleₘ hleₖ) (t, z)

/-- Two independently certified liftable diffeotopies with the same base family have
`q`-compatible lifted diffeotopies.

This is the factor-compatibility statement available at the certified mapping-class layer.  It
compares the actual relative-diffeomorphism representatives and their isotopies.  Since a
general smooth `q` cannot push forward arbitrary diffeomorphisms, it deliberately does not claim
that `q` induces a homomorphism between the two upstairs mapping-class groups. -/
theorem factor_comp_certifiedDiffeotopyLift
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK ∞ q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (f g : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ)
    (Kₘ : hₘ.TwoSidedLiftableDiffeotopy eₘ
      (hₘ.commonLiftableToFirst hₖ eₘ eₖ f)
      (hₘ.commonLiftableToFirst hₖ eₘ eₖ g))
    (Kₖ : hₖ.TwoSidedLiftableDiffeotopy eₖ
      (hₘ.commonLiftableToSecond hₖ eₘ eₖ f)
      (hₘ.commonLiftableToSecond hₖ eₘ eₖ g))
    (hfamily : ∀ t, Kₘ.family t = Kₖ.family t) :
    q ∘ (Kₘ.lift hₘ eₘ).toFun =
      (Kₖ.lift hₖ eₖ).toFun ∘ factorFamilyDomain q := by
  let _ : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace ℝ
  let _ : PathConnectedSpace unitInterval :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  apply hₖ.isCoveringMap.eq_of_comp_eq
    (hq.comp (Kₘ.lift hₘ eₘ).contMDiff_toFun).continuous
    ((Kₖ.lift hₖ eₖ).contMDiff_toFun.comp (contMDiff_factorFamilyDomain hq)).continuous
  · funext z
    change pₖ (q (hₘ.basedFamilyLift (diffeomorphismFamilyEval Kₘ.family)
        Kₘ.contMDiff_eval eₘ Kₘ.fixed Kₘ.liftingCriterion z)) =
      pₖ (hₖ.basedFamilyLift (diffeomorphismFamilyEval Kₖ.family)
        Kₖ.contMDiff_eval eₖ Kₖ.fixed Kₖ.liftingCriterion (z.1, q z.2))
    calc
      pₖ (q (hₘ.basedFamilyLift (diffeomorphismFamilyEval Kₘ.family)
          Kₘ.contMDiff_eval eₘ Kₘ.fixed Kₘ.liftingCriterion z)) =
          pₘ (hₘ.basedFamilyLift (diffeomorphismFamilyEval Kₘ.family)
            Kₘ.contMDiff_eval eₘ Kₘ.fixed Kₘ.liftingCriterion z) :=
        congrFun htriangle (hₘ.basedFamilyLift (diffeomorphismFamilyEval Kₘ.family)
          Kₘ.contMDiff_eval eₘ Kₘ.fixed Kₘ.liftingCriterion z)
      _ = Kₘ.family z.1 (pₘ z.2) :=
        hₘ.proj_basedFamilyLift (diffeomorphismFamilyEval Kₘ.family)
          Kₘ.contMDiff_eval eₘ Kₘ.fixed Kₘ.liftingCriterion z.1 z.2
      _ = Kₖ.family z.1 (pₖ (q z.2)) := by
        rw [hfamily z.1]
        exact congrArg (Kₖ.family z.1)
          (by simpa only [Function.comp_apply] using (congrFun htriangle z.2).symm)
      _ = pₖ (hₖ.basedFamilyLift (diffeomorphismFamilyEval Kₖ.family)
          Kₖ.contMDiff_eval eₖ Kₖ.fixed Kₖ.liftingCriterion (z.1, q z.2)) :=
        (hₖ.proj_basedFamilyLift (diffeomorphismFamilyEval Kₖ.family)
          Kₖ.contMDiff_eval eₖ Kₖ.fixed Kₖ.liftingCriterion z.1 (q z.2)).symm
  · calc
      q ((Kₘ.lift hₘ eₘ).toFun ((0 : unitInterval), eₘ)) =
          q ((hₘ.liftableDiffeomorphLiftHom eₘ
            (hₘ.commonLiftableToFirst hₖ eₘ eₖ f)).1 eₘ) :=
        congrArg q ((Kₘ.lift hₘ eₘ).zero eₘ)
      _ = q eₘ := congrArg q (hₘ.liftableDiffeomorphLift_basepoint eₘ
        (hₘ.commonLiftableToFirst hₖ eₘ eₖ f))
      _ = eₖ := hq_base
      _ = (hₖ.liftableDiffeomorphLiftHom eₖ
          (hₘ.commonLiftableToSecond hₖ eₘ eₖ f)).1 eₖ :=
        (hₖ.liftableDiffeomorphLift_basepoint eₖ
          (hₘ.commonLiftableToSecond hₖ eₘ eₖ f)).symm
      _ = (Kₖ.lift hₖ eₖ).toFun ((0 : unitInterval), q eₘ) := by
        rw [hq_base]
        exact ((Kₖ.lift hₖ eₖ).zero eₖ).symm

/-- Pointwise form of compatibility for certified lifted diffeotopies. -/
theorem factor_certifiedDiffeotopyLift_apply
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (hq : ContMDiff IM IK ∞ q) (htriangle : pₖ ∘ q = pₘ)
    (eₘ : Eₘ) (eₖ : Eₖ) (hq_base : q eₘ = eₖ)
    (f g : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ)
    (Kₘ : hₘ.TwoSidedLiftableDiffeotopy eₘ
      (hₘ.commonLiftableToFirst hₖ eₘ eₖ f)
      (hₘ.commonLiftableToFirst hₖ eₘ eₖ g))
    (Kₖ : hₖ.TwoSidedLiftableDiffeotopy eₖ
      (hₘ.commonLiftableToSecond hₖ eₘ eₖ f)
      (hₘ.commonLiftableToSecond hₖ eₘ eₖ g))
    (hfamily : ∀ t, Kₘ.family t = Kₖ.family t)
    (t : unitInterval) (z : Eₘ) :
    q ((Kₘ.lift hₘ eₘ).toFun (t, z)) =
      (Kₖ.lift hₖ eₖ).toFun (t, q z) :=
  congrFun (factor_comp_certifiedDiffeotopyLift hₘ hₖ hq htriangle
    eₘ eₖ hq_base f g Kₘ Kₖ hfamily) (t, z)

/-- A single certificate that a diffeotopy is liftable through both covers and that the two
certificates use the same base family.  The two product lifting criteria and all-time two-sided
preservation hypotheses remain explicit inside the two constituent certificates. -/
structure FactorCompatibleDiffeotopy
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ)
    (f g : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) where
  /-- The full lifting certificate through the first cover. -/
  first : hₘ.TwoSidedLiftableDiffeotopy eₘ
    (hₘ.commonLiftableToFirst hₖ eₘ eₖ f)
    (hₘ.commonLiftableToFirst hₖ eₘ eₖ g)
  /-- The full lifting certificate through the second cover. -/
  second : hₖ.TwoSidedLiftableDiffeotopy eₖ
    (hₘ.commonLiftableToSecond hₖ eₘ eₖ f)
    (hₘ.commonLiftableToSecond hₖ eₘ eₖ g)
  /-- Both certificates describe exactly the same family downstairs. -/
  family_eq : ∀ t, first.family t = second.family t

namespace FactorCompatibleDiffeotopy

variable (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
  [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
  [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
  (eₘ : Eₘ) (eₖ : Eₖ)
  {f g : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ}

/-- The two lifted diffeotopies associated to a factor-compatible certificate commute with the
factor map at every time. -/
theorem lift_apply (hq : ContMDiff IM IK ∞ q) (htriangle : pₖ ∘ q = pₘ)
    (hq_base : q eₘ = eₖ) (K : hₘ.FactorCompatibleDiffeotopy hₖ eₘ eₖ f g)
    (t : unitInterval) (z : Eₘ) :
    q ((K.first.lift hₘ eₘ).toFun (t, z)) =
      (K.second.lift hₖ eₖ).toFun (t, q z) :=
  factor_certifiedDiffeotopyLift_apply hₘ hₖ hq htriangle eₘ eₖ hq_base
    f g K.first K.second K.family_eq t z

end FactorCompatibleDiffeotopy

/-- Endpoint differences of diffeotopies carrying compatible lifting certificates for both
covers.  This is intentionally narrower than either cover's independently certified relation. -/
def factorCompatibleDiffeotopyRelators
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    Set (hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) :=
  {r | ∃ f g, Nonempty (hₘ.FactorCompatibleDiffeotopy hₖ eₘ eₖ f g) ∧ r = f / g}

/-- The normal closure of the factor-compatible certified diffeotopy relators. -/
def factorCompatibleDiffeotopyNormal
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    Subgroup (hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) :=
  Subgroup.normalClosure (hₘ.factorCompatibleDiffeotopyRelators hₖ eₘ eₖ)

instance factorCompatibleDiffeotopyNormal_normal
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    (hₘ.factorCompatibleDiffeotopyNormal hₖ eₘ eₖ).Normal :=
  Subgroup.normalClosure_normal

/-- The common source mapping-class group obtained by imposing only diffeotopies certified
compatibly for both covers. -/
abbrev FactorCompatibleMappingClass
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :=
  hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ ⧸
    hₘ.factorCompatibleDiffeotopyNormal hₖ eₘ eₖ

/-- Canonical class of a common two-sided-liftable base diffeomorphism. -/
def factorCompatibleMappingClassMk
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ →*
      hₘ.FactorCompatibleMappingClass hₖ eₘ eₖ :=
  QuotientGroup.mk' (hₘ.factorCompatibleDiffeotopyNormal hₖ eₘ eₖ)

/-- The first canonical lift homomorphism sends factor-compatible relators to genuine relative
diffeotopy relators upstairs. -/
theorem commonLiftHomFirst_maps_factorCompatibleRelators
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    MapsTo (hₘ.commonLiftableDiffeomorphLiftHomFirst hₖ eₘ eₖ)
      (hₘ.factorCompatibleDiffeotopyRelators hₖ eₘ eₖ)
      (relativeDiffeotopyRelators (IM := IM) ({eₘ} : Set Eₘ)) := by
  rintro r ⟨f, g, ⟨K⟩, rfl⟩
  refine ⟨hₘ.commonLiftableDiffeomorphLiftHomFirst hₖ eₘ eₖ f,
    hₘ.commonLiftableDiffeomorphLiftHomFirst hₖ eₘ eₖ g, ?_, ?_⟩
  · refine ⟨?_⟩
    exact K.first.lift hₘ eₘ
  · exact map_div (hₘ.commonLiftableDiffeomorphLiftHomFirst hₖ eₘ eₖ) f g

/-- The second canonical lift homomorphism sends factor-compatible relators to genuine relative
diffeotopy relators upstairs. -/
theorem commonLiftHomSecond_maps_factorCompatibleRelators
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    MapsTo (hₘ.commonLiftableDiffeomorphLiftHomSecond hₖ eₘ eₖ)
      (hₘ.factorCompatibleDiffeotopyRelators hₖ eₘ eₖ)
      (relativeDiffeotopyRelators (IM := IK) ({eₖ} : Set Eₖ)) := by
  rintro r ⟨f, g, ⟨K⟩, rfl⟩
  refine ⟨hₘ.commonLiftableDiffeomorphLiftHomSecond hₖ eₘ eₖ f,
    hₘ.commonLiftableDiffeomorphLiftHomSecond hₖ eₘ eₖ g, ?_, ?_⟩
  · refine ⟨?_⟩
    exact K.second.lift hₖ eₖ
  · exact map_div (hₘ.commonLiftableDiffeomorphLiftHomSecond hₖ eₘ eₖ) f g

/-- The common certified normal subgroup lies in the preimage of the first upstairs
diffeotopy-normal subgroup. -/
theorem factorCompatibleNormal_le_comap_first
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.factorCompatibleDiffeotopyNormal hₖ eₘ eₖ ≤
      (relativeDiffeotopyNormal (IM := IM) ({eₘ} : Set Eₘ)).comap
        (hₘ.commonLiftableDiffeomorphLiftHomFirst hₖ eₘ eₖ) := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact Subgroup.subset_normalClosure
    (hₘ.commonLiftHomFirst_maps_factorCompatibleRelators hₖ eₘ eₖ hr)

/-- The common certified normal subgroup lies in the preimage of the second upstairs
diffeotopy-normal subgroup. -/
theorem factorCompatibleNormal_le_comap_second
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.factorCompatibleDiffeotopyNormal hₖ eₘ eₖ ≤
      (relativeDiffeotopyNormal (IM := IK) ({eₖ} : Set Eₖ)).comap
        (hₘ.commonLiftableDiffeomorphLiftHomSecond hₖ eₘ eₖ) := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact Subgroup.subset_normalClosure
    (hₘ.commonLiftHomSecond_maps_factorCompatibleRelators hₖ eₘ eₖ hr)

/-- Canonical lifting through the first cover descended from the common certified source
mapping-class group. -/
noncomputable def factorCompatibleMappingClassLiftFirst
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.FactorCompatibleMappingClass hₖ eₘ eₖ →*
      RelativeMappingClass (IM := IM) ({eₘ} : Set Eₘ) :=
  QuotientGroup.map (hₘ.factorCompatibleDiffeotopyNormal hₖ eₘ eₖ)
    (relativeDiffeotopyNormal (IM := IM) ({eₘ} : Set Eₘ))
    (hₘ.commonLiftableDiffeomorphLiftHomFirst hₖ eₘ eₖ)
    (hₘ.factorCompatibleNormal_le_comap_first hₖ eₘ eₖ)

/-- Canonical lifting through the second cover descended from the common certified source
mapping-class group. -/
noncomputable def factorCompatibleMappingClassLiftSecond
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.FactorCompatibleMappingClass hₖ eₘ eₖ →*
      RelativeMappingClass (IM := IK) ({eₖ} : Set Eₖ) :=
  QuotientGroup.map (hₘ.factorCompatibleDiffeotopyNormal hₖ eₘ eₖ)
    (relativeDiffeotopyNormal (IM := IK) ({eₖ} : Set Eₖ))
    (hₘ.commonLiftableDiffeomorphLiftHomSecond hₖ eₘ eₖ)
    (hₘ.factorCompatibleNormal_le_comap_second hₖ eₘ eₖ)

/-- Representative formula for the first quotient-level canonical lift. -/
@[simp]
theorem factorCompatibleMappingClassLiftFirst_mk
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ)
    (f : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) :
    hₘ.factorCompatibleMappingClassLiftFirst hₖ eₘ eₖ
        (hₘ.factorCompatibleMappingClassMk hₖ eₘ eₖ f) =
      relativeMappingClassMk (IM := IM) ({eₘ} : Set Eₘ)
        (hₘ.commonLiftableDiffeomorphLiftHomFirst hₖ eₘ eₖ f) :=
  QuotientGroup.map_mk' _ _ _ _ f

/-- Representative formula for the second quotient-level canonical lift. -/
@[simp]
theorem factorCompatibleMappingClassLiftSecond_mk
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ)
    (f : hₘ.commonTwoSidedLiftableSubgroup hₖ eₘ eₖ) :
    hₘ.factorCompatibleMappingClassLiftSecond hₖ eₘ eₖ
        (hₘ.factorCompatibleMappingClassMk hₖ eₘ eₖ f) =
      relativeMappingClassMk (IM := IK) ({eₖ} : Set Eₖ)
        (hₘ.commonLiftableDiffeomorphLiftHomSecond hₖ eₘ eₖ f) :=
  QuotientGroup.map_mk' _ _ _ _ f

/-- Both quotient-level lift homomorphisms preserve the identity class. -/
@[simp]
theorem factorCompatibleMappingClassLifts_one
    (hₘ : SmoothCover IM IX ∞ pₘ) (hₖ : SmoothCover IK IX ∞ pₖ)
    [PathConnectedSpace Eₘ] [LocallyPathConnectedSpace Eₘ]
    [PathConnectedSpace Eₖ] [LocallyPathConnectedSpace Eₖ]
    (eₘ : Eₘ) (eₖ : Eₖ) :
    hₘ.factorCompatibleMappingClassLiftFirst hₖ eₘ eₖ 1 = 1 ∧
      hₘ.factorCompatibleMappingClassLiftSecond hₖ eₘ eₖ 1 = 1 :=
  ⟨map_one _, map_one _⟩

end SmoothCover

end SplittingSpheres
