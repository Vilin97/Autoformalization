/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SplittingSpheres.Foundations.SmoothEmbeddingRange
public import SplittingSpheres.Foundations.SmoothIsotopy

/-!
# Smooth concatenation of embedding isotopies

Two jointly smooth isotopies whose adjoining endpoint maps agree can be concatenated without
losing smoothness.  We reparametrize the first track so it is already constant for the middle
half of the interval and the second so it is still constant there.  Thus the two smooth formulas
agree on a neighborhood of the cutting hypersurface, where `ContMDiff.piecewise` applies.

The endpoint-map equality is intentionally explicit.  The frozen isotopy relation records only
endpoint ranges; converting equal embedded ranges into a smooth source reparametrization is a
separate geometric theorem.
-/

@[expose] public section

open Function Metric Set
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace unitInterval

/-- Smooth time change for the first half of a concatenated isotopy.  It reaches `1` by time
`1/4` and stays there. -/
def concatLeftTime (t : I) : I :=
  ⟨Real.smoothTransition (4 * (t : ℝ)),
    Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- Smooth time change for the second half of a concatenated isotopy.  It stays at `0` through
time `3/4` and then reaches `1`. -/
def concatRightTime (t : I) : I :=
  ⟨Real.smoothTransition (4 * (t : ℝ) - 3),
    Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem contMDiff_concatLeftTime :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ concatLeftTime := by
  let L : ℝ →L[ℝ] ℝ := (4 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hsub : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : I ↦ (t : ℝ)) :=
    contMDiff_subtypeVal_Icc
  have harg : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : I ↦ 4 * (t : ℝ)) := by
    convert L.contMDiff.comp hsub using 1
    funext t
    simp [L]
  have hval : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun t : I ↦ Real.smoothTransition (4 * (t : ℝ))) :=
    Real.smoothTransition.contDiff.contMDiff.comp harg
  rw [contMDiff_iff_comp_subtypeVal_Icc]
  exact ⟨hval.continuous.subtype_mk _, hval⟩

theorem contMDiff_concatRightTime :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ concatRightTime := by
  let L : ℝ →L[ℝ] ℝ := (4 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hsub : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : I ↦ (t : ℝ)) :=
    contMDiff_subtypeVal_Icc
  have hmul : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : I ↦ 4 * (t : ℝ)) := by
    convert L.contMDiff.comp hsub using 1
    funext t
    simp [L]
  have harg : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : I ↦ 4 * (t : ℝ) - 3) :=
    hmul.sub contMDiff_const
  have hval : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun t : I ↦ Real.smoothTransition (4 * (t : ℝ) - 3)) :=
    Real.smoothTransition.contDiff.contMDiff.comp harg
  rw [contMDiff_iff_comp_subtypeVal_Icc]
  exact ⟨hval.continuous.subtype_mk _, hval⟩

@[simp]
theorem concatLeftTime_zero : concatLeftTime 0 = 0 := by
  apply Subtype.ext
  simp [concatLeftTime]

@[simp]
theorem concatRightTime_one : concatRightTime 1 = 1 := by
  apply Subtype.ext
  norm_num [concatRightTime, Real.smoothTransition.one]

theorem concatLeftTime_eq_one {t : I} (ht : (1 / 4 : ℝ) < t) :
    concatLeftTime t = 1 := by
  apply Subtype.ext
  change Real.smoothTransition (4 * (t : ℝ)) = 1
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem concatRightTime_eq_zero {t : I} (ht : (t : ℝ) < 3 / 4) :
    concatRightTime t = 0 := by
  apply Subtype.ext
  change Real.smoothTransition (4 * (t : ℝ) - 3) = 0
  apply Real.smoothTransition.zero_of_nonpos
  linarith

end unitInterval

namespace SplittingSpheres

/-- Reparametrize the source of every slice of a sphere isotopy by a fixed diffeomorphism.  Since
the source map is onto, this changes no endpoint range. -/
def SmoothSphereIsotopy.precompDiffeomorph
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 3 ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ Sphere 3) :
    SmoothSphereIsotopy S₀ S₁ where
  toFun := fun p ↦ H.toFun (p.1, e p.2)
  contMDiff_toFun := H.contMDiff_toFun.comp
    (contMDiff_fst.prodMk (e.contMDiff.comp contMDiff_snd))
  isSmoothEmbedding_slice := fun t ↦
    (H.isSmoothEmbedding_slice t).precomp_diffeomorph e
  range_zero := by
    change range ((fun x ↦ H.toFun (0, x)) ∘ e) = range S₀
    have he : Surjective (fun x ↦ e x) := e.toEquiv.surjective
    exact (he.range_comp (fun x ↦ H.toFun (0, x))).trans H.range_zero
  range_one := by
    change range ((fun x ↦ H.toFun (1, x)) ∘ e) = range S₁
    have he : Surjective (fun x ↦ e x) := e.toEquiv.surjective
    exact (he.range_comp (fun x ↦ H.toFun (1, x))).trans H.range_one

/-- Source reparametrization preserves pointwise avoidance of the unlink. -/
theorem SmoothSphereIsotopy.precompDiffeomorph_avoids
    {S₀ S₁ : SmoothSphereEmbedding 3 4}
    (H : SmoothSphereIsotopy S₀ S₁)
    (e : Sphere 3 ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ Sphere 3)
    (hH : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ∀ p, (H.precompDiffeomorph e).toFun p ∉ standardUnlinkCarrier := by
  rintro ⟨t, x⟩
  exact hH (t, e x)

/-- Concatenate two smooth sphere isotopies when their adjoining endpoint maps agree pointwise.
The reparametrized tracks are constant on an overlapping time interval, so the pasted family is
jointly smooth. -/
def SmoothSphereIsotopy.transOfEndpointEq
    {S₀ S₁ S₂ : SmoothSphereEmbedding 3 4}
    (H₀ : SmoothSphereIsotopy S₀ S₁) (H₁ : SmoothSphereIsotopy S₁ S₂)
    (hmatch : (fun x ↦ H₀.toFun (1, x)) = fun x ↦ H₁.toFun (0, x)) :
    SmoothSphereIsotopy S₀ S₂ where
  toFun := fun p ↦ if (p.1 : ℝ) ≤ 1 / 2 then
      H₀.toFun (unitInterval.concatLeftTime p.1, p.2)
    else H₁.toFun (unitInterval.concatRightTime p.1, p.2)
  contMDiff_toFun := by
    classical
    let time : I × Sphere 3 → ℝ := fun p ↦ p.1
    let A : Set (I × Sphere 3) := time ⁻¹' Iic (1 / 2)
    let F : I × Sphere 3 → Sphere 4 := fun p ↦
      H₀.toFun (unitInterval.concatLeftTime p.1, p.2)
    let G : I × Sphere 3 → Sphere 4 := fun p ↦
      H₁.toFun (unitInterval.concatRightTime p.1, p.2)
    have htime : Continuous time := continuous_subtype_val.comp continuous_fst
    have hF : ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 4) ∞ F :=
      H₀.contMDiff_toFun.comp
        ((unitInterval.contMDiff_concatLeftTime.comp contMDiff_fst).prodMk contMDiff_snd)
    have hG : ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 4) ∞ G :=
      H₁.contMDiff_toFun.comp
        ((unitInterval.contMDiff_concatRightTime.comp contMDiff_fst).prodMk contMDiff_snd)
    have hpaste : ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 4) ∞
        (A.piecewise F G) := by
      apply hF.piecewise hG
      intro p hp
      have hfront : time p ∈ frontier (Iic (1 / 2 : ℝ)) :=
        htime.frontier_preimage_subset (Iic (1 / 2 : ℝ)) hp
      have htimep : time p = 1 / 2 := by
        exact mem_singleton_iff.mp (frontier_Iic_subset (1 / 2 : ℝ) hfront)
      have hpIoo : time p ∈ Ioo (1 / 4 : ℝ) (3 / 4 : ℝ) := by
        rw [htimep]
        norm_num
      filter_upwards [htime.continuousAt (isOpen_Ioo.mem_nhds hpIoo)] with q hq
      have hleft : unitInterval.concatLeftTime q.1 = 1 :=
        unitInterval.concatLeftTime_eq_one hq.1
      have hright : unitInterval.concatRightTime q.1 = 0 :=
        unitInterval.concatRightTime_eq_zero hq.2
      change F q = G q
      simpa only [F, G, hleft, hright] using congrFun hmatch q.2
    have heq : (fun p : I × Sphere 3 ↦ if (p.1 : ℝ) ≤ 1 / 2 then
        H₀.toFun (unitInterval.concatLeftTime p.1, p.2)
      else H₁.toFun (unitInterval.concatRightTime p.1, p.2)) =
        A.piecewise F G := by
      funext p
      by_cases hp : (p.1 : ℝ) ≤ 1 / 2
      · have hpA : p ∈ A := by simpa [A, time] using hp
        rw [if_pos hp, Set.piecewise_eq_of_mem _ _ _ hpA]
      · have hpA : p ∉ A := by simpa [A, time] using hp
        rw [if_neg hp, Set.piecewise_eq_of_notMem _ _ _ hpA]
    rw [heq]
    exact hpaste
  isSmoothEmbedding_slice := by
    intro t
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simpa only [ht, ite_true] using H₀.isSmoothEmbedding_slice
        (unitInterval.concatLeftTime t)
    · simpa only [ht, ite_false] using H₁.isSmoothEmbedding_slice
        (unitInterval.concatRightTime t)
  range_zero := by
    have hzero : (((0 : I) : ℝ) ≤ 1 / 2) := by norm_num
    change range (fun x ↦ if (((0 : I) : ℝ) ≤ 1 / 2) then
      H₀.toFun (unitInterval.concatLeftTime 0, x)
      else H₁.toFun (unitInterval.concatRightTime 0, x)) = range S₀
    simp only [hzero, ite_true]
    simpa only [unitInterval.concatLeftTime_zero] using H₀.range_zero
  range_one := by
    have hnot : ¬((1 : ℝ) ≤ 1 / 2) := by norm_num
    change range (fun x ↦ if ((1 : ℝ) ≤ 1 / 2) then
      H₀.toFun (unitInterval.concatLeftTime 1, x)
      else H₁.toFun (unitInterval.concatRightTime 1, x)) = range S₂
    simp only [hnot, ite_false]
    simpa only [unitInterval.concatRightTime_one] using H₁.range_one

/-- Complement avoidance is preserved by endpoint-matched smooth concatenation. -/
theorem SmoothlyIsotopicInComplement.transOfEndpointEq
    {S₀ S₁ S₂ : SmoothSphereEmbedding 3 4}
    {H₀ : SmoothSphereIsotopy S₀ S₁} {H₁ : SmoothSphereIsotopy S₁ S₂}
    (hH₀ : ∀ p, H₀.toFun p ∉ standardUnlinkCarrier)
    (hH₁ : ∀ p, H₁.toFun p ∉ standardUnlinkCarrier)
    (hmatch : (fun x ↦ H₀.toFun (1, x)) = fun x ↦ H₁.toFun (0, x)) :
    SmoothlyIsotopicInComplement S₀ S₂ := by
  refine ⟨H₀.transOfEndpointEq H₁ hmatch, ?_⟩
  rintro ⟨t, x⟩
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · change (if (t : ℝ) ≤ 1 / 2 then
      H₀.toFun (unitInterval.concatLeftTime t, x)
      else H₁.toFun (unitInterval.concatRightTime t, x)) ∉ standardUnlinkCarrier
    simpa only [ht, ite_true] using hH₀ (unitInterval.concatLeftTime t, x)
  · change (if (t : ℝ) ≤ 1 / 2 then
      H₀.toFun (unitInterval.concatLeftTime t, x)
      else H₁.toFun (unitInterval.concatRightTime t, x)) ∉ standardUnlinkCarrier
    simpa only [ht, ite_false] using hH₁ (unitInterval.concatRightTime t, x)

/-- Smooth isotopy in the fixed unlink complement is transitive.  Although the frozen relation
records only endpoint ranges, the two adjoining endpoint embeddings have equal ranges and hence
differ by the canonical smooth source reparametrization.  After applying that reparametrization
to the second track, `transOfEndpointEq` performs the smooth concatenation. -/
theorem smoothlyIsotopicInComplement_trans
    {S₀ S₁ S₂ : SmoothSphereEmbedding 3 4}
    (h₀₁ : SmoothlyIsotopicInComplement S₀ S₁)
    (h₁₂ : SmoothlyIsotopicInComplement S₁ S₂) :
    SmoothlyIsotopicInComplement S₀ S₂ := by
  obtain ⟨H₀, hH₀⟩ := h₀₁
  obtain ⟨H₁, hH₁⟩ := h₁₂
  let f : SmoothSphereEmbedding 3 4 :=
    TauCeti.SmoothEmbedding.ofIsSmoothEmbedding (fun x ↦ H₀.toFun (1, x))
      (H₀.isSmoothEmbedding_slice 1)
  let g : SmoothSphereEmbedding 3 4 :=
    TauCeti.SmoothEmbedding.ofIsSmoothEmbedding (fun x ↦ H₁.toFun (0, x))
      (H₁.isSmoothEmbedding_slice 0)
  have hrange : range f = range g := by
    simpa only [f, g, TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_coe] using
      H₀.range_one.trans H₁.range_zero.symm
  let e : Sphere 3 ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ Sphere 3 :=
    TauCeti.SmoothEmbedding.sourceDiffeomorphOfRangeEq f g hrange
  let H₁' : SmoothSphereIsotopy S₁ S₂ := H₁.precompDiffeomorph e
  have hmatch : (fun x ↦ H₀.toFun (1, x)) = fun x ↦ H₁'.toFun (0, x) := by
    funext x
    change H₀.toFun (1, x) = H₁.toFun (0, e x)
    have heq := TauCeti.SmoothEmbedding.sourceDiffeomorphOfRangeEq_apply f g hrange x
    have hf : f x = H₀.toFun (1, x) :=
      TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_apply _
        (H₀.isSmoothEmbedding_slice 1) x
    have hg : g (e x) = H₁.toFun (0, e x) :=
      TauCeti.SmoothEmbedding.ofIsSmoothEmbedding_apply _
        (H₁.isSmoothEmbedding_slice 0) (e x)
    exact hf.symm.trans (heq.symm.trans hg)
  exact SmoothlyIsotopicInComplement.transOfEndpointEq hH₀
    (H₁.precompDiffeomorph_avoids e hH₁) hmatch

end SplittingSpheres
