/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Split derivatives give immersions

This file packages the Banach-space inverse function theorem at arbitrary differentiability
order, and applies it to the standard augmented-map proof that a split derivative gives an
immersion normal form.

The inverse supplied directly by the inverse function theorem is initially only `C¹`.  We
restrict its domain to the open locus where the derivative remains a continuous linear
equivalence; the higher-order inverse theorem then upgrades the inverse to the requested order.
-/

@[expose] public section

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {a : E} {n : ℕ∞ω} {e : E ≃L[ℝ] F}

/-- The inverse function theorem, packaged as an all-orders local manifold diffeomorphism.

The forward map is assumed globally `C^n`; the conclusion is local at the base point.  The
nonzero-order hypothesis supplies the continuously varying derivative needed to restrict to the
open locus of invertible derivatives.
-/
theorem isLocalDiffeomorphAt_of_contDiff_hasFDerivAt_equiv
    (hf : ContDiff ℝ n f) (hfa : HasFDerivAt f (e : E →L[ℝ] F) a)
    (hn : n ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) n f a := by
  let P : OpenPartialHomeomorph E F :=
    hf.contDiffAt.toOpenPartialHomeomorph f hfa hn
  let U : Set E := (fderiv ℝ f) ⁻¹'
    range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
  have hUopen : IsOpen U :=
    ContinuousLinearEquiv.isOpen.preimage (hf.continuous_fderiv hn)
  have haU : a ∈ U := by
    change fderiv ℝ f a ∈ range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
    rw [hfa.fderiv]
    exact mem_range_self e
  let Q : OpenPartialHomeomorph E F := P.restr U
  have haP : a ∈ P.source :=
    hf.contDiffAt.mem_toOpenPartialHomeomorph_source hfa hn
  have haQ : a ∈ Q.source := by
    simpa only [Q, P.restr_source' U hUopen, mem_inter_iff] using ⟨haP, haU⟩
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n := {
    toPartialEquiv := Q.toPartialEquiv
    open_source := Q.open_source
    open_target := Q.open_target
    contMDiffOn_toFun := by
      change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) n f Q.source
      exact hf.contMDiff.contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply ContDiffWithinAt.contMDiffWithinAt
      apply ContDiffAt.contDiffWithinAt
      have hxy : Q.symm y ∈ U := by
        have hxsource : Q.symm y ∈ Q.source := Q.symm.map_source hy
        rw [show Q.source = P.source ∩ U by exact P.restr_source' U hUopen] at hxsource
        exact hxsource.2
      obtain ⟨ex, hex⟩ : ∃ ex : E ≃L[ℝ] F,
          (ex : E →L[ℝ] F) = fderiv ℝ f (Q.symm y) := hxy
      apply Q.contDiffAt_symm hy (f₀' := ex)
      · rw [hex]
        exact (hf.differentiable hn).differentiableAt.hasFDerivAt
      · exact hf.contDiffAt
    }
  exact Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) n haQ

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

/-- Adding a complementary linear variable turns a map with a split derivative into a local
diffeomorphism. -/
theorem augmented_isLocalDiffeomorphAt
    (T : E → F) (L : (E × C) ≃L[ℝ] F) (a : E) {n : ℕ∞ω}
    (hT : ContDiff ℝ n T)
    (hder : HasFDerivAt T
      ((ContinuousLinearEquiv.toContinuousLinearMap L).comp
        (ContinuousLinearMap.inl ℝ E C)) a)
    (hn : n ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E × C) 𝓘(ℝ, F) n
      (fun q : E × C ↦ T q.1 +
        ContinuousLinearEquiv.toContinuousLinearMap L ((0 : E), q.2)) (a, 0) := by
  let tangential : (E × C) →L[ℝ] F :=
    ((ContinuousLinearEquiv.toContinuousLinearMap L).comp
      (ContinuousLinearMap.inl ℝ E C)).comp
        (ContinuousLinearMap.fst ℝ E C)
  let normal : (E × C) →L[ℝ] F :=
    (ContinuousLinearEquiv.toContinuousLinearMap L).comp
      ((ContinuousLinearMap.inr ℝ E C).comp (ContinuousLinearMap.snd ℝ E C))
  have hA : ContDiff ℝ n
      (fun q : E × C ↦ T q.1 +
        ContinuousLinearEquiv.toContinuousLinearMap L ((0 : E), q.2)) := by
    have hfirst : ContDiff ℝ n (fun q : E × C ↦ T q.1) :=
      hT.comp contDiff_fst
    have hnormal : ContDiff ℝ n
        (fun q : E × C ↦
          ContinuousLinearEquiv.toContinuousLinearMap L ((0 : E), q.2)) := by
      rw [show (fun q : E × C ↦
        ContinuousLinearEquiv.toContinuousLinearMap L ((0 : E), q.2)) = normal by
          funext q
          rfl]
      exact normal.contDiff
    exact hfirst.add hnormal
  have hAder : HasFDerivAt
      (fun q : E × C ↦ T q.1 +
        ContinuousLinearEquiv.toContinuousLinearMap L ((0 : E), q.2))
      (ContinuousLinearEquiv.toContinuousLinearMap L) (a, (0 : C)) := by
    have hfst : HasFDerivAt (fun q : E × C ↦ q.1)
        (ContinuousLinearMap.fst ℝ E C) (a, (0 : C)) := hasFDerivAt_fst
    have hfirst := hder.comp (a, (0 : C)) hfst
    have hnormal : HasFDerivAt
        (fun q : E × C ↦
          ContinuousLinearEquiv.toContinuousLinearMap L ((0 : E), q.2))
        normal (a, (0 : C)) := by
      rw [show (fun q : E × C ↦
        ContinuousLinearEquiv.toContinuousLinearMap L ((0 : E), q.2)) = normal by
          funext q
          rfl]
      exact normal.hasFDerivAt
    have htangential :
        ((ContinuousLinearEquiv.toContinuousLinearMap L).comp
          (ContinuousLinearMap.inl ℝ E C)).comp
            (ContinuousLinearMap.fst ℝ E C) = tangential := rfl
    have hlin : tangential + normal =
          ContinuousLinearEquiv.toContinuousLinearMap L := by
      apply ContinuousLinearMap.ext
      rintro ⟨qE, qC⟩
      change ContinuousLinearEquiv.toContinuousLinearMap L (qE, 0) +
        ContinuousLinearEquiv.toContinuousLinearMap L (0, qC) =
        ContinuousLinearEquiv.toContinuousLinearMap L (qE, qC)
      rw [← (ContinuousLinearEquiv.toContinuousLinearMap L).map_add]
      congr
      exact Prod.ext (add_zero qE) (zero_add qC)
    exact (hfirst.add hnormal).congr_fderiv (htangential ▸ hlin)
  exact isLocalDiffeomorphAt_of_contDiff_hasFDerivAt_equiv hA hAder hn

/-- A globally smooth map whose derivative is the inclusion under a continuous linear
equivalence has the corresponding immersion normal form at the base point. -/
theorem isImmersionAtOfComplement_of_contDiff_hasFDerivAt_split
    (T : E → F) (L : (E × C) ≃L[ℝ] F) (a : E) {n : ℕ∞ω}
    (hT : ContDiff ℝ n T)
    (hder : HasFDerivAt T
      ((ContinuousLinearEquiv.toContinuousLinearMap L).comp
        (ContinuousLinearMap.inl ℝ E C)) a)
    (hn : n ≠ 0) :
    Manifold.IsImmersionAtOfComplement C 𝓘(ℝ, E) 𝓘(ℝ, F) n T a := by
  let A : E × C → F := fun q ↦ T q.1 +
    ContinuousLinearEquiv.toContinuousLinearMap L ((0 : E), q.2)
  have hlocal := augmented_isLocalDiffeomorphAt T L a hT hder hn
  change ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E × C) 𝓘(ℝ, F) (E × C) F n,
    (a, (0 : C)) ∈ Φ.source ∧
      EqOn (fun q : E × C ↦ T q.1 +
        ContinuousLinearEquiv.toContinuousLinearMap L ((0 : E), q.2)) Φ Φ.source at hlocal
  obtain ⟨Φ, hbase, hΦeq⟩ := hlocal
  let inc : E → E × C := fun x ↦ (x, 0)
  let s : Set E := inc ⁻¹' Φ.source
  have hsopen : IsOpen s := Φ.open_source.preimage (by fun_prop)
  let c : OpenPartialHomeomorph E E := (OpenPartialHomeomorph.refl E).restr s
  let ell : OpenPartialHomeomorph (E × C) F :=
    ContinuousLinearEquiv.toHomeomorph L |>.toOpenPartialHomeomorph
  let d : OpenPartialHomeomorph F F := Φ.toOpenPartialHomeomorph.symm.trans ell
  have hac : a ∈ c.source := by
    rw [show c.source = (OpenPartialHomeomorph.refl E).source ∩ s by
      exact (OpenPartialHomeomorph.refl E).restr_source' s hsopen]
    refine ⟨by simp, ?_⟩
    simpa only [s, mem_preimage, inc] using hbase
  have hTa : A (a, 0) = T a := by simp [A]
  have hΦa : Φ (a, 0) = T a := by
    rw [← hTa]
    exact (hΦeq hbase).symm
  have hTad : T a ∈ d.source := by
    simp only [d, OpenPartialHomeomorph.trans_source, mem_inter_iff,
      OpenPartialHomeomorph.symm_source, mem_preimage, ell,
      Homeomorph.toOpenPartialHomeomorph_source]
    refine ⟨?_, trivial⟩
    rw [← hΦa]
    exact Φ.toOpenPartialHomeomorph.map_source hbase
  have hcmax : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) n E := by
    apply restr_mem_maximalAtlas (contDiffGroupoid n 𝓘(ℝ, E))
      (IsManifold.subset_maximalAtlas (by simp)) hsopen
  have hd_smooth : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) n d d.source := by
    rw [show (d : F → F) =
      (ContinuousLinearEquiv.toHomeomorph L) ∘ Φ.symm by rfl]
    apply (ContinuousLinearEquiv.contDiff L).contMDiff.comp_contMDiffOn
      (Φ.symm.contMDiffOn.mono ?_)
    intro z hz
    exact hz.1
  have hd_symm_smooth : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) n d.symm d.target := by
    rw [show (d.symm : F → F) = Φ ∘
      (ContinuousLinearEquiv.toHomeomorph L).symm by rfl]
    apply Φ.contMDiffOn.comp
      ((ContinuousLinearEquiv.contDiff L.symm).contMDiff.contMDiffOn)
    intro z hz
    exact hz.2
  have hdmax : d ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) n F :=
    d.mem_maximalAtlas_of_contMDiffOn hd_smooth hd_symm_smooth
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    hT.continuous.continuousAt L c d hac hTad hcmax hdmax
  intro y hy
  have hyc : y ∈ c.target := by
    rw [OpenPartialHomeomorph.extend_target] at hy
    have hy' := hy.1
    change 𝓘(ℝ, E).symm y ∈ c.target at hy'
    simpa only [modelWithCornersSelf_coe_symm, id_eq] using hy'
  have hy_source : (y, (0 : C)) ∈ Φ.source := by
    have : y ∈ s := by
      have hc_target : c.target = s := by
        change ((OpenPartialHomeomorph.refl E).restr s).target = s
        rw [(OpenPartialHomeomorph.refl E).restr_toPartialEquiv' s hsopen]
        exact PartialEquiv.refl_restr_target s
      rwa [hc_target] at hyc
    exact this
  have hΦy : Φ (y, (0 : C)) = T y := by
    have h := hΦeq hy_source
    change A (y, (0 : C)) = Φ (y, (0 : C)) at h
    calc
      Φ (y, (0 : C)) = A (y, (0 : C)) := h.symm
      _ = T y := by simp [A]
  rw [OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm]
  change d (T (c.symm y)) = L (y, (0 : C))
  have hcy : c.symm y = y := by rfl
  rw [hcy]
  change L (Φ.toOpenPartialHomeomorph.symm (T y)) = L (y, (0 : C))
  rw [← hΦy]
  congr 1
  exact Φ.toOpenPartialHomeomorph.left_inv hy_source

end SplittingSpheres
