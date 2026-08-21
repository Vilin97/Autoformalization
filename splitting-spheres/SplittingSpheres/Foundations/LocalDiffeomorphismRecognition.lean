/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothLocalDiffeomorphLift

/-!
# Recognizing global and local diffeomorphisms

This file provides small recognition principles for local diffeomorphisms.  A homeomorphism that
is locally diffeomorphic has a smooth inverse.  Local diffeomorphism can also be canceled through
a local-diffeomorphic parametrization, pointwise or over a covering family of parametrizations.

The results are entirely generic and make no geometric identification.
-/

@[expose] public section

open Function Filter Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

universe uM uN uP uH uK

variable {EM FM : Type*}
variable [NormedAddCommGroup EM] [NormedSpace ℝ EM]
variable [NormedAddCommGroup FM] [NormedSpace ℝ FM]
variable {H : Type uH} {K : Type uK}
variable [TopologicalSpace H] [TopologicalSpace K]
variable (I : ModelWithCorners ℝ EM H) (J : ModelWithCorners ℝ FM K)
variable {M : Type uM} {N : Type uN}
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace K N]
variable {n : ℕ∞ω}

/-- A homeomorphism that is a local diffeomorphism is a diffeomorphism. -/
def diffeomorphOfHomeomorphIsLocalDiffeomorph
    (e : M ≃ₜ N) (he : IsLocalDiffeomorph I J n e) :
    M ≃ₘ^n⟮I, J⟯ N where
  toEquiv := e.toEquiv
  contMDiff_toFun := he.contMDiff
  contMDiff_invFun := by
    apply contMDiff_of_comp_isLocalDiffeomorph J I J he e.symm.continuous
    exact (contMDiff_id : ContMDiff J J n (id : N → N)).congr (fun x ↦ by
      simp only [comp_apply, e.apply_symm_apply, id_eq])

private theorem isLocalDiffeomorphAt_congr_of_eqOn_open
    {f g : M → N} {x : M} (hg : IsLocalDiffeomorphAt I J n g x)
    (W : Set M) (hW : IsOpen W) (hxW : x ∈ W)
    (heq : EqOn f g W) :
    IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp <|
    hg.contMDiffAt.continuousAt.preimage_mem_nhds <|
      hg.localInverse.open_source.mem_nhds hg.localInverse_mem_source
  let Ψ := hg.localInverse.symm
  let U := W ∩ V
  have hU : IsOpen U := hW.inter hVopen
  let q := Ψ.toOpenPartialHomeomorph.restrOpen U hU
  have hEq : EqOn f q q.source := by
    intro y hy
    change y ∈ Ψ.source ∩ U at hy
    have hyTarget : y ∈ hg.localInverse.target := hy.1
    have hgySource : g y ∈ hg.localInverse.source := hVsub hy.2.2
    apply (heq hy.2.1).trans
    change g y = hg.localInverse.symm y
    calc
      g y = hg.localInverse.symm (hg.localInverse (g y)) :=
        (hg.localInverse.left_inv hgySource).symm
      _ = hg.localInverse.symm y :=
        congrArg hg.localInverse.symm (hg.localInverse_left_inv hyTarget)
  let Φ : PartialDiffeomorph I J M N n :=
    { toPartialEquiv :=
        { toFun := f
          invFun := q.toPartialEquiv.invFun
          source := q.source
          target := q.target
          map_source' := by
            intro y hy
            rw [hEq hy]
            exact q.map_source hy
          map_target' := by
            intro y hy
            exact q.map_target hy
          left_inv' := by
            intro y hy
            rw [hEq hy]
            exact q.left_inv hy
          right_inv' := by
            intro y hy
            exact (hEq (q.toPartialEquiv.map_target hy)).trans
              (q.toPartialEquiv.right_inv hy) }
      open_source := q.open_source
      open_target := q.open_target
      contMDiffOn_toFun := by
        apply (Ψ.contMDiffOn_toFun.mono ?_).congr hEq
        intro y hy
        change y ∈ Ψ.source ∩ U at hy
        exact hy.1
      contMDiffOn_invFun := by
        apply Ψ.contMDiffOn_invFun.mono
        intro y hy
        change y ∈ Ψ.target ∩ Ψ.symm ⁻¹' U at hy
        exact hy.1 }
  apply Φ.isLocalDiffeomorphAt
  change x ∈ Ψ.source ∩ U
  exact ⟨hg.localInverse_mem_target, hxW, hxV⟩

private theorem isLocalDiffeomorphAt_congr_of_eventuallyEq
    {f g : M → N} {x : M} (hg : IsLocalDiffeomorphAt I J n g x)
    (heq : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp heq
  exact isLocalDiffeomorphAt_congr_of_eqOn_open I J hg W hWopen hxW
    (fun y hy ↦ hWsub hy)

/-- Cancel a local-diffeomorphic parametrization at one represented point. -/
theorem isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    {P : Type uP} [TopologicalSpace P] [ChartedSpace H P]
    (F : M → N) (c : P → M)
    (hc : IsLocalDiffeomorph I I n c)
    (hFc : IsLocalDiffeomorph I J n (F ∘ c))
    (p : P) :
    IsLocalDiffeomorphAt I J n F (c p) := by
  let hp := hc p
  have hcomp : IsLocalDiffeomorphAt I J n
      ((F ∘ c) ∘ hp.localInverse) (c p) :=
    hp.localInverse_isLocalDiffeomorphAt.comp J N
      (hFc (hp.localInverse (c p)))
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq I J hcomp
  filter_upwards [hp.localInverse_eventuallyEq_right] with y hy
  simp only [comp_apply] at hy ⊢
  simp [hy]

/-- Descend local diffeomorphism through a surjective local-diffeomorphic parametrization. -/
theorem isLocalDiffeomorph_of_localDiffeomorph_parametrized_cover
    {P : Type uP} [TopologicalSpace P] [ChartedSpace H P]
    (F : M → N) (c : P → M)
    (hc : IsLocalDiffeomorph I I n c)
    (hFc : IsLocalDiffeomorph I J n (F ∘ c))
    (hcover : ∀ x : M, ∃ p : P, c p = x) :
    IsLocalDiffeomorph I J n F := by
  intro x
  obtain ⟨p, rfl⟩ := hcover x
  exact isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    I J F c hc hFc p

/-- Descend local diffeomorphism through three local-diffeomorphic parametrizations whose images
cover the source. -/
theorem isLocalDiffeomorph_of_three_localDiffeomorph_parametrizations
    {P₁ P₂ P₃ : Type*}
    [TopologicalSpace P₁] [ChartedSpace H P₁]
    [TopologicalSpace P₂] [ChartedSpace H P₂]
    [TopologicalSpace P₃] [ChartedSpace H P₃]
    (F : M → N) (c₁ : P₁ → M) (c₂ : P₂ → M) (c₃ : P₃ → M)
    (hc₁ : IsLocalDiffeomorph I I n c₁)
    (hc₂ : IsLocalDiffeomorph I I n c₂)
    (hc₃ : IsLocalDiffeomorph I I n c₃)
    (hFc₁ : IsLocalDiffeomorph I J n (F ∘ c₁))
    (hFc₂ : IsLocalDiffeomorph I J n (F ∘ c₂))
    (hFc₃ : IsLocalDiffeomorph I J n (F ∘ c₃))
    (hcover : ∀ x : M,
      (∃ p : P₁, c₁ p = x) ∨ (∃ p : P₂, c₂ p = x) ∨
        (∃ p : P₃, c₃ p = x)) :
    IsLocalDiffeomorph I J n F := by
  intro x
  rcases hcover x with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
      I J F c₁ hc₁ hFc₁ p
  · exact isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
      I J F c₂ hc₂ hFc₂ p
  · exact isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
      I J F c₃ hc₃ hFc₃ p

end SplittingSpheres
