/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CompactlySupportedTimeDependentFlow
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Analysis.ODE.SmoothParameter

/-!
# Smooth compactly supported time-dependent flows

This file upgrades the selected Picard--Lindelöf flows from
`CompactlySupportedTimeDependentFlow` to smooth flows in finite-dimensional real normed spaces.
The local input is TauCeti's smooth parameter dependence theorem, applied to a scaled displacement
field which vanishes at elapsed time zero.  ODE uniqueness identifies that smooth germ with the
already selected flow.  The autonomous flow law and connectedness of the time interval then
propagate the germ across the whole unit-time slab.

Every autonomous slice is bundled as a diffeomorphism.  For a smooth time-dependent field, the
spacetime flow similarly gives a diffeomorphism of the spatial fiber from time zero to time `t`.
The final existence theorems return these diffeomorphisms with exact pointwise agreement with the
continuous `TauCeti.AmbientIsotopy` constructed by the preceding module.
-/

@[expose] public section

open Filter Function Metric Set
open unitInterval
open scoped ContDiff Manifold NNReal Topology unitInterval

noncomputable section

namespace SplittingSpheres.TimeDependentFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The selected autonomous flow satisfies the flow-addition law whenever the base time and
elapsed time both lie in `[-1, 1]`. -/
theorem flow_add_on_unit_interval
    (W : E → E) (K : ℝ≥0) (hWlip : LipschitzWith K W)
    (flow : E × ℝ → E)
    (hflow0 : ∀ x, flow (x, 0) = x)
    (hflow : ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t) :
    ∀ x t s, t ∈ Icc (-1 : ℝ) 1 → s ∈ Icc (-1 : ℝ) 1 →
      flow (flow (x, t), s) = flow (x, t + s) := by
  intro x t s ht hs
  let f : ℝ → E := fun u ↦ flow (flow (x, t), u)
  let g : ℝ → E := fun u ↦ flow (x, t + u)
  have hsmall : Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ) ⊆ Icc (-3 : ℝ) 3 := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hshift : MapsTo (fun u : ℝ ↦ t + u) (Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ))
      (Icc (-3 : ℝ) 3) := by
    intro u hu
    constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
  have hf_cont : ContinuousOn f (Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ)) := by
    exact HasDerivWithinAt.continuousOn fun u hu ↦
      (hflow (flow (x, t)) u (hsmall hu)).mono hsmall
  have hg_cont : ContinuousOn g (Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ)) := by
    have hc : ContinuousOn (fun r ↦ flow (x, r)) (Icc (-3 : ℝ) 3) :=
      HasDerivWithinAt.continuousOn (fun r hr ↦ hflow x r hr)
    exact hc.comp (by fun_prop) hshift
  have heq : EqOn f g (Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ)) := by
    apply ODE_solution_unique_of_mem_Icc
      (s := fun _ ↦ univ) (K := K) (t₀ := 0)
      (fun _ _ ↦ hWlip.lipschitzOnWith)
      (by norm_num)
      hf_cont
    · intro u hu
      exact (hflow (flow (x, t)) u (hsmall (Ioo_subset_Icc_self hu))).hasDerivAt
        (Icc_mem_nhds (by linarith [hu.1]) (by linarith [hu.2]))
    · simp
    · exact hg_cont
    · intro u hu
      have hu' : t + u ∈ Ioo (-3 : ℝ) 3 := by
        constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
      have hd := (hflow x (t + u) (Ioo_subset_Icc_self hu')).hasDerivAt
        (Icc_mem_nhds hu'.1 hu'.2)
      have hd' : HasDerivAt (fun r ↦ flow (x, r)) (W (flow (x, u + t))) (u + t) := by
        simpa [add_comm] using hd
      simpa [g, add_comm] using hd'.comp_add_const u t
    · simp
    · simp [f, g, hflow0]
  exact heq ⟨by linarith [hs.1], by linarith [hs.2]⟩

private theorem contDiffAt_flow_zero
    [FiniteDimensional ℝ E]
    (n : ℕ) (W : E → E) (hW : ContDiff ℝ ∞ W)
    (K : ℝ≥0) (hWlip : LipschitzWith K W)
    (flow : E × ℝ → E)
    (hflow0 : ∀ x, flow (x, 0) = x)
    (hflow : ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t)
    (x₀ : E) :
    ContDiffAt ℝ n flow (x₀, 0) := by
  let F : (E × ℝ) × E → E := fun p ↦ p.1.2 • W (p.1.1 + p.2)
  have hF : ContDiff ℝ ∞ F := by
    fun_prop
  obtain ⟨γ, hγsmooth, hγbase, hγode⟩ :=
    ODE.exists_contDiffAt_picard_solution n F (x₀, 0) 0
      ((hF.of_le (by simp)).contDiffAt) (by simp [F])
  let oneIcc : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
  have hcand : ContDiffAt ℝ (n + 1)
      (fun p : E × ℝ ↦ p.1 + γ p oneIcc) (x₀, 0) := by
    apply contDiffAt_fst.add
    change ContDiffAt ℝ (n + 1)
      ((ContinuousMap.evalCLM ℝ oneIcc) ∘ γ) (x₀, 0)
    exact (ContinuousMap.evalCLM ℝ oneIcc).contDiff.contDiffAt.comp (x₀, 0) hγsmooth
  have hsmall : ∀ᶠ p in nhds (x₀, 0), p.2 ∈ Ioo (-1 : ℝ) 1 := by
    exact (continuousAt_snd : ContinuousAt (fun p : E × ℝ ↦ p.2) (x₀, 0)).eventually
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  have heq : (fun p : E × ℝ ↦ p.1 + γ p oneIcc) =ᶠ[nhds (x₀, 0)] flow := by
    filter_upwards [hγode, hsmall] with p hp hplam
    let f : ℝ → E := fun s ↦ γ p (Set.projIcc 0 1 zero_le_one s)
    let g : ℝ → E := fun s ↦ flow (p.1, p.2 * s) - p.1
    let Kp : ℝ≥0 := ‖p.2‖₊ * K
    have htrans : LipschitzWith 1 (fun y : E ↦ p.1 + y) := by
      apply LipschitzWith.mk_one
      intro y z
      simp
    have hFp : LipschitzWith Kp (fun y ↦ F (p, y)) := by
      simpa [F, Kp, Function.comp_def] using
        (lipschitzWith_smul p.2).comp (hWlip.comp htrans)
    have hf_cont : ContinuousOn f (Icc (0 : ℝ) 1) :=
      (γ p).continuous.comp continuous_projIcc |>.continuousOn
    have hg_deriv : ∀ s ∈ Icc (0 : ℝ) 1,
        HasDerivAt g (F (p, g s)) s := by
      intro s hs
      have htime : p.2 * s ∈ Ioo (-3 : ℝ) 3 := by
        have hs' : 0 ≤ s := hs.1
        have hsone : s ≤ 1 := hs.2
        constructor
        · nlinarith [hplam.1, hplam.2]
        · nlinarith [hplam.1, hplam.2]
      have hd := (hflow p.1 (p.2 * s) (Ioo_subset_Icc_self htime)).hasDerivAt
        (Icc_mem_nhds htime.1 htime.2)
      have hmul : HasDerivAt (fun r : ℝ ↦ p.2 * r) p.2 s := by
        simpa using (hasDerivAt_id s).const_mul p.2
      have hcomp := hd.scomp s hmul
      simpa [g, F, smul_eq_mul] using hcomp.sub_const p.1
    have hg_cont : ContinuousOn g (Icc (0 : ℝ) 1) :=
      HasDerivAt.continuousOn hg_deriv
    have huniq : EqOn f g (Icc (0 : ℝ) 1) := by
      apply ODE_solution_unique_of_mem_Icc_right
        (v := fun _ y ↦ F (p, y)) (s := fun _ ↦ univ) (K := Kp)
        (fun _ _ ↦ hFp.lipschitzOnWith)
        hf_cont
      · exact hp.2.2
      · simp
      · exact hg_cont
      · intro s hs
        exact (hg_deriv s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt
      · simp
      · change γ p (Set.projIcc 0 1 zero_le_one 0) =
          flow (p.1, p.2 * 0) - p.1
        rw [mul_zero, hflow0, sub_self]
        simpa using hp.1 (Set.projIcc 0 1 zero_le_one 0)
    have hone := huniq (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    simpa [f, g, oneIcc] using congrArg (p.1 + ·) hone
  exact (hcand.of_le (by exact_mod_cast Nat.le_succ n)).congr_of_eventuallyEq heq.symm

private theorem contDiffAt_flow_slice
    [FiniteDimensional ℝ E]
    (n : ℕ) (W : E → E) (hW : ContDiff ℝ ∞ W)
    (K : ℝ≥0) (hWlip : LipschitzWith K W)
    (flow : E × ℝ → E)
    (hflow0 : ∀ x, flow (x, 0) = x)
    (hflow : ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t)
    (x₀ : E) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      ContDiffAt ℝ n (fun x ↦ flow (x, t)) x₀ := by
  let _ : ConnectedSpace (Set.Icc (-1 : ℝ) 1) :=
    Subtype.connectedSpace ⟨nonempty_Icc.mpr (by norm_num), isPreconnected_Icc⟩
  let S : Set (Set.Icc (-1 : ℝ) 1) :=
    {t | ContDiffAt ℝ n (fun x ↦ flow (x, (t : ℝ))) x₀}
  have htime_cont : Continuous
      (fun t : Set.Icc (-1 : ℝ) 1 ↦ flow (x₀, (t : ℝ))) := by
    rw [← continuousOn_univ]
    have hc : ContinuousOn (fun t ↦ flow (x₀, t)) (Icc (-3 : ℝ) 3) :=
      HasDerivWithinAt.continuousOn (fun t ht ↦ hflow x₀ t ht)
    apply hc.comp (by fun_prop)
    intro t _
    exact ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change ContDiffAt ℝ n (fun x ↦ flow (x, (t : ℝ))) x₀ at ht
    have houter := (contDiffAt_flow_zero n W hW K hWlip flow hflow0 hflow
      (flow (x₀, (t : ℝ)))).eventually (by simp)
    have hmap : Tendsto
        (fun u : Set.Icc (-1 : ℝ) 1 ↦
          (flow (x₀, (t : ℝ)), (u : ℝ) - (t : ℝ)))
        (nhds t) (nhds (flow (x₀, (t : ℝ)), 0)) := by
      have hc : ContinuousAt
          (fun u : Set.Icc (-1 : ℝ) 1 ↦
            (flow (x₀, (t : ℝ)), (u : ℝ) - (t : ℝ))) t := by
        fun_prop
      simpa only [ContinuousAt, sub_self] using hc
    have hout := hmap.eventually houter
    have hdeltaMap : Tendsto
        (fun u : Set.Icc (-1 : ℝ) 1 ↦ (u : ℝ) - (t : ℝ))
        (nhds t) (nhds 0) := by
      have hc : ContinuousAt
          (fun u : Set.Icc (-1 : ℝ) 1 ↦ (u : ℝ) - (t : ℝ)) t := by
        fun_prop
      simpa only [ContinuousAt, sub_self] using hc
    have hdelta : ∀ᶠ u : Set.Icc (-1 : ℝ) 1 in nhds t,
        (u : ℝ) - (t : ℝ) ∈ Icc (-1 : ℝ) 1 :=
      hdeltaMap.eventually (Icc_mem_nhds
        (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hout, hdelta] with u hu hdu
    change ContDiffAt ℝ n (fun x ↦ flow (x, (u : ℝ))) x₀
    have hinner : ContDiffAt ℝ n
        (fun x : E ↦ (flow (x, (t : ℝ)), (u : ℝ) - (t : ℝ))) x₀ :=
      ht.prodMk contDiffAt_const
    have hcomp := hu.comp x₀ hinner
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [] with x
    change flow (x, (u : ℝ)) =
      flow (flow (x, (t : ℝ)), (u : ℝ) - (t : ℝ))
    rw [flow_add_on_unit_interval W K hWlip flow hflow0 hflow
      x (t : ℝ) ((u : ℝ) - (t : ℝ)) t.property hdu]
    congr 1
    ring_nf
  have hopen_compl : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change ¬ContDiffAt ℝ n (fun x ↦ flow (x, (t : ℝ))) x₀ at ht
    have houter := (contDiffAt_flow_zero n W hW K hWlip flow hflow0 hflow
      (flow (x₀, (t : ℝ)))).eventually (by simp)
    have hmap : Tendsto
        (fun u : Set.Icc (-1 : ℝ) 1 ↦
          (flow (x₀, (u : ℝ)), (t : ℝ) - (u : ℝ)))
        (nhds t) (nhds (flow (x₀, (t : ℝ)), 0)) := by
      have hsub : ContinuousAt
          (fun u : Set.Icc (-1 : ℝ) 1 ↦ (t : ℝ) - (u : ℝ)) t := by
        fun_prop
      have hc : ContinuousAt
          (fun u : Set.Icc (-1 : ℝ) 1 ↦
            (flow (x₀, (u : ℝ)), (t : ℝ) - (u : ℝ))) t :=
        htime_cont.continuousAt.prodMk hsub
      simpa only [ContinuousAt, sub_self] using hc
    have hout := hmap.eventually houter
    have hdeltaMap : Tendsto
        (fun u : Set.Icc (-1 : ℝ) 1 ↦ (t : ℝ) - (u : ℝ))
        (nhds t) (nhds 0) := by
      have hc : ContinuousAt
          (fun u : Set.Icc (-1 : ℝ) 1 ↦ (t : ℝ) - (u : ℝ)) t := by
        fun_prop
      simpa only [ContinuousAt, sub_self] using hc
    have hdelta : ∀ᶠ u : Set.Icc (-1 : ℝ) 1 in nhds t,
        (t : ℝ) - (u : ℝ) ∈ Icc (-1 : ℝ) 1 :=
      hdeltaMap.eventually (Icc_mem_nhds
        (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hout, hdelta] with u hu hdu
    change ¬ContDiffAt ℝ n (fun x ↦ flow (x, (u : ℝ))) x₀
    intro husmooth
    apply ht
    have hinner : ContDiffAt ℝ n
        (fun x : E ↦ (flow (x, (u : ℝ)), (t : ℝ) - (u : ℝ))) x₀ :=
      husmooth.prodMk contDiffAt_const
    have hcomp := hu.comp x₀ hinner
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [] with x
    change flow (x, (t : ℝ)) =
      flow (flow (x, (u : ℝ)), (t : ℝ) - (u : ℝ))
    rw [flow_add_on_unit_interval W K hWlip flow hflow0 hflow
      x (u : ℝ) ((t : ℝ) - (u : ℝ)) u.property hdu]
    congr 1
    ring_nf
  have hclosed : IsClosed S := by
    simpa only [compl_compl] using hopen_compl.isClosed_compl
  have hnonempty : S.Nonempty := by
    let zeroT : Set.Icc (-1 : ℝ) 1 := ⟨0, by norm_num⟩
    refine ⟨zeroT, ?_⟩
    change ContDiffAt ℝ n (fun x ↦ flow (x, 0)) x₀
    exact contDiffAt_id.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall hflow0
  have hSuniv : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hnonempty
  intro t ht
  let tsub : Set.Icc (-1 : ℝ) 1 := ⟨t, ht⟩
  have hmem : tsub ∈ S := by
    rw [hSuniv]
    exact mem_univ _
  exact hmem

private theorem contDiffAt_flow
    [FiniteDimensional ℝ E]
    (n : ℕ) (W : E → E) (hW : ContDiff ℝ ∞ W)
    (K : ℝ≥0) (hWlip : LipschitzWith K W)
    (flow : E × ℝ → E)
    (hflow0 : ∀ x, flow (x, 0) = x)
    (hflow : ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t)
    (x₀ : E) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ContDiffAt ℝ n flow (x₀, t) := by
  have hslice := contDiffAt_flow_slice n W hW K hWlip flow hflow0 hflow x₀ t ht
  have hfirst : ContDiffAt ℝ n
      (fun p : E × ℝ ↦ flow (p.1, t)) (x₀, t) :=
    by simpa [Function.comp_def] using hslice.comp (x₀, t) contDiffAt_fst
  have hinner : ContDiffAt ℝ n
      (fun p : E × ℝ ↦ (flow (p.1, t), p.2 - t)) (x₀, t) :=
    hfirst.prodMk (contDiffAt_snd.sub contDiffAt_const)
  have houter := contDiffAt_flow_zero n W hW K hWlip flow hflow0 hflow
    (flow (x₀, t))
  have houter' : ContDiffAt ℝ n flow (flow (x₀, t), t - t) := by
    simpa only [sub_self] using houter
  have hcomp := houter'.comp (x₀, t) hinner
  have hdeltaMap : Tendsto (fun p : E × ℝ ↦ p.2 - t)
      (nhds (x₀, t)) (nhds 0) := by
    have hc : ContinuousAt (fun p : E × ℝ ↦ p.2 - t) (x₀, t) := by
      fun_prop
    simpa only [ContinuousAt, sub_self] using hc
  have hdelta : ∀ᶠ p : E × ℝ in nhds (x₀, t),
      p.2 - t ∈ Icc (-1 : ℝ) 1 :=
    hdeltaMap.eventually (Icc_mem_nhds
      (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hdelta] with p hp
  change flow p = flow (flow (p.1, t), p.2 - t)
  rw [flow_add_on_unit_interval W K hWlip flow hflow0 hflow
    p.1 t (p.2 - t) ht hp]
  congr 1
  ring_nf

/-- Every unit-time slice of a selected smooth autonomous flow is smooth in its initial point. -/
theorem contDiff_flow_slice
    [FiniteDimensional ℝ E]
    (W : E → E) (hW : ContDiff ℝ ∞ W)
    (K : ℝ≥0) (hWlip : LipschitzWith K W)
    (flow : E × ℝ → E)
    (hflow0 : ∀ x, flow (x, 0) = x)
    (hflow : ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t)
    (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x ↦ flow (x, t)) := by
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_flow_slice n W hW K hWlip flow hflow0 hflow x t ht

/-- A selected smooth autonomous flow depends smoothly on its initial point and elapsed time on
the closed unit-time slab. -/
theorem contDiffOn_flow_unit_interval
    [FiniteDimensional ℝ E]
    (W : E → E) (hW : ContDiff ℝ ∞ W)
    (K : ℝ≥0) (hWlip : LipschitzWith K W)
    (flow : E × ℝ → E)
    (hflow0 : ∀ x, flow (x, 0) = x)
    (hflow : ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t) :
    ContDiffOn ℝ ∞ flow (univ ×ˢ Icc (-1 : ℝ) 1) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_infty]
  intro n
  exact contDiffAt_flow n W hW K hWlip flow hflow0 hflow p.1 p.2 hp.2

private def autonomousFlowDiffeomorph
    [FiniteDimensional ℝ E]
    (W : E → E) (hW : ContDiff ℝ ∞ W)
    (K : ℝ≥0) (hWlip : LipschitzWith K W)
    (flow : E × ℝ → E)
    (hflow0 : ∀ x, flow (x, 0) = x)
    (hflow : ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t)
    (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    E ≃ₘ[ℝ] E where
  toEquiv :=
    { toFun := fun x ↦ flow (x, t)
      invFun := fun x ↦ flow (x, -t)
      left_inv := fun x ↦ flow_inverse_on_unit_interval W K hWlip flow hflow0 hflow x t ht
      right_inv := fun x ↦ by
        simpa using flow_inverse_on_unit_interval W K hWlip flow hflow0 hflow x (-t)
          ⟨by linarith [ht.2], by linarith [ht.1]⟩ }
  contMDiff_toFun :=
    (contDiff_flow_slice W hW K hWlip flow hflow0 hflow t ht).contMDiff
  contMDiff_invFun :=
    (contDiff_flow_slice W hW K hWlip flow hflow0 hflow (-t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩).contMDiff

/-- A bounded globally Lipschitz smooth autonomous vector field has a selected continuous ambient
isotopy whose time slices are diffeomorphisms and whose flow is jointly smooth on the unit slab. -/
theorem exists_ambientIsotopy_autonomous_diffeomorph
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (W : E → E) (hW : ContDiff ℝ ∞ W) (K L : ℝ≥0)
    (hWlip : LipschitzWith K W) (hWnorm : ∀ x, ‖W x‖ ≤ L) :
    ∃ (Φ : TauCeti.AmbientIsotopy E) (flow : E × ℝ → E)
        (Ψ : I → E ≃ₘ[ℝ] E),
      (∀ x, flow (x, 0) = x) ∧
      (∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u ↦ flow (x, u)) (W (flow (x, t)))
          (Icc (-3) 3) t) ∧
      ContinuousOn flow (univ ×ˢ Icc (-3 : ℝ) 3) ∧
      ContDiffOn ℝ ∞ flow (univ ×ˢ Icc (-1 : ℝ) 1) ∧
      (∀ t : I, ∀ x, Ψ t x = flow (x, (t : ℝ))) ∧
      ∀ t : I, ∀ x, Φ.toContinuousMap (t, x) = Ψ t x := by
  obtain ⟨Φ, flow, hflow0, hflow, hflow_cont, hΦ⟩ :=
    exists_ambientIsotopy_autonomous W K L hWlip hWnorm
  let Ψ : I → E ≃ₘ[ℝ] E := fun t ↦
    autonomousFlowDiffeomorph W hW K hWlip flow hflow0 hflow (t : ℝ)
      ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
  refine ⟨Φ, flow, Ψ, hflow0, hflow, hflow_cont,
    contDiffOn_flow_unit_interval W hW K hWlip flow hflow0 hflow, ?_, ?_⟩
  · intro t x
    rfl
  · intro t x
    rw [hΦ]
    rfl

private noncomputable def timeDependentFlowDiffeomorph
    [FiniteDimensional ℝ E]
    (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V)
    (K : ℝ≥0) (hVlip : LipschitzWith K V)
    (flow : (ℝ × E) × ℝ → ℝ × E)
    (hflow0 : ∀ z, flow (z, 0) = z)
    (hflow : ∀ z t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ flow (z, u))
        (1, V (flow (z, t))) (Icc (-3) 3) t)
    (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    E ≃ₘ[ℝ] E := by
  let W : ℝ × E → ℝ × E := fun z ↦ (1, V z)
  have hW : ContDiff ℝ ∞ W := by
    fun_prop
  have hWlip : LipschitzWith K W := by
    refine LipschitzWith.of_dist_le_mul fun z z' ↦ ?_
    simpa [W, Prod.dist_eq] using hVlip.dist_le_mul z z'
  have hflowW : ∀ z u, u ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun s ↦ flow (z, s)) (W (flow (z, u)))
        (Icc (-3) 3) u := by
    simpa [W] using hflow
  have hinv := flow_inverse_on_unit_interval W K hWlip flow hflow0 hflowW
  have hfst := lifted_flow_fst V flow hflow0 hflow
  have hforward : ContDiff ℝ ∞
      (fun x : E ↦ (flow ((0, x), t)).2) := by
    have hfull := contDiff_flow_slice W hW K hWlip flow hflow0 hflowW t ht
    have hin : ContDiff ℝ ∞ (fun x : E ↦ ((0 : ℝ), x)) :=
      contDiff_const.prodMk contDiff_id
    simpa [Function.comp_def] using contDiff_snd.comp (hfull.comp hin)
  have htneg : -t ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hbackward : ContDiff ℝ ∞
      (fun x : E ↦ (flow ((t, x), -t)).2) := by
    have hfull := contDiff_flow_slice W hW K hWlip flow hflow0 hflowW (-t) htneg
    have hin : ContDiff ℝ ∞ (fun x : E ↦ (t, x)) :=
      contDiff_const.prodMk contDiff_id
    simpa [Function.comp_def] using contDiff_snd.comp (hfull.comp hin)
  refine
    { toEquiv :=
        { toFun := fun x ↦ (flow ((0, x), t)).2
          invFun := fun x ↦ (flow ((t, x), -t)).2
          left_inv := fun x ↦ ?_
          right_inv := fun x ↦ ?_ }
      contMDiff_toFun := hforward.contMDiff
      contMDiff_invFun := hbackward.contMDiff }
  · have hz : (t, (flow ((0, x), t)).2) = flow ((0, x), t) := by
      apply Prod.ext
      · simpa using (hfst (0, x) t
          ⟨by linarith [ht.1], by linarith [ht.2]⟩).symm
      · rfl
    have hi := hinv (0, x) t ht
    change (flow ((t, (flow ((0, x), t)).2), -t)).2 = x
    rw [hz]
    exact congrArg Prod.snd hi
  · have hz : (0, (flow ((t, x), -t)).2) = flow ((t, x), -t) := by
      apply Prod.ext
      · simpa using (hfst (t, x) (-t)
          ⟨by linarith [htneg.1], by linarith [htneg.2]⟩).symm
      · rfl
    have hi := hinv (t, x) (-t) htneg
    change (flow ((0, (flow ((t, x), -t)).2), t)).2 = x
    rw [hz]
    simpa using congrArg Prod.snd hi

/-- A bounded globally Lipschitz smooth time-dependent field integrates to the existing continuous
ambient isotopy together with exactly agreeing diffeomorphism slices and a jointly smooth spatial
flow on the unit slab. -/
theorem exists_ambientIsotopy_diffeomorph
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V)
    (K B : ℝ≥0) (hVlip : LipschitzWith K V)
    (hVnorm : ∀ z, ‖V z‖ ≤ B) :
    ∃ (Φ : TauCeti.AmbientIsotopy E) (eFlow : E × ℝ → E)
        (Ψ : I → E ≃ₘ[ℝ] E),
      (∀ t : I, ∀ x, Φ.toContinuousMap (t, x) = eFlow (x, (t : ℝ))) ∧
      (∀ t : I, ∀ x, Ψ t x = eFlow (x, (t : ℝ))) ∧
      ContDiffOn ℝ ∞ eFlow (univ ×ˢ Icc (-1 : ℝ) 1) ∧
      ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u ↦ eFlow (x, u)) (V (t, eFlow (x, t)))
          (Icc (-3) 3) t := by
  obtain ⟨Φ, eFlow, hΦ, heFlow⟩ := exists_ambientIsotopy V K B hVlip hVnorm
  let W : ℝ × E → ℝ × E := fun z ↦ (1, V z)
  have hW : ContDiff ℝ ∞ W := by
    fun_prop
  have hWlip : LipschitzWith K W := by
    refine LipschitzWith.of_dist_le_mul fun z z' ↦ ?_
    simpa [W, Prod.dist_eq] using hVlip.dist_le_mul z z'
  let L : ℝ≥0 := max 1 B
  have hWnorm : ∀ z, ‖W z‖ ≤ L := by
    intro z
    simp only [W, Prod.norm_mk, norm_one]
    apply max_le
    · exact_mod_cast le_max_left (1 : ℝ≥0) B
    · exact (hVnorm z).trans (by exact_mod_cast le_max_right (1 : ℝ≥0) B)
  obtain ⟨flow, hflow0, hflow, hflow_cont⟩ :=
    exists_flow_on_Icc W K L hWlip hWnorm
  have hflowV : ∀ z t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ flow (z, u))
        (1, V (flow (z, t))) (Icc (-3) 3) t := by
    simpa [W] using hflow
  have heq (x : E) : EqOn
      (fun t : ℝ ↦ (t, eFlow (x, t)))
      (fun t : ℝ ↦ flow ((0, x), t)) (Icc (-1 : ℝ) 1) := by
    let f : ℝ → ℝ × E := fun t ↦ (t, eFlow (x, t))
    let g : ℝ → ℝ × E := fun t ↦ flow ((0, x), t)
    have hsub : Icc (-1 : ℝ) 1 ⊆ Icc (-3 : ℝ) 3 := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hfderiv : ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivWithinAt f (W (f t)) (Icc (-1) 1) t := by
      intro t ht
      have he := (heFlow x t (hsub ht)).mono hsub
      simpa [f, W] using
        (hasDerivWithinAt_id t (Icc (-1 : ℝ) 1)).prodMk he
    have hgderiv : ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivWithinAt g (W (g t)) (Icc (-1) 1) t := by
      intro t ht
      exact (hflow (0, x) t (hsub ht)).mono hsub
    apply ODE_solution_unique_of_mem_Icc
      (s := fun _ ↦ univ) (K := K) (t₀ := 0)
      (fun _ _ ↦ hWlip.lipschitzOnWith)
      (by norm_num)
      (HasDerivWithinAt.continuousOn hfderiv)
    · intro t ht
      exact (hfderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    · simp
    · exact HasDerivWithinAt.continuousOn hgderiv
    · intro t ht
      exact (hgderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    · simp
    · have he0 : eFlow (x, 0) = x := (hΦ 0 x).symm.trans (Φ.map_zero_left x)
      simp [f, hflow0, he0]
  let eFull : E × ℝ → E := fun p ↦ (flow ((0, p.1), p.2)).2
  have heFullSmooth : ContDiffOn ℝ ∞ eFull (univ ×ˢ Icc (-1 : ℝ) 1) := by
    have hfullSmooth :=
      contDiffOn_flow_unit_interval W hW K hWlip flow hflow0 hflow
    let r : E × ℝ → (ℝ × E) × ℝ := fun p ↦ ((0, p.1), p.2)
    have hr : ContDiffOn ℝ ∞ r (univ ×ˢ Icc (-1 : ℝ) 1) := by
      fun_prop
    have hrange : MapsTo r (univ ×ˢ Icc (-1 : ℝ) 1)
        (univ ×ˢ Icc (-1 : ℝ) 1) := by
      intro p hp
      exact ⟨mem_univ _, hp.2⟩
    have hcomp := hfullSmooth.comp hr hrange
    have hsnd := contDiff_snd.fun_comp_contDiffOn hcomp
    simpa [eFull, r, Function.comp_def] using hsnd
  have heFlowSmooth : ContDiffOn ℝ ∞ eFlow (univ ×ˢ Icc (-1 : ℝ) 1) := by
    apply heFullSmooth.congr
    intro p hp
    exact congrArg Prod.snd (heq p.1 hp.2)
  let Ψ : I → E ≃ₘ[ℝ] E := fun t ↦
    timeDependentFlowDiffeomorph V hV K hVlip flow hflow0 hflowV (t : ℝ)
      ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
  refine ⟨Φ, eFlow, Ψ, hΦ, ?_, heFlowSmooth, heFlow⟩
  intro t x
  change (flow ((0, x), (t : ℝ))).2 = eFlow (x, (t : ℝ))
  exact congrArg Prod.snd (heq x
    ⟨by linarith [t.property.1], by linarith [t.property.2]⟩).symm

/-- A compactly supported smooth time-dependent field integrates to the existing continuous
ambient isotopy together with exactly agreeing diffeomorphism slices. -/
theorem exists_ambientIsotopy_diffeomorph_of_contDiff_hasCompactSupport
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport V) :
    ∃ (Φ : TauCeti.AmbientIsotopy E) (eFlow : E × ℝ → E)
        (Ψ : I → E ≃ₘ[ℝ] E),
      (∀ t : I, ∀ x, Φ.toContinuousMap (t, x) = eFlow (x, (t : ℝ))) ∧
      (∀ t : I, ∀ x, Ψ t x = eFlow (x, (t : ℝ))) ∧
      ContDiffOn ℝ ∞ eFlow (univ ×ˢ Icc (-1 : ℝ) 1) ∧
      ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u ↦ eFlow (x, u)) (V (t, eFlow (x, t)))
          (Icc (-3) 3) t := by
  have hVone : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  obtain ⟨K, hK⟩ := hVone.lipschitzWith_of_hasCompactSupport hcompact (by norm_num)
  obtain ⟨C, hC⟩ := hV.continuous.bounded_above_of_compact_support hcompact
  let B : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  apply exists_ambientIsotopy_diffeomorph V hV K B hK
  intro z
  exact (hC z).trans (by exact_mod_cast le_max_left C 0)

end SplittingSpheres.TimeDependentFlow

end
