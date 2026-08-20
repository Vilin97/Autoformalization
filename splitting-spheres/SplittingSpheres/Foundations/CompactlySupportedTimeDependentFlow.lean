/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Normed.Group.Bounded
public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Compactly supported time-dependent flows

This file turns the pinned Picard--Lindelöf existence and uniqueness theorems into a global
continuous ambient isotopy.  A bounded globally Lipschitz autonomous vector field first produces a
continuous flow on a buffered interval.  Uniqueness supplies the reverse-time inverse and hence the
homeomorphism property of the level-preserving total map.

For a time-dependent field `V : ℝ × E → E`, the autonomous lift
`(τ, x) ↦ (1, V (τ, x))` has first coordinate `τ + t`.  Projecting its flow therefore integrates
`V`.  The final theorem packages the common case in which `V` is jointly `C¹` and compactly
supported; these hypotheses imply the global boundedness and Lipschitz estimates used by the
construction.  The result is a continuous `TauCeti.AmbientIsotopy`; it does not assert smoothness of
the time slices.
-/

@[expose] public section


open Function Metric Set
open unitInterval
open scoped NNReal Topology unitInterval

noncomputable section

namespace SplittingSpheres

namespace TimeDependentFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem picardLindelof_global_three
    (W : E → E) (K L r : ℝ≥0)
    (hWlip : LipschitzWith K W) (hWnorm : ∀ x, ‖W x‖ ≤ L) (x : E) :
    IsPicardLindelof (tmin := -3) (tmax := 3) (fun _ : ℝ => W)
      (⟨0, by norm_num⟩ : Icc (-3 : ℝ) 3) x (3 * L + r) r L K where
  lipschitzOnWith _ _ := hWlip.lipschitzOnWith
  continuousOn _ _ := continuousOn_const
  norm_le _ _ y _ := hWnorm y
  mul_max_le := by
    norm_num
    rw [mul_comm]

/-- A globally bounded, globally Lipschitz autonomous vector field has trajectories on `[-3,3]`
that depend continuously on the initial point and time. -/
theorem exists_flow_on_Icc
    (W : E → E) (K L : ℝ≥0)
    (hWlip : LipschitzWith K W) (hWnorm : ∀ x, ‖W x‖ ≤ L) :
    ∃ flow : E × ℝ → E,
      (∀ x, flow (x, 0) = x) ∧
      (∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u => flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t) ∧
      ContinuousOn flow (univ ×ˢ Icc (-3 : ℝ) 3) := by
  let t0 : Icc (-3 : ℝ) 3 := ⟨0, by norm_num⟩
  have hpoint (x : E) :=
    (picardLindelof_global_three W K L 0 hWlip hWnorm x).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose curve hcurve0 hcurve using hpoint
  let flow : E × ℝ → E := fun p => curve p.1 p.2
  refine ⟨flow, ?_, ?_, ?_⟩
  · intro x
    exact hcurve0 x
  · intro x t ht
    exact hcurve x t ht
  · intro p hp
    let r : ℝ≥0 := 1
    have hlocal :=
      (picardLindelof_global_three W K L r hWlip hWnorm p.1)
        |>.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    obtain ⟨localFlow, hlocalCurve, hlocalContinuous⟩ := hlocal
    have hEq : ∀ x ∈ closedBall p.1 (r : ℝ),
        EqOn (fun t => flow (x, t)) (fun t => localFlow (x, t)) (Icc (-3 : ℝ) 3) := by
      intro x hx
      apply ODE_solution_unique_of_mem_Icc
        (s := fun _ => univ) (K := K) (t₀ := 0)
        (fun _ _ => hWlip.lipschitzOnWith)
        (by norm_num)
      · exact HasDerivWithinAt.continuousOn (fun t ht => hcurve x t ht)
      · intro t ht
        exact (hcurve x t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)
      · simp
      · exact HasDerivWithinAt.continuousOn (fun t ht => (hlocalCurve x hx).2 t ht)
      · intro t ht
        exact ((hlocalCurve x hx).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)
      · simp
      · exact (hcurve0 x).trans (hlocalCurve x hx).1.symm
    have hA : closedBall p.1 (r : ℝ) ×ˢ Icc (-3 : ℝ) 3 ∈
        𝓝[univ ×ˢ Icc (-3 : ℝ) 3] p := by
      rw [mem_nhdsWithin_prod_iff]
      refine ⟨closedBall p.1 (r : ℝ), ?_, Icc (-3 : ℝ) 3, self_mem_nhdsWithin, ?_⟩
      · exact mem_nhdsWithin_of_mem_nhds <|
          closedBall_mem_nhds p.1 (show 0 < (r : ℝ) by norm_num)
      · exact Subset.rfl
    have hEqEventually : flow =ᶠ[𝓝[univ ×ˢ Icc (-3 : ℝ) 3] p] localFlow := by
      filter_upwards [hA] with q hq
      exact hEq q.1 hq.1 hq.2
    exact (hlocalContinuous p ⟨mem_closedBall_self (by norm_num), hp.2⟩).mono_of_mem_nhdsWithin hA
      |>.congr_of_eventuallyEq_of_mem hEqEventually hp

omit [CompleteSpace E] in
/-- Reversing the time parameter undoes the selected flow on the unit time interval. -/
theorem flow_inverse_on_unit_interval
    (W : E → E) (K : ℝ≥0) (hWlip : LipschitzWith K W)
    (flow : E × ℝ → E)
    (hflow0 : ∀ x, flow (x, 0) = x)
    (hflow : ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u => flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t) :
    ∀ x t, t ∈ Icc (-1 : ℝ) 1 → flow (flow (x, t), -t) = x := by
  intro x t ht
  let f : ℝ → E := fun u => flow (flow (x, t), u)
  let g : ℝ → E := fun u => flow (x, t + u)
  have hsmall : Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ) ⊆ Icc (-3 : ℝ) 3 := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hshift : MapsTo (fun u : ℝ => t + u) (Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ))
      (Icc (-3 : ℝ) 3) := by
    intro u hu
    constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
  have hf_cont : ContinuousOn f (Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ)) := by
    exact HasDerivWithinAt.continuousOn fun u hu =>
      (hflow (flow (x, t)) u (hsmall hu)).mono hsmall
  have hg_cont : ContinuousOn g (Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ)) := by
    have hc : ContinuousOn (fun s => flow (x, s)) (Icc (-3 : ℝ) 3) :=
      HasDerivWithinAt.continuousOn (fun s hs => hflow x s hs)
    exact hc.comp (by fun_prop) hshift
  have heq : EqOn f g (Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ)) := by
    apply ODE_solution_unique_of_mem_Icc
      (s := fun _ => univ) (K := K) (t₀ := 0)
      (fun _ _ => hWlip.lipschitzOnWith)
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
      have hd' : HasDerivAt (fun s => flow (x, s)) (W (flow (x, u + t))) (u + t) := by
        simpa [add_comm] using hd
      simpa [g, add_comm] using hd'.comp_add_const u t
    · simp
    · simp [f, g, hflow0]
  have hneg : -t ∈ Icc (-(3 / 2 : ℝ)) (3 / 2 : ℝ) := by
    constructor <;> linarith [ht.1, ht.2]
  have := heq hneg
  simpa [f, g, hflow0] using this

/-- The bounded globally Lipschitz autonomous flow bundles as a genuine ambient isotopy. -/
theorem exists_ambientIsotopy_autonomous
    (W : E → E) (K L : ℝ≥0)
    (hWlip : LipschitzWith K W) (hWnorm : ∀ x, ‖W x‖ ≤ L) :
    ∃ (Φ : TauCeti.AmbientIsotopy E) (flow : E × ℝ → E),
      (∀ x, flow (x, 0) = x) ∧
      (∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u => flow (x, u)) (W (flow (x, t))) (Icc (-3) 3) t) ∧
      ContinuousOn flow (univ ×ˢ Icc (-3 : ℝ) 3) ∧
      ∀ t : I, ∀ x, Φ.toContinuousMap (t, x) = flow (x, (t : ℝ)) := by
  obtain ⟨flow, hflow0, hflow, hflow_cont⟩ := exists_flow_on_Icc W K L hWlip hWnorm
  have hflow_inv := flow_inverse_on_unit_interval W K hWlip flow hflow0 hflow
  have hforward : Continuous (fun p : I × E => flow (p.2, (p.1 : ℝ))) := by
    rw [← continuousOn_univ]
    apply hflow_cont.comp (by fun_prop)
    intro p _
    exact ⟨mem_univ _, ⟨by linarith [p.1.property.1], by linarith [p.1.property.2]⟩⟩
  have hbackward : Continuous (fun p : I × E => flow (p.2, -(p.1 : ℝ))) := by
    rw [← continuousOn_univ]
    apply hflow_cont.comp (by fun_prop)
    intro p _
    exact ⟨mem_univ _, ⟨by linarith [p.1.property.2], by linarith [p.1.property.1]⟩⟩
  let Φ : TauCeti.AmbientIsotopy E :=
    { toContinuousMap := ⟨fun p => flow (p.2, (p.1 : ℝ)), hforward⟩
      isHomeomorph_total' := by
        rw [isHomeomorph_iff_exists_inverse]
        refine ⟨continuous_fst.prodMk hforward,
          fun p : I × E => (p.1, flow (p.2, -(p.1 : ℝ))), ?_, ?_,
          continuous_fst.prodMk hbackward⟩
        · intro p
          apply Prod.ext
          · rfl
          · exact hflow_inv p.2 (p.1 : ℝ)
              ⟨by linarith [p.1.property.1], by linarith [p.1.property.2]⟩
        · intro p
          apply Prod.ext
          · rfl
          · simpa using hflow_inv p.2 (-(p.1 : ℝ))
              ⟨by linarith [p.1.property.2], by linarith [p.1.property.1]⟩
      map_zero_left' := hflow0 }
  exact ⟨Φ, flow, hflow0, hflow, hflow_cont, fun _ _ => rfl⟩

omit [CompleteSpace E] in
/-- The first coordinate of the autonomous lift advances by elapsed time. -/
theorem lifted_flow_fst
    (V : ℝ × E → E) (flow : (ℝ × E) × ℝ → ℝ × E)
    (hflow0 : ∀ z, flow (z, 0) = z)
    (hflow : ∀ z t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u => flow (z, u)) (1, V (flow (z, t))) (Icc (-3) 3) t) :
    ∀ z t, t ∈ Icc (-3 : ℝ) 3 → (flow (z, t)).1 = z.1 + t := by
  intro z
  have hfst : ∀ t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u => (flow (z, u)).1) 1 (Icc (-3) 3) t := by
    intro t ht
    simpa using (hflow z t ht).hasFDerivWithinAt.fst.hasDerivWithinAt
  have heq : EqOn (fun t => (flow (z, t)).1) (fun t => z.1 + t) (Icc (-3 : ℝ) 3) := by
    apply ODE_solution_unique_of_mem_Icc
      (v := fun _ _ : ℝ => 1) (s := fun _ => univ) (K := 0) (t₀ := 0)
      (fun _ _ => LipschitzWith.const 1 |>.lipschitzOnWith)
      (by norm_num)
    · exact HasDerivWithinAt.continuousOn hfst
    · intro t ht
      exact (hfst t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · simp
    · fun_prop
    · intro t _
      simpa using (hasDerivAt_id t).const_add z.1
    · simp
    · simpa using congrArg Prod.fst (hflow0 z)
  exact fun t ht => heq ht

/-- A jointly globally Lipschitz and globally bounded time-dependent vector field integrates to
a genuine ambient isotopy, via the autonomous lift `(tau, x)' = (1, V (tau, x))`. -/
theorem exists_ambientIsotopy
    (V : ℝ × E → E) (K B : ℝ≥0)
    (hVlip : LipschitzWith K V) (hVnorm : ∀ z, ‖V z‖ ≤ B) :
    ∃ (Φ : TauCeti.AmbientIsotopy E) (eFlow : E × ℝ → E),
      (∀ t : I, ∀ x, Φ.toContinuousMap (t, x) = eFlow (x, (t : ℝ))) ∧
      ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u => eFlow (x, u)) (V (t, eFlow (x, t)))
          (Icc (-3) 3) t := by
  let W : ℝ × E → ℝ × E := fun z => (1, V z)
  have hWlip : LipschitzWith K W := by
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    simpa [W, Prod.dist_eq] using hVlip.dist_le_mul z z'
  let L : ℝ≥0 := max 1 B
  have hWnorm : ∀ z, ‖W z‖ ≤ L := by
    intro z
    simp only [W, Prod.norm_mk, norm_one]
    apply max_le
    · exact_mod_cast le_max_left (1 : ℝ≥0) B
    · exact (hVnorm z).trans (by exact_mod_cast le_max_right (1 : ℝ≥0) B)
  obtain ⟨flow, hflow0, hflow, hflow_cont⟩ := exists_flow_on_Icc W K L hWlip hWnorm
  have hflow_inv := flow_inverse_on_unit_interval W K hWlip flow hflow0 hflow
  have hflow_fst : ∀ z t, t ∈ Icc (-3 : ℝ) 3 → (flow (z, t)).1 = z.1 + t := by
    apply lifted_flow_fst V flow hflow0
    simpa [W] using hflow
  let eFlow : E × ℝ → E := fun p => (flow ((0, p.1), p.2)).2
  have hforwardF : Continuous (fun p : I × E => flow ((0, p.2), (p.1 : ℝ))) := by
    rw [← continuousOn_univ]
    apply hflow_cont.comp (by fun_prop)
    intro p _
    exact ⟨mem_univ _, ⟨by linarith [p.1.property.1], by linarith [p.1.property.2]⟩⟩
  have hforward : Continuous (fun p : I × E => eFlow (p.2, (p.1 : ℝ))) := by
    exact continuous_snd.comp hforwardF
  have hbackwardF :
      Continuous (fun p : I × E => flow (((p.1 : ℝ), p.2), -(p.1 : ℝ))) := by
    rw [← continuousOn_univ]
    apply hflow_cont.comp (by fun_prop)
    intro p _
    exact ⟨mem_univ _, ⟨by linarith [p.1.property.2], by linarith [p.1.property.1]⟩⟩
  have hbackward :
      Continuous (fun p : I × E => (flow (((p.1 : ℝ), p.2), -(p.1 : ℝ))).2) := by
    exact continuous_snd.comp hbackwardF
  let Φ : TauCeti.AmbientIsotopy E :=
    { toContinuousMap := ⟨fun p => eFlow (p.2, (p.1 : ℝ)), hforward⟩
      isHomeomorph_total' := by
        rw [isHomeomorph_iff_exists_inverse]
        refine ⟨continuous_fst.prodMk hforward,
          fun p : I × E => (p.1, (flow (((p.1 : ℝ), p.2), -(p.1 : ℝ))).2),
          ?_, ?_, continuous_fst.prodMk hbackward⟩
        · intro p
          apply Prod.ext
          · rfl
          · have ht : (p.1 : ℝ) ∈ Icc (-1 : ℝ) 1 :=
              ⟨by linarith [p.1.property.1], by linarith [p.1.property.2]⟩
            have hz : ((p.1 : ℝ), eFlow (p.2, (p.1 : ℝ))) =
                flow ((0, p.2), (p.1 : ℝ)) := by
              apply Prod.ext
              · simpa [eFlow] using (hflow_fst (0, p.2) (p.1 : ℝ)
                  ⟨by linarith [p.1.property.1], by linarith [p.1.property.2]⟩).symm
              · rfl
            have hi := hflow_inv (0, p.2) (p.1 : ℝ) ht
            change (flow (((p.1 : ℝ), eFlow (p.2, (p.1 : ℝ))), -(p.1 : ℝ))).2 = p.2
            rw [hz]
            exact congrArg Prod.snd hi
        · intro p
          apply Prod.ext
          · rfl
          · have ht : -(p.1 : ℝ) ∈ Icc (-1 : ℝ) 1 :=
              ⟨by linarith [p.1.property.2], by linarith [p.1.property.1]⟩
            have hz : (0, (flow (((p.1 : ℝ), p.2), -(p.1 : ℝ))).2) =
                flow (((p.1 : ℝ), p.2), -(p.1 : ℝ)) := by
              apply Prod.ext
              · simpa using (hflow_fst ((p.1 : ℝ), p.2) (-(p.1 : ℝ))
                  ⟨by linarith [p.1.property.2], by linarith [p.1.property.1]⟩).symm
              · rfl
            have hi := hflow_inv ((p.1 : ℝ), p.2) (-(p.1 : ℝ)) ht
            change (flow ((0, (flow (((p.1 : ℝ), p.2), -(p.1 : ℝ))).2),
              (p.1 : ℝ))).2 = p.2
            rw [hz]
            simpa using congrArg Prod.snd hi
      map_zero_left' := by
        intro x
        exact congrArg Prod.snd (hflow0 (0, x)) }
  refine ⟨Φ, eFlow, fun _ _ => rfl, ?_⟩
  intro x t ht
  have hz : flow ((0, x), t) = (t, eFlow (x, t)) := by
    apply Prod.ext
    · simpa using hflow_fst (0, x) t ht
    · rfl
  have hd := (hflow (0, x) t ht).hasFDerivWithinAt.snd.hasDerivWithinAt
  have hd' : HasDerivWithinAt (fun u => eFlow (x, u)) (V (flow ((0, x), t)))
      (Icc (-3) 3) t := by
    simpa [W, eFlow] using hd
  rw [hz] at hd'
  exact hd'

/-- In particular, joint `C^1` regularity plus compact support supplies the global boundedness and
global Lipschitz hypotheses needed above. -/
theorem exists_ambientIsotopy_of_contDiff_hasCompactSupport
    (V : ℝ × E → E) (hV : ContDiff ℝ 1 V) (hcompact : HasCompactSupport V) :
    ∃ (Φ : TauCeti.AmbientIsotopy E) (eFlow : E × ℝ → E),
      (∀ t : I, ∀ x, Φ.toContinuousMap (t, x) = eFlow (x, (t : ℝ))) ∧
      ∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u => eFlow (x, u)) (V (t, eFlow (x, t)))
          (Icc (-3) 3) t := by
  obtain ⟨K, hK⟩ := hV.lipschitzWith_of_hasCompactSupport hcompact (by norm_num)
  obtain ⟨C, hC⟩ := hV.continuous.bounded_above_of_compact_support hcompact
  let B : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  apply exists_ambientIsotopy V K B hK
  intro z
  exact (hC z).trans (by exact_mod_cast le_max_left C 0)

end TimeDependentFlow

end SplittingSpheres
