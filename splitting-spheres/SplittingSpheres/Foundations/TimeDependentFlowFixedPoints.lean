/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CompactlySupportedTimeDependentFlow
public import SplittingSpheres.Foundations.AmbientIsotopyRestriction

/-!
# Fixed points of time-dependent flows

This file records the uniqueness consequence needed to localize the continuous ambient isotopy
constructed in `CompactlySupportedTimeDependentFlow`.  If the time-dependent vector field vanishes
at one spatial point throughout the buffered time interval, then the selected trajectory starting
there is the constant trajectory.  Strengthened existence theorems expose this fixed-point law
alongside the flow and its ODE.

No smoothness of the resulting ambient-isotopy slices is asserted.
-/

@[expose] public section


open Function Metric Set
open unitInterval
open scoped NNReal Topology unitInterval

noncomputable section

namespace SplittingSpheres

namespace TimeDependentFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A trajectory of a jointly Lipschitz time-dependent vector field is constant when the field
vanishes at its initial spatial point throughout the buffered time interval. -/
theorem trajectory_eq_const_of_field_eq_zero
    (V : ℝ × E → E) (K : ℝ≥0) (hVlip : LipschitzWith K V)
    (eFlow : E × ℝ → E) (x : E)
    (hflow0 : eFlow (x, 0) = x)
    (hflow : ∀ t, t ∈ Icc (-3 : ℝ) 3 →
      HasDerivWithinAt (fun u ↦ eFlow (x, u)) (V (t, eFlow (x, t)))
        (Icc (-3) 3) t)
    (hzero : ∀ t, t ∈ Icc (-3 : ℝ) 3 → V (t, x) = 0) :
    ∀ t, t ∈ Icc (-3 : ℝ) 3 → eFlow (x, t) = x := by
  have hspaceLip : ∀ t : ℝ, LipschitzWith K (fun y : E ↦ V (t, y)) := by
    intro t
    refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    simpa [Prod.dist_eq] using hVlip.dist_le_mul (t, y) (t, z)
  have heq : EqOn (fun t ↦ eFlow (x, t)) (fun _ : ℝ ↦ x) (Icc (-3 : ℝ) 3) := by
    apply ODE_solution_unique_of_mem_Icc
      (v := fun t y ↦ V (t, y)) (s := fun _ ↦ univ) (K := K) (t₀ := 0)
      (fun t _ ↦ (hspaceLip t).lipschitzOnWith)
      (by norm_num)
    · exact HasDerivWithinAt.continuousOn fun t ht ↦ hflow t ht
    · intro t ht
      exact (hflow t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    · simp
    · fun_prop
    · intro t ht
      rw [hzero t (Ioo_subset_Icc_self ht)]
      exact hasDerivAt_const t x
    · simp
    · simpa using hflow0
  exact fun t ht ↦ heq ht

/-- The bounded globally Lipschitz construction, strengthened with its exact fixed-point law on
the entire buffered interval. -/
theorem exists_ambientIsotopy_with_fixed_points
    [CompleteSpace E]
    (V : ℝ × E → E) (K B : ℝ≥0)
    (hVlip : LipschitzWith K V) (hVnorm : ∀ z, ‖V z‖ ≤ B) :
    ∃ (Φ : TauCeti.AmbientIsotopy E) (eFlow : E × ℝ → E),
      (∀ t : I, ∀ x, Φ.toContinuousMap (t, x) = eFlow (x, (t : ℝ))) ∧
      (∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u ↦ eFlow (x, u)) (V (t, eFlow (x, t)))
          (Icc (-3) 3) t) ∧
      ∀ x, (∀ t, t ∈ Icc (-3 : ℝ) 3 → V (t, x) = 0) →
        ∀ t, t ∈ Icc (-3 : ℝ) 3 → eFlow (x, t) = x := by
  obtain ⟨Φ, eFlow, happly, hflow⟩ := exists_ambientIsotopy V K B hVlip hVnorm
  refine ⟨Φ, eFlow, happly, hflow, ?_⟩
  intro x hzero
  apply trajectory_eq_const_of_field_eq_zero V K hVlip eFlow x
  · calc
      eFlow (x, 0) = Φ.toContinuousMap (0, x) := (happly 0 x).symm
      _ = x := Φ.map_zero_left x
  · exact hflow x
  · exact hzero

/-- Joint `C¹` regularity and compact support produce an ambient isotopy whose flow fixes every
point at which the vector field vanishes throughout the buffered interval. -/
theorem exists_ambientIsotopy_of_contDiff_hasCompactSupport_with_fixed_points
    [CompleteSpace E]
    (V : ℝ × E → E) (hV : ContDiff ℝ 1 V) (hcompact : HasCompactSupport V) :
    ∃ (Φ : TauCeti.AmbientIsotopy E) (eFlow : E × ℝ → E),
      (∀ t : I, ∀ x, Φ.toContinuousMap (t, x) = eFlow (x, (t : ℝ))) ∧
      (∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u ↦ eFlow (x, u)) (V (t, eFlow (x, t)))
          (Icc (-3) 3) t) ∧
      ∀ x, (∀ t, t ∈ Icc (-3 : ℝ) 3 → V (t, x) = 0) →
        ∀ t, t ∈ Icc (-3 : ℝ) 3 → eFlow (x, t) = x := by
  obtain ⟨K, hK⟩ := hV.lipschitzWith_of_hasCompactSupport hcompact (by norm_num)
  obtain ⟨C, hC⟩ := hV.continuous.bounded_above_of_compact_support hcompact
  let B : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  apply exists_ambientIsotopy_with_fixed_points V K B hK
  intro z
  exact (hC z).trans (by exact_mod_cast le_max_left C 0)

omit [NormedSpace ℝ E] in
/-- On unit time, the strengthened flow theorem fixes the same points in the packaged ambient
isotopy. -/
theorem ambientIsotopy_apply_eq_of_field_eq_zero
    (V : ℝ × E → E) (Φ : TauCeti.AmbientIsotopy E) (eFlow : E × ℝ → E)
    (happly : ∀ t : I, ∀ x, Φ.toContinuousMap (t, x) = eFlow (x, (t : ℝ)))
    (hfixed : ∀ x, (∀ t, t ∈ Icc (-3 : ℝ) 3 → V (t, x) = 0) →
      ∀ t, t ∈ Icc (-3 : ℝ) 3 → eFlow (x, t) = x)
    (x : E) (hzero : ∀ t, t ∈ Icc (-3 : ℝ) 3 → V (t, x) = 0) (t : I) :
    Φ.toContinuousMap (t, x) = x := by
  rw [happly]
  exact hfixed x hzero (t : ℝ)
    ⟨by linarith [t.property.1], by linarith [t.property.2]⟩

/-- A jointly `C¹`, compactly supported time-dependent field that vanishes outside an open set
integrates to an ambient isotopy of that open subtype.  The returned equation identifies this
restricted isotopy with the ambient ODE trajectory exactly. -/
theorem exists_restrictedAmbientIsotopy_of_contDiff_hasCompactSupport
    [CompleteSpace E]
    (U : TopologicalSpace.Opens E) (V : ℝ × E → E)
    (hV : ContDiff ℝ 1 V) (hcompact : HasCompactSupport V)
    (hzeroOutside : ∀ t : ℝ, ∀ x, x ∉ U → V (t, x) = 0) :
    ∃ (Psi : TauCeti.AmbientIsotopy U) (eFlow : E × ℝ → E),
      (∀ t : I, ∀ x : U,
        ((Psi.toContinuousMap (t, x) : U) : E) = eFlow ((x : E), (t : ℝ))) ∧
      (∀ x t, t ∈ Icc (-3 : ℝ) 3 →
        HasDerivWithinAt (fun u ↦ eFlow (x, u)) (V (t, eFlow (x, t)))
          (Icc (-3) 3) t) ∧
      ∀ t : I, ∀ x, x ∉ U → eFlow (x, (t : ℝ)) = x := by
  obtain ⟨Phi, eFlow, happly, hflow, hfixed⟩ :=
    exists_ambientIsotopy_of_contDiff_hasCompactSupport_with_fixed_points V hV hcompact
  have hPhiFixed : ∀ t : I, ∀ x, x ∉ U → Phi.toContinuousMap (t, x) = x := by
    intro t x hx
    apply ambientIsotopy_apply_eq_of_field_eq_zero V Phi eFlow happly hfixed x
    intro s _
    exact hzeroOutside s x hx
  let Psi : TauCeti.AmbientIsotopy U :=
    Phi.restrictOpensOfFixedComplement U hPhiFixed
  refine ⟨Psi, eFlow, ?_, hflow, ?_⟩
  · intro t x
    change Phi.toContinuousMap (t, (x : E)) = eFlow ((x : E), (t : ℝ))
    exact happly t x
  · intro t x hx
    apply hfixed x
    · intro s _
      exact hzeroOutside s x hx
    · exact ⟨by linarith [t.property.1], by linarith [t.property.2]⟩

end TimeDependentFlow

end SplittingSpheres
