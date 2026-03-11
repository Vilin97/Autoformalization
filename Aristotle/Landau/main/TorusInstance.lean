import Aristotle.Landau.main.TorusDefs

/-!
# FlatTorus3 Instance for T^3

Proves the remaining `FlatTorus3` axioms (integration by parts, harmonic implies
constant, Laplacian maximum principle, Killing implies harmonic, curl-div implies
harmonic) and assembles the full `FlatTorus3` instance on `Fin 3 -> AddCircle 1`.
-/

open MeasureTheory Matrix Finset BigOperators Real Filter

noncomputable section

-- ============================================================================
-- Box integral machinery (proved by Aristotle)
-- ============================================================================

section AristotleLemmas
open intervalIntegral

def box3 : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ => Set.Ioc 0 1)

/-- The volume measure on T³ is the pushforward of the box measure. -/
lemma measure_torus_eq_map :
    (volume : Measure Torus3) =
    (volume.restrict box3).map torusMk := by
      have h_volume_eq : MeasureTheory.MeasureSpace.volume = MeasureTheory.Measure.map torusMk (MeasureTheory.Measure.pi (fun _ => MeasureTheory.MeasureSpace.volume.restrict (Set.Ioc 0 1))) := by
        have h_volume_eq : ∀ i : Fin 3,
            (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioc 0 1)).map
              (fun x => QuotientAddGroup.mk x : ℝ → AddCircle (1 : ℝ)) =
            MeasureTheory.MeasureSpace.volume := by
          intro i
          symm
          convert (AddCircle.measurePreserving_mk 1 (0 : ℝ) |> MeasureTheory.MeasurePreserving.map_eq) using 1
          · ext s hs
            rw [ MeasureTheory.Measure.map_apply ]
            · rw [ MeasureTheory.Measure.restrict_apply' ]
              · exact AddCircle.add_projection_respects_measure 1 0 hs
              · norm_num
            · exact fun ⦃t⦄ a ↦ a
            · exact hs
          · convert (AddCircle.measurePreserving_mk 1 (0 : ℝ) |> MeasureTheory.MeasurePreserving.map_eq) using 1
            norm_num +zetaDelta at *
        convert MeasureTheory.Measure.pi_map_pi _ using 1
        any_goals tauto
        any_goals exact fun i => MeasureTheory.MeasureSpace.volume
        all_goals try infer_instance
        · exact Eq.symm Measure.map_id'
        · convert MeasureTheory.Measure.pi_map_pi (fun i => _) using 1
          · aesop
          · exact fun i ↦ sigmaFinite_of_locallyFinite
          · exact Continuous.aemeasurable (by continuity)
        · exact fun i => measurable_id.aemeasurable
      erw [ MeasureTheory.Measure.pi_eq ] at h_volume_eq
      convert h_volume_eq
      intro s hs; erw [ MeasureTheory.Measure.restrict_apply ]
      · erw [ show (Set.univ.pi s ∩ box3 : Set (Fin 3 → ℝ) ) = Set.pi Set.univ fun i => s i ∩ Set.Ioc 0 1 from ?_, MeasureTheory.Measure.pi_pi ] ; aesop
        unfold box3; aesop
      · exact MeasurableSet.univ_pi hs

/-- ∫ over T³ = ∫ over [0,1]³ of the periodic lift. -/
lemma integral_torus_eq_integral_box (g : Torus3 → ℝ) (hg : Continuous g) :
    ∫ x : Torus3, g x = ∫ y in box3, g (torusMk y) := by
      rw [ ← MeasureTheory.integral_map ]
      · convert MeasureTheory.integral_map _ _ using 3
        · rw [ ← MeasureTheory.integral_map ]
          · rw [ ← measure_torus_eq_map ]
          · refine Continuous.aemeasurable ?_
            exact continuous_pi_iff.mpr fun i => QuotientAddGroup.continuous_mk.comp (continuous_apply i)
          · exact hg.aestronglyMeasurable
        · exact measurable_id.aemeasurable
        · exact hg.aestronglyMeasurable
      · exact measurable_id.aemeasurable
      · exact hg.aestronglyMeasurable

/-- ∫ ∂F/∂xᵢ over [0,1]³ = 0 for periodic F (FTC + periodicity). -/
lemma integral_derivative_periodic_zero (F : (Fin 3 → ℝ) → ℝ) (i : Fin 3)
    (hF : ContDiff ℝ 1 F) (hper : ∀ x, F (x + Pi.single i 1) = F x) :
    ∫ y in box3, fderiv ℝ F y (Pi.single i 1) = 0 := by
      have h_periodic : ∀ x : Fin 3 → ℝ, (F (x + Pi.single i 1)) = (F x) := by
        assumption
      have h_fubini : ∀ (g : (Fin 3 → ℝ) → ℝ), Continuous g →
          (∫ y in (Set.pi Set.univ (fun _ => Set.Ioc 0 1)), g y) =
          (∫ y : ℝ in Set.Ioc 0 1,
            ∫ z : Fin 2 → ℝ in (Set.pi Set.univ (fun _ => Set.Ioc 0 1)),
              g (Fin.insertNth i y z)) := by
        intro g hg
        have h_fubini :
            ∫ y : Fin 3 → ℝ in (Set.pi Set.univ (fun _ => Set.Ioc 0 1)), g y =
            ∫ y : ℝ × (Fin 2 → ℝ) in
              (Set.Ioc 0 1) ×ˢ (Set.pi Set.univ (fun _ => Set.Ioc 0 1)),
              g (Fin.insertNth i y.1 y.2) := by
          rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ]
          · have h_iso :
                (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) =
                MeasureTheory.Measure.map
                  (fun x : ℝ × (Fin 2 → ℝ) => Fin.insertNth i x.1 x.2)
                  (MeasureTheory.volume.prod
                    (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → ℝ))) := by
              simp +decide [ MeasureTheory.MeasureSpace.volume ]
              erw [ MeasureTheory.Measure.pi_eq ]
              intro s hs; erw [ MeasureTheory.Measure.map_apply ]
              · rw [ show (fun x : ℝ × (Fin 2 → ℝ) => i.insertNth x.1 x.2) ⁻¹' Set.univ.pi s = (s i) ×ˢ (Set.pi Set.univ fun j => s (Fin.succAbove i j) ) from ?_ ]
                · simp +decide [ Fin.prod_univ_three, MeasureTheory.Measure.prod_prod ]
                  fin_cases i <;> ring!
                · ext ⟨x, y⟩; simp [Fin.insertNth]
                  fin_cases i <;> simp +decide [ Fin.forall_fin_succ ]
                  · tauto
                  · tauto
              · refine measurable_pi_iff.mpr ?_
                intro a; fin_cases a <;> simp +decide [ Fin.insertNth ]
                · fin_cases i <;> simp +decide [ Fin.succAboveCases ]
                  · exact measurable_fst
                  · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
                  · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
                · fin_cases i <;> simp +decide [ Fin.succAboveCases ] <;> measurability
                · fin_cases i <;> simp +decide [ Fin.succAboveCases ]
                  · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
                  · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
                  · exact measurable_fst
              · exact MeasurableSet.univ_pi hs
            rw [ h_iso, MeasureTheory.integral_map ]
            · simp +decide [ Set.indicator ]
              fin_cases i <;> simp +decide [ Fin.forall_fin_succ ]
              · rfl
              · simp +decide only [and_left_comm]
                rfl
              · simp +decide [ Fin.insertNth ]
                simp +decide [ Fin.succAboveCases ] ; congr ; ext ; split_ifs <;> tauto
            · refine Measurable.aemeasurable ?_
              refine measurable_pi_iff.mpr ?_
              intro a; fin_cases a <;> simp +decide [ Fin.insertNth ]
              · fin_cases i <;> simp +decide [ Fin.succAboveCases ]
                · exact measurable_fst
                · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
                · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
              · fin_cases i <;> simp +decide [ Fin.succAboveCases ]
                · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
                · exact measurable_fst
                · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
              · fin_cases i <;> simp +decide [ Fin.succAboveCases ]
                · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
                · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
                · exact measurable_fst
            · refine Measurable.aestronglyMeasurable ?_
              exact Measurable.indicator (hg.measurable) (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
          · exact measurableSet_Ioc.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
          · exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc
        erw [ h_fubini, MeasureTheory.setIntegral_prod ]
        have h_integrable : ContinuousOn (fun y : ℝ × (Fin 2 → ℝ) => g (Fin.insertNth i y.1 y.2)) (Set.Icc 0 1 ×ˢ Set.pi Set.univ (fun _ => Set.Icc 0 1)) := by
          refine hg.comp_continuousOn ?_
          refine Continuous.continuousOn ?_
          fin_cases i <;> simp +decide [ Fin.insertNth ]
          · exact continuous_pi_iff.mpr fun i => by
              fin_cases i <;>
              [ exact continuous_fst
              ; exact continuous_apply 0 |> Continuous.comp <| continuous_snd
              ; exact continuous_apply 1 |> Continuous.comp <| continuous_snd ]
          · refine continuous_pi_iff.mpr ?_
            intro i; fin_cases i <;> simp +decide [ Fin.insertNth ]
            · exact continuous_apply 0 |> Continuous.comp <| continuous_snd
            · exact continuous_fst
            · exact continuous_apply 1 |> Continuous.comp <| continuous_snd
          · exact continuous_pi_iff.mpr fun i => by
              fin_cases i <;>
              [ exact continuous_pi_iff.mp continuous_snd 0
              ; exact continuous_pi_iff.mp continuous_snd 1
              ; exact continuous_fst ]
        exact (h_integrable.integrableOn_compact
            (isCompact_Icc.prod (isCompact_univ_pi fun _ => CompactIccSpace.isCompact_Icc)))
          |> fun h => h.mono_set
            (Set.prod_mono (Set.Ioc_subset_Icc_self)
              (Set.pi_mono fun _ _ => Set.Ioc_subset_Icc_self))
      have h_ftc : ∀ (z : Fin 2 → ℝ), ∫ y in Set.Ioc 0 1, (fderiv ℝ F (Fin.insertNth i y z)) (Pi.single i 1) = 0 := by
        intro z
        have h_ftc : ∫ y in (0 : ℝ)..1, (fderiv ℝ F (Fin.insertNth i y z)) (Pi.single i 1) = F (Fin.insertNth i 1 z) - F (Fin.insertNth i 0 z) := by
          rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ]
          rotate_right
          use fun x => F (Fin.insertNth i x z)
          · rfl
          · intro x hx
            convert HasFDerivAt.hasDerivAt (HasFDerivAt.comp x (hF.contDiffAt.differentiableAt le_rfl |> DifferentiableAt.hasFDerivAt) (hasFDerivAt_pi.mpr _) ) using 1
            rotate_left
            use fun j => if j = i then 1 else 0
            · intro j; split_ifs <;> simp_all +decide [ hasFDerivAt_iff_isLittleO_nhds_zero ]
              simp_all +decide [ Fin.insertNth ]
              fin_cases i <;> fin_cases j <;> simp_all +decide [ Fin.succAboveCases ]
            · simp +decide [ Pi.single_apply ]
              congr ; ext j ; aesop
          · apply_rules [ Continuous.intervalIntegrable ]
            have h_cont : Continuous (fun y => fderiv ℝ F (Fin.insertNth i y z)) := by
              exact hF.continuous_fderiv le_rfl |> Continuous.comp <| continuous_pi_iff.mpr fun j => by fin_cases i <;> fin_cases j <;> continuity
            exact h_cont.clm_apply continuous_const
        convert h_ftc using 1 <;> norm_num [ intervalIntegral.integral_of_le zero_le_one ]
        rw [ eq_comm, sub_eq_zero ]
        convert h_periodic (Fin.insertNth i 0 z) using 2 ; ext j ; fin_cases i <;> fin_cases j <;> simp +decide [ Fin.insertNth ]
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      convert h_fubini _ _ using 1
      · rw [ MeasureTheory.integral_integral_swap ]
        · aesop
        · have h_cont : Continuous (fun p : ℝ × (Fin 2 → ℝ) => (fderiv ℝ F (i.insertNth p.1 p.2)) (Pi.single i 1)) := by
            have h_cont : Continuous (fun p : ℝ × (Fin 2 → ℝ) => fderiv ℝ F (i.insertNth p.1 p.2)) := by
              have h_cont : Continuous (fun p : Fin 3 → ℝ => fderiv ℝ F p) := by
                exact hF.continuous_fderiv le_rfl
              refine h_cont.comp ?_
              refine continuous_pi_iff.mpr ?_
              intro j; fin_cases j <;> simp +decide [ Fin.insertNth ]
              · fin_cases i <;> simp +decide [ Fin.succAboveCases ]
                · exact continuous_fst
                · exact continuous_apply 0 |> Continuous.comp <| continuous_snd
                · exact continuous_apply 0 |> Continuous.comp <| continuous_snd
              · fin_cases i <;> simp +decide [ Fin.succAboveCases ]
                · exact continuous_apply 0 |> Continuous.comp <| continuous_snd
                · exact continuous_fst
                · exact continuous_apply _ |> Continuous.comp <| continuous_snd
              · fin_cases i <;> simp +decide [ Fin.succAboveCases ]
                · exact continuous_apply _ |> Continuous.comp <| continuous_snd
                · exact continuous_apply _ |> Continuous.comp <| continuous_snd
                · exact continuous_fst
            exact Continuous.eval_const h_cont (Pi.single i 1)
          rw [ MeasureTheory.Measure.prod_restrict ]
          exact ContinuousOn.integrableOn_compact
              (isCompact_Icc.prod (isCompact_univ_pi fun _ => CompactIccSpace.isCompact_Icc))
              (h_cont.continuousOn)
            |> fun h => h.mono_set
              (Set.prod_mono (Set.Ioc_subset_Icc_self)
                (Set.pi_mono fun _ _ => Set.Ioc_subset_Icc_self))
      · fun_prop (disch := norm_num)

end AristotleLemmas

-- ============================================================================
-- IBP and Stokes axioms
-- ============================================================================

/-- ∫ torusGradX f x i = 0 on T³ (FTC + periodicity on the box). Proved by Aristotle. -/
lemma torus_gradX_integral_zero (f : Torus3 → ℝ) (i : Fin 3)
    (hf : ContDiff ℝ 1 (periodicLift f)) :
    ∫ x : Torus3, torusGradX f x i = 0 := by
  convert integral_derivative_periodic_zero (periodicLift f) i hf _ using 1
  · convert integral_torus_eq_integral_box (fun x => torusGradX f x i)
      (continuous_torusGradX f i hf) using 1
    congr! 2; exact (periodicLift_torusGradX f i _).symm
  · exact fun y => periodicLift_periodic f y i

/-- Product rule: ∂(φψ)/∂xᵢ = φ · ∂ψ/∂xᵢ + ψ · ∂φ/∂xᵢ. Proved by Aristotle. -/
lemma torusGradX_mul (φ ψ : Torus3 → ℝ) (i : Fin 3)
    (hφ : Differentiable ℝ (periodicLift φ))
    (hψ : Differentiable ℝ (periodicLift ψ)) :
    ∀ x : Torus3, torusGradX (fun z => φ z * ψ z) x i =
      φ x * torusGradX ψ x i + ψ x * torusGradX φ x i := by
  intro x
  simp only [torusGradX]
  have hlift : periodicLift (fun z => φ z * ψ z) = periodicLift φ * periodicLift ψ := by
    ext y; simp [periodicLift, Pi.mul_apply]
  rw [hlift]
  let x₀ := (torusMk_surjective x).choose
  have hx₀ := (torusMk_surjective x).choose_spec
  rw [fderiv_mul hφ.differentiableAt hψ.differentiableAt]
  simp only [ContinuousLinearMap.add_apply, periodicLift, Function.comp_apply]
  rw [show torusMk x₀ = x from hx₀]
  simp [smul_eq_mul]

private lemma integrable_mul_torusGradX (φ ψ : Torus3 → ℝ) (i : Fin 3)
    (hφ : ContDiff ℝ 1 (periodicLift φ)) (hψ : ContDiff ℝ 1 (periodicLift ψ)) :
    Integrable (fun x => φ x * torusGradX ψ x i) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff.mpr hφ.continuous).mul
      (continuous_torusGradX ψ i hψ)
  · exact HasCompactSupport.of_compactSpace _

/-- IBP on T³: ∫ φ · ∂ψ/∂xᵢ = -∫ ψ · ∂φ/∂xᵢ. Proved by Aristotle. -/
theorem torus_hIBP_spatial (φ ψ : Torus3 → ℝ) (i : Fin 3)
    (hφ : ContDiff ℝ 1 (periodicLift φ)) (hψ : ContDiff ℝ 1 (periodicLift ψ)) :
    (∫ x, φ x * torusGradX ψ x i) = -(∫ x, ψ x * torusGradX φ x i) := by
  have hprod : ∫ x : Torus3, torusGradX (fun z => φ z * ψ z) x i =
    (∫ x : Torus3, φ x * torusGradX ψ x i) + ∫ x : Torus3, ψ x * torusGradX φ x i := by
    simp_rw [torusGradX_mul φ ψ i (hφ.differentiable le_rfl) (hψ.differentiable le_rfl)]
    exact integral_add (integrable_mul_torusGradX φ ψ i hφ hψ)
      (integrable_mul_torusGradX ψ φ i hψ hφ)
  have hzero : ∫ x : Torus3, torusGradX (fun z => φ z * ψ z) x i = 0 := by
    apply torus_gradX_integral_zero
    have : periodicLift (fun z => φ z * ψ z) = fun y => periodicLift φ y * periodicLift ψ y := by
      ext y; simp [periodicLift]
    rw [this]; exact hφ.mul hψ
  linarith [hprod ▸ hzero]

/-- ∫ u · (∇×F) = 0 on T³. Each gradient integral vanishes by periodicity. -/
theorem torus_hCurlIntZero (F : Torus3 → Fin 3 → ℝ) (u : Fin 3 → ℝ)
    (hF_diff : ∀ j, ContDiff ℝ 1 (periodicLift (fun x => F x j))) :
    ∫ x, dotProduct u (torusCurlX F x) = 0 := by
  have hzero := fun j i => torus_gradX_integral_zero (fun z => F z j) i (hF_diff j)
  have hint : ∀ j i, Integrable (fun x : Torus3 => torusGradX (fun z => F z j) x i) :=
    fun j i => (continuous_torusGradX (fun z => F z j) i (hF_diff j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- Key: torusCurlX F x k = torusGradX difference (by rfl, same choose)
  have hcurl0 : ∀ x, torusCurlX F x 0 =
      torusGradX (fun z => F z 2) x 1 - torusGradX (fun z => F z 1) x 2 := fun _ => rfl
  have hcurl1 : ∀ x, torusCurlX F x 1 =
      torusGradX (fun z => F z 0) x 2 - torusGradX (fun z => F z 2) x 0 := fun _ => rfl
  have hcurl2 : ∀ x, torusCurlX F x 2 =
      torusGradX (fun z => F z 1) x 0 - torusGradX (fun z => F z 0) x 1 := fun _ => rfl
  -- Rewrite integrand
  have key : (fun x => dotProduct u (torusCurlX F x)) = fun x =>
      u 0 * (torusGradX (fun z => F z 2) x 1 - torusGradX (fun z => F z 1) x 2) +
      (u 1 * (torusGradX (fun z => F z 0) x 2 - torusGradX (fun z => F z 2) x 0) +
       u 2 * (torusGradX (fun z => F z 1) x 0 - torusGradX (fun z => F z 0) x 1)) := by
    ext x; simp only [dotProduct, Fin.sum_univ_three, hcurl0, hcurl1, hcurl2]; ring
  rw [key]
  have h₀ : ∫ x : Torus3, u 0 * (torusGradX (fun z => F z 2) x 1 -
      torusGradX (fun z => F z 1) x 2) = 0 := by
    rw [integral_mul_left, integral_sub (hint 2 1) (hint 1 2),
        hzero 2 1, hzero 1 2, sub_self, mul_zero]
  have h₁ : ∫ x : Torus3, u 1 * (torusGradX (fun z => F z 0) x 2 -
      torusGradX (fun z => F z 2) x 0) = 0 := by
    rw [integral_mul_left, integral_sub (hint 0 2) (hint 2 0),
        hzero 0 2, hzero 2 0, sub_self, mul_zero]
  have h₂ : ∫ x : Torus3, u 2 * (torusGradX (fun z => F z 1) x 0 -
      torusGradX (fun z => F z 0) x 1) = 0 := by
    rw [integral_mul_left, integral_sub (hint 1 0) (hint 0 1),
        hzero 1 0, hzero 0 1, sub_self, mul_zero]
  have hA := (hint 2 1).sub (hint 1 2) |>.const_mul (u 0)
  have hB := (hint 0 2).sub (hint 2 0) |>.const_mul (u 1)
  have hC := (hint 1 0).sub (hint 0 1) |>.const_mul (u 2)
  refine (integral_add hA (hB.add hC)).trans ?_
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [h₀, zero_add]
  refine (integral_add hB hC).trans ?_
  simp only [Pi.sub_apply]
  rw [h₁, h₂, add_zero]

/-- Harmonic → constant on T³. Energy method using IBP. -/
theorem torus_hHarmonic_const (φ : Torus3 → ℝ)
    (hd : ContDiff ℝ ⊤ (periodicLift φ))
    (hharmonic : ∀ x, torusDivX (torusGradX φ) x = 0) :
    ∀ x y, φ x = φ y := by
  -- Smoothness of gradient components (C¹ suffices for IBP)
  have hgrad_pl : ∀ i, periodicLift (fun x => torusGradX φ x i) =
      fun y => fderiv ℝ (periodicLift φ) y (Pi.single i 1) :=
    fun i => funext (periodicLift_torusGradX φ i)
  have hgrad_c1 : ∀ i, ContDiff ℝ 1 (periodicLift (fun x => torusGradX φ x i)) := by
    intro i; rw [hgrad_pl]; exact ((hd.fderiv_right le_top).clm_apply contDiff_const).of_le le_top
  have hφ_cont : Continuous φ :=
    isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff.mpr hd.continuous
  -- IBP: ∫ (∂φ/∂xᵢ)² = -∫ φ·∂²φ/∂xᵢ²
  have hIBP_i : ∀ i, ∫ x : Torus3, torusGradX φ x i * torusGradX φ x i =
      -(∫ x : Torus3, φ x * torusGradX (fun y => torusGradX φ y i) x i) :=
    fun i => torus_hIBP_spatial (fun y => torusGradX φ y i) φ i (hgrad_c1 i) (hd.of_le le_top)
  -- Each φ * ∂²φ/∂xᵢ² is integrable (continuous on compact)
  have hint : ∀ i, Integrable (fun x : Torus3 =>
      φ x * torusGradX (fun y => torusGradX φ y i) x i) :=
    fun i => (hφ_cont.mul (continuous_torusGradX _ i (hgrad_c1 i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- ∑ᵢ ∫ (∂φ/∂xᵢ)² = 0 via harmonicity
  have hsum_zero : ∑ i : Fin 3, ∫ x : Torus3, torusGradX φ x i * torusGradX φ x i = 0 := by
    simp_rw [hIBP_i]
    rw [Finset.sum_neg_distrib, neg_eq_zero,
      ← integral_finset_sum _ (fun i _ => hint i)]
    simp_rw [← Finset.mul_sum]
    simp_rw [show ∀ x, ∑ i : Fin 3, torusGradX (fun y => torusGradX φ y i) x i =
        torusDivX (torusGradX φ) x from fun _ => rfl, hharmonic, mul_zero, integral_zero]
  -- Each ∫ (∂φ/∂xᵢ)² = 0 (nonneg + sum = 0)
  have h_nonneg : ∀ i, 0 ≤ ∫ x : Torus3, torusGradX φ x i * torusGradX φ x i :=
    fun i => integral_nonneg (fun x => mul_self_nonneg _)
  have hgrad_sq_zero : ∀ i, ∫ x : Torus3, torusGradX φ x i * torusGradX φ x i = 0 := by
    intro i; apply le_antisymm _ (h_nonneg i)
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => h_nonneg j) (Finset.mem_univ i)
    linarith [hsum_zero]
  -- ∂φ/∂xᵢ = 0 everywhere (nonneg continuous, integral = 0, compact space)
  have hgrad_zero : ∀ i x, torusGradX φ x i = 0 := by
    intro i x
    have hcont := continuous_torusGradX φ i (hd.of_le le_top)
    have hae : (fun x => torusGradX φ x i * torusGradX φ x i) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _)
        ((hcont.mul hcont).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))).mp (hgrad_sq_zero i)
    have hae' : (fun x => torusGradX φ x i) =ᵐ[volume] 0 := by
      filter_upwards [hae] with x hx; exact mul_self_eq_zero.mp hx
    exact congr_fun (MeasureTheory.Measure.eq_of_ae_eq hae' hcont continuous_const) x
  -- fderiv of periodicLift φ is zero everywhere
  have hfderiv_zero : ∀ y, fderiv ℝ (periodicLift φ) y = 0 := by
    intro y; ext v
    have hv : v = ∑ i : Fin 3, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
    rw [hv, map_sum, ContinuousLinearMap.zero_apply]
    apply Finset.sum_eq_zero; intro i _
    rw [map_smul, smul_eq_mul, show (fderiv ℝ (periodicLift φ) y) (Pi.single i 1) =
        torusGradX φ (torusMk y) i from (periodicLift_torusGradX φ i y).symm,
      hgrad_zero, mul_zero]
  -- φ is constant via periodicLift constant
  intro x y
  obtain ⟨x₀, hx⟩ := torusMk_surjective x
  obtain ⟨y₀, hy⟩ := torusMk_surjective y
  have := is_const_of_fderiv_eq_zero (hd.differentiable le_top) hfderiv_zero x₀ y₀
  rw [← hx, ← hy]; exact this

-- ============================================================================
-- ℝⁿ lemmas (proved in aristotle-in/, integrated here)
-- ============================================================================

/-- At a local maximum of a twice-differentiable function, the second derivative is nonpositive.
    Proved by Aristotle. -/
private theorem second_deriv_nonpos_at_local_max' {f : ℝ → ℝ} {x₀ : ℝ}
    (hmax : IsLocalMax f x₀)
    (hf' : ∀ᶠ x in nhds x₀, DifferentiableAt ℝ f x)
    (hf'' : DifferentiableAt ℝ (deriv f) x₀) :
    deriv (deriv f) x₀ ≤ 0 := by
  have h_first_deriv_zero : deriv f x₀ = 0 := IsLocalMax.deriv_eq_zero hmax
  by_contra h_contra; push_neg at h_contra
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ x ∈ Set.Ioo x₀ (x₀ + ε), deriv f x > 0 := by
    have := Metric.tendsto_nhds_nhds.1 (hf''.hasDerivAt.isLittleO.tendsto_div_nhds_zero)
    obtain ⟨δ, δ_pos, H⟩ := this _ h_contra; use δ, δ_pos; intro x hx
    have := H (show |x - x₀| < δ from abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    simp_all +decide [div_eq_mul_inv]
    rw [← div_eq_mul_inv, div_lt_iff₀] at this <;>
      cases abs_cases (deriv f x - (x - x₀) * deriv (deriv f) x₀) <;>
      cases abs_cases (x - x₀) <;>
      nlinarith [mul_pos (sub_pos.mpr hx.1) h_contra]
  have h_mvt : ∀ x ∈ Set.Ioo x₀ (x₀ + ε), ∃ c ∈ Set.Ioo x₀ x, deriv f c = (f x - f x₀) / (x - x₀) := by
    intros x hx
    apply exists_deriv_eq_slope f hx.left
    exact continuousOn_of_forall_continuousAt fun y hy =>
      if h : y = x₀ then by rw [h]; exact DifferentiableAt.continuousAt hf'.self_of_nhds
      else DifferentiableAt.continuousAt (differentiableAt_of_deriv_ne_zero
        (ne_of_gt (hε.2 y ⟨lt_of_le_of_ne hy.1 (Ne.symm h), by linarith [hy.2, hx.2]⟩)))
    exact fun y hy => DifferentiableAt.differentiableWithinAt
      (differentiableAt_of_deriv_ne_zero (ne_of_gt (hε.2 y ⟨hy.1, hy.2.trans hx.2⟩)))
  have h_inc : ∀ x ∈ Set.Ioo x₀ (x₀ + ε), f x > f x₀ := by
    intro x hx; obtain ⟨c, hc₁, hc₂⟩ := h_mvt x hx
    have := hε.2 c ⟨by linarith [hc₁.1, hx.1], by linarith [hc₁.2, hx.2]⟩
    rw [eq_div_iff] at hc₂ <;> nlinarith [hc₁.1, hc₁.2]
  rcases Metric.eventually_nhds_iff.mp hmax with ⟨δ, hδ, hδ'⟩
  exact absurd (h_inc (x₀ + Min.min ε δ / 2) ⟨by linarith [lt_min hε.1 hδ],
      by linarith [min_le_left ε δ, min_le_right ε δ]⟩)
    (not_lt_of_ge <| hδ' <| mem_ball_iff_norm.mpr <| abs_lt.mpr
      ⟨by linarith [lt_min hε.1 hδ, min_le_left ε δ, min_le_right ε δ],
       by linarith [lt_min hε.1 hδ, min_le_left ε δ, min_le_right ε δ]⟩)

/-- Killing equation on ℝⁿ implies each component is harmonic. -/
private theorem killing_harmonic_rn' {n : ℕ} (b : (Fin n → ℝ) → (Fin n → ℝ))
    (hb : ∀ j, ContDiff ℝ 2 (fun y => b y j))
    (hKilling : ∀ x i j,
      fderiv ℝ (fun y => b y j) x (Pi.single i 1) +
      fderiv ℝ (fun y => b y i) x (Pi.single j 1) = 0)
    (j : Fin n) (x : Fin n → ℝ) :
    ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => b z j) y (Pi.single i 1)) x (Pi.single i 1) = 0 := by
  apply Finset.sum_eq_zero; intro i _
  have hK_fun : ∀ y, fderiv ℝ (fun z => b z j) y (Pi.single i 1) =
      -(fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by
    intro y; linarith [hKilling y i j]
  have hfun_eq : (fun y => fderiv ℝ (fun z => b z j) y (Pi.single i 1)) =
      (fun y => -(fderiv ℝ (fun z => b z i) y (Pi.single j 1))) := funext hK_fun
  rw [hfun_eq]
  have hdiff_j : Differentiable ℝ (fun y => fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by
    have : ContDiff ℝ 1 (fun y => fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by
      apply ContDiff.clm_apply
      · exact (hb i).fderiv_right le_rfl
      · exact contDiff_const
    exact this.differentiable le_rfl
  have hfun_neg : (fun y => -(fderiv ℝ (fun z => b z i) y (Pi.single j 1))) =
      -(fun y => fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by ext; simp
  rw [hfun_neg, fderiv_neg]
  simp only [ContinuousLinearMap.neg_apply, neg_eq_zero]
  rw [clairaut_fderiv (fun z => b z i) x i j (hb i)]
  have hK_diag_fun : (fun y => fderiv ℝ (fun z => b z i) y (Pi.single i 1)) = fun _ => 0 := by
    ext y; linarith [hKilling y i i]
  rw [hK_diag_fun]; simp

/-- Irrotational + solenoidal → each component is harmonic on ℝⁿ. -/
private theorem curl_div_harmonic_rn' {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ∀ i, ContDiff ℝ 2 (fun y => F y i))
    (hcurl : ∀ x i j,
      fderiv ℝ (fun y => F y j) x (Pi.single i 1) =
      fderiv ℝ (fun y => F y i) x (Pi.single j 1))
    (hdiv : ∀ x, ∑ i : Fin n,
      fderiv ℝ (fun y => F y i) x (Pi.single i 1) = 0)
    (j : Fin n) (x : Fin n → ℝ) :
    ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => F z j) y (Pi.single i 1)) x (Pi.single i 1) = 0 := by
  have hcurl_fun : ∀ i, (fun y => fderiv ℝ (fun z => F z j) y (Pi.single i 1)) =
      (fun y => fderiv ℝ (fun z => F z i) y (Pi.single j 1)) := by
    intro i; ext y; exact hcurl y i j
  simp_rw [hcurl_fun]
  simp_rw [clairaut_fderiv (fun z => F z _) x _ j (hF _)]
  have hdiff_comp : ∀ i, DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x := by
    intro i
    have : ContDiff ℝ 1 (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) :=
      ContDiff.clm_apply ((hF i).fderiv_right le_rfl) contDiff_const
    exact (this.differentiable le_rfl).differentiableAt
  have : ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x (Pi.single j 1) =
      (∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x) (Pi.single j 1) :=
    (ContinuousLinearMap.sum_apply _ _ _).symm
  rw [this]
  have hfsum : (∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x) =
      fderiv ℝ (fun y => ∑ i : Fin n, fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x := by
    rw [fderiv_fun_sum (fun i _ => hdiff_comp i)]
  rw [hfsum]
  have hsum_fun : (fun y => ∑ i : Fin n, fderiv ℝ (fun z => F z i) y (Pi.single i 1)) = fun _ => 0 :=
    funext hdiv
  rw [hsum_fun]; simp

-- ============================================================================

/-- hLaplacianMaxNonpos: Δφ ≤ 0 at a global maximum.
    Second derivative test: at a maximum, the Hessian is negative semi-definite,
    so its trace (= Laplacian) ≤ 0. -/
theorem torus_hLaplacianMaxNonpos (φ : Torus3 → ℝ) (x₀ : Torus3)
    (hd : ContDiff ℝ 1 (periodicLift φ))
    (hmax : ∀ x, φ x ≤ φ x₀) :
    torusDivX (torusGradX φ) x₀ ≤ 0 := by
  simp only [torusDivX]
  -- Rewrite using periodicLift_torusGradX
  simp_rw [show ∀ i, (fun y => periodicLift (fun z => torusGradX φ z i) y) =
      (fun y => fderiv ℝ (periodicLift φ) y (Pi.single i 1)) from
      fun i => funext (periodicLift_torusGradX φ i)]
  -- Let x₀' be the canonical preimage of x₀
  set x₀' := (torusMk_surjective x₀).choose
  -- For each i, show the term is ≤ 0
  apply Finset.sum_nonpos; intro i _
  -- Let hᵢ y = fderiv ℝ (periodicLift φ) y (Pi.single i 1)
  -- Case split: either hᵢ is differentiable at x₀' or not
  by_cases hdiff : DifferentiableAt ℝ (fun y => fderiv ℝ (periodicLift φ) y (Pi.single i 1)) x₀'
  · -- Case: hᵢ is differentiable at x₀'. Use 1D second derivative test.
    -- Let gᵢ t = periodicLift φ (x₀' + t • eᵢ)
    let eᵢ : Fin 3 → ℝ := Pi.single i 1
    let gᵢ : ℝ → ℝ := fun t => periodicLift φ (x₀' + t • eᵢ)
    -- gᵢ has global max at 0
    have hmax_gi : IsLocalMax gᵢ 0 :=
      Filter.Eventually.mono Filter.univ_mem fun t _ => by
        simp only [gᵢ, zero_smul, add_zero, periodicLift, Function.comp_apply]
        rw [(torusMk_surjective x₀).choose_spec]
        exact hmax (torusMk (x₀' + t • eᵢ))
    -- Helper: the path t ↦ x₀' + t • eᵢ has derivative eᵢ
    have hpath_hd : ∀ t, HasDerivAt (fun s => x₀' + s • eᵢ) eᵢ t := fun t => by
      have hsmul : HasDerivAt (fun s : ℝ => s • eᵢ) eᵢ t := by
        have h := (hasDerivAt_id t).smul_const eᵢ
        simp only [id, one_smul] at h; exact h
      simpa using hsmul.const_add x₀'
    -- gᵢ is differentiable everywhere (since periodicLift φ is C¹)
    have hd_diff : Differentiable ℝ (periodicLift φ) := hd.differentiable le_rfl
    have hgi_diff : ∀ t, DifferentiableAt ℝ gᵢ t := fun t =>
      hd_diff.differentiableAt.comp t (hpath_hd t).differentiableAt
    -- deriv gᵢ = hᵢ ∘ (x₀' + · • eᵢ)
    have hderiv_gi : ∀ t, deriv gᵢ t = fderiv ℝ (periodicLift φ) (x₀' + t • eᵢ) eᵢ := fun t =>
      (hd_diff.differentiableAt.hasFDerivAt.comp_hasDerivAt t (hpath_hd t)).deriv
    -- deriv gᵢ is differentiable at 0 (since hᵢ is diff at x₀')
    have hderiv_gi_diff : DifferentiableAt ℝ (deriv gᵢ) 0 := by
      rw [show deriv gᵢ = fun t => fderiv ℝ (periodicLift φ) (x₀' + t • eᵢ) eᵢ from funext hderiv_gi]
      show DifferentiableAt ℝ ((fun y => fderiv ℝ (periodicLift φ) y eᵢ) ∘ (fun t : ℝ => x₀' + t • eᵢ)) 0
      apply DifferentiableAt.comp
      · simp only [zero_smul, add_zero]; exact hdiff
      · exact (hpath_hd 0).differentiableAt
    -- Apply 1D second derivative test
    have h1d : deriv (deriv gᵢ) 0 ≤ 0 :=
      second_deriv_nonpos_at_local_max' hmax_gi
        (Filter.Eventually.mono Filter.univ_mem (fun t _ => hgi_diff t))
        hderiv_gi_diff
    -- Connect: fderiv ℝ hᵢ x₀' eᵢ = deriv (deriv gᵢ) 0
    have hconnect : deriv (deriv gᵢ) 0 = fderiv ℝ (fun y => fderiv ℝ (periodicLift φ) y eᵢ) x₀' eᵢ := by
      rw [show deriv gᵢ = fun t : ℝ => fderiv ℝ (periodicLift φ) (x₀' + t • eᵢ) eᵢ from funext hderiv_gi]
      -- Use chain rule: g ∘ f has deriv (fderiv g x₀') eᵢ at 0
      -- where g = fun y => fderiv ... y eᵢ, f = fun t => x₀' + t • eᵢ
      have hfda : HasFDerivAt (fun y => fderiv ℝ (periodicLift φ) y eᵢ)
          (fderiv ℝ (fun y => fderiv ℝ (periodicLift φ) y eᵢ) x₀') (x₀' + (0 : ℝ) • eᵢ) := by
        simp only [zero_smul, add_zero]; exact hdiff.hasFDerivAt
      exact (hfda.comp_hasDerivAt 0 (hpath_hd 0)).deriv
    rw [← hconnect]; exact h1d
  · -- Case: hᵢ not differentiable at x₀'. fderiv = 0 ≤ 0.
    simp [fderiv_zero_of_not_differentiableAt hdiff]

-- ============================================================================
-- Flatness axioms
-- ============================================================================

/-- hKillingToHarmonic: Killing vector field components are harmonic on flat T³. -/
-- Helper used by both Killing and curl/div proofs:
-- derive ContDiff ℝ 2 from C¹ + C¹ of each partial
private lemma contDiff2_from_partials {g : (Fin 3 → ℝ) → ℝ}
    (hg1 : ContDiff ℝ 1 g)
    (hg_parts : ∀ i : Fin 3, ContDiff ℝ 1 (fun y => fderiv ℝ g y (Pi.single i 1))) :
    ContDiff ℝ 2 g := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨hg1.differentiable le_rfl, fun h => by simp at h, ?_⟩
  rw [contDiff_clm_apply_iff]
  intro v
  have heq : (fun y => fderiv ℝ g y v) =
      fun y => ∑ i : Fin 3, v i * fderiv ℝ g y (Pi.single i 1) := by
    ext y
    set L := fderiv ℝ g y with hL
    have hv : v = ∑ i : Fin 3, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
      ext m; simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq']
    -- conv_lhs rewrites only the argument of L, not the v inside the sum on the RHS
    calc L v = L (∑ i : Fin 3, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ)) := by
            conv_lhs => rw [hv]
      _ = ∑ i : Fin 3, v i * L (Pi.single i (1 : ℝ)) := by
          simp [map_sum, map_smul, smul_eq_mul]
  rw [heq]
  exact ContDiff.sum (fun i _ => (hg_parts i).const_smul (v i))

theorem torus_hKillingToHarmonic (b : Torus3 → Fin 3 → ℝ)
    (hb_C1 : ∀ j, ContDiff ℝ 1 (periodicLift (fun z => b z j)))
    (hb_C2 : ∀ j i, ContDiff ℝ 1 (periodicLift (fun x => torusGradX (fun y => b y j) x i)))
    (hKilling : ∀ x i j, torusGradX (fun y => b y j) x i +
                          torusGradX (fun y => b y i) x j = 0) :
    ∀ j : Fin 3, ∀ x, torusDivX (torusGradX (fun y => b y j)) x = 0 := by
  -- Convert hb_C2 to ℝⁿ form: each partial ∂b_k/∂x_i is C¹
  have hC2_comp : ∀ k i : Fin 3, ContDiff ℝ 1
      (fun y => fderiv ℝ (periodicLift (fun z => b z k)) y (Pi.single i 1)) := by
    intro k i
    have h := hb_C2 k i
    rwa [show periodicLift (fun x => torusGradX (fun y => b y k) x i) =
        fun y => fderiv ℝ (periodicLift (fun z => b z k)) y (Pi.single i 1) from
        funext (periodicLift_torusGradX (fun z => b z k) i)] at h
  -- Derive ContDiff ℝ 2 for each component
  have hC2_all : ∀ k : Fin 3, ContDiff ℝ 2 (periodicLift (fun z => b z k)) :=
    fun k => contDiff2_from_partials (hb_C1 k) (hC2_comp k)
  -- Killing condition in ℝⁿ form
  have hKilling_rn : ∀ (y : Fin 3 → ℝ) (i k : Fin 3),
      fderiv ℝ (periodicLift (fun z => b z k)) y (Pi.single i 1) +
      fderiv ℝ (periodicLift (fun z => b z i)) y (Pi.single k 1) = 0 := by
    intro y i k
    rw [← periodicLift_torusGradX (fun w => b w k) i y,
        ← periodicLift_torusGradX (fun w => b w i) k y]
    simp only [periodicLift, Function.comp_apply]
    exact hKilling (torusMk y) i k
  -- Main proof: for each j and x, show div(grad(b_j))(x) = 0
  intro jj x
  simp only [torusDivX]
  simp_rw [show ∀ i : Fin 3, (fun y => periodicLift (fun z => torusGradX (fun w => b w jj) z i) y) =
      (fun y => fderiv ℝ (periodicLift (fun z => b z jj)) y (Pi.single i 1)) from
      fun i => funext (periodicLift_torusGradX (fun z => b z jj) i)]
  exact killing_harmonic_rn'
    (fun y k => periodicLift (fun z => b z k) y)
    hC2_all hKilling_rn jj (torusMk_surjective x).choose

/-- hCurlZeroDivZeroHarmonic: irrotational + solenoidal → harmonic on flat T³. -/
theorem torus_hCurlZeroDivZeroHarmonic (F : Torus3 → Fin 3 → ℝ)
    (hF_C1 : ∀ i, ContDiff ℝ 1 (periodicLift (fun z => F z i)))
    (hF_C2 : ∀ i j, ContDiff ℝ 1 (periodicLift (fun x => torusGradX (fun y => F y i) x j)))
    (hcurl : ∀ x, torusCurlX F x = 0) (hdiv : ∀ x, torusDivX F x = 0) :
    ∀ i, ∀ x, torusDivX (torusGradX (fun y => F y i)) x = 0 := by
  -- Convert hF_C2 to ℝⁿ form
  have hC2_comp : ∀ k j : Fin 3, ContDiff ℝ 1
      (fun y => fderiv ℝ (periodicLift (fun z => F z k)) y (Pi.single j 1)) := by
    intro k j
    have h := hF_C2 k j
    rwa [show periodicLift (fun x => torusGradX (fun y => F y k) x j) =
        fun y => fderiv ℝ (periodicLift (fun z => F z k)) y (Pi.single j 1) from
        funext (periodicLift_torusGradX (fun z => F z k) j)] at h
  -- ContDiff ℝ 2 for each component
  have hC2_all : ∀ k : Fin 3, ContDiff ℝ 2 (periodicLift (fun z => F z k)) :=
    fun k => contDiff2_from_partials (hF_C1 k) (hC2_comp k)
  -- Symmetric Jacobian from curl = 0.
  -- Key insight: torusCurlX F x = ![torusGradX (F·2) x 1 - ..., ..., ...] by rfl
  -- (both use the same canonical preimage x₀ = (torusMk_surjective x).choose,
  --  and fun w => periodicLift f w = periodicLift f by eta reduction in Lean 4)
  have hjac_sym : ∀ (y : Fin 3 → ℝ) (i j : Fin 3),
      fderiv ℝ (periodicLift (fun z => F z j)) y (Pi.single i 1) =
      fderiv ℝ (periodicLift (fun z => F z i)) y (Pi.single j 1) := by
    intro y i j
    rw [← periodicLift_torusGradX (fun z => F z j) i y,
        ← periodicLift_torusGradX (fun z => F z i) j y]
    simp only [periodicLift, Function.comp_apply]
    -- Goal: torusGradX (F·j) (torusMk y) i = torusGradX (F·i) (torusMk y) j
    have hcurl_y := hcurl (torusMk y)
    -- Express torusCurlX directly in terms of torusGradX (by definitional equality / eta)
    have hcurl_expand : torusCurlX F (torusMk y) =
        ![torusGradX (fun w => F w 2) (torusMk y) 1 - torusGradX (fun w => F w 1) (torusMk y) 2,
          torusGradX (fun w => F w 0) (torusMk y) 2 - torusGradX (fun w => F w 2) (torusMk y) 0,
          torusGradX (fun w => F w 1) (torusMk y) 0 - torusGradX (fun w => F w 0) (torusMk y) 1] := rfl
    rw [hcurl_expand] at hcurl_y
    -- Extract the three symmetry conditions
    have h0 : torusGradX (fun w => F w 2) (torusMk y) 1 = torusGradX (fun w => F w 1) (torusMk y) 2 := by
      have := congr_fun hcurl_y 0; simp at this; linarith
    have h1 : torusGradX (fun w => F w 0) (torusMk y) 2 = torusGradX (fun w => F w 2) (torusMk y) 0 := by
      have := congr_fun hcurl_y 1; simp at this; linarith
    have h2 : torusGradX (fun w => F w 1) (torusMk y) 0 = torusGradX (fun w => F w 0) (torusMk y) 1 := by
      have := congr_fun hcurl_y 2; simp at this; linarith
    fin_cases i <;> fin_cases j <;> simp_all
  -- Divergence-free in ℝⁿ form
  -- torusDivX F (torusMk y) = 0 gives the sum at x₀ = (torusMk_surjective (torusMk y)).choose.
  -- Transfer to y via periodicLift_fderiv_eq (both x₀ and y are preimages of torusMk y).
  have hdiv_rn : ∀ (y : Fin 3 → ℝ),
      ∑ i : Fin 3, fderiv ℝ (periodicLift (fun z => F z i)) y (Pi.single i 1) = 0 := by
    intro y
    have key := hdiv (torusMk y)
    simp only [torusDivX] at key
    -- key uses x₀ = (torusMk_surjective (torusMk y)).choose; normalize eta form
    simp only [show ∀ i : Fin 3, (fun w => periodicLift (fun z => F z i) w) =
        periodicLift (fun z => F z i) from fun _ => rfl] at key
    -- key : ∑ i, fderiv ℝ (periodicLift (F·i)) x₀ (Pi.single i 1) = 0
    -- Convert to sum at y using periodicLift_fderiv_eq
    calc ∑ i : Fin 3, fderiv ℝ (periodicLift (fun z => F z i)) y (Pi.single i 1)
        = ∑ i : Fin 3, fderiv ℝ (periodicLift (fun z => F z i))
            ((torusMk_surjective (torusMk y)).choose) (Pi.single i 1) := by
          apply Finset.sum_congr rfl; intro i _
          exact congrFun (congrArg DFunLike.coe
            (periodicLift_fderiv_eq (fun z => F z i) y _
            ((torusMk_surjective (torusMk y)).choose_spec.symm))) (Pi.single i 1)
      _ = 0 := key
  -- Main proof
  intro ii x
  simp only [torusDivX]
  simp_rw [show ∀ i : Fin 3, (fun y => periodicLift (fun z => torusGradX (fun w => F w ii) z i) y) =
      (fun y => fderiv ℝ (periodicLift (fun z => F z ii)) y (Pi.single i 1)) from
      fun i => funext (periodicLift_torusGradX (fun z => F z ii) i)]
  exact curl_div_harmonic_rn'
    (fun y k => periodicLift (fun z => F z k) y)
    hC2_all hjac_sym hdiv_rn ii (torusMk_surjective x).choose

-- ============================================================================
-- The FlatTorus3 instance (all fields proved, 0 sorry's)
-- ============================================================================

instance : VML.FlatTorus3 Torus3 where
  toMeasureSpace := inferInstance
  instCompact := inferInstance
  instNonempty := ⟨fun _ => 0⟩
  instFirstCountable := inferInstance
  gradX := torusGradX
  divX := torusDivX
  curlX := torusCurlX
  hDivLinear := by
    intro α G x; simp only [torusDivX]
    simp only [show ∀ i, periodicLift (fun z => (α • G z) i) = fun y => α * periodicLift (fun z => G z i) y
      from fun i => by ext y; simp [periodicLift, Pi.smul_apply, smul_eq_mul]]
    simp [fderiv_const_mul_always, Finset.mul_sum]
  hGradConst := torus_hGradConst
  hSpatialPos := fun g hcont hpos => torus_hSpatialPos g hpos hcont
  hSpatialNonnegZero := fun g hcont hnn hint => torus_hSpatialNonnegZero g hnn hint hcont
  IsSpatiallyDiff := fun f => ContDiff ℝ ⊤ (periodicLift f)
  hDiff_const := fun c => by
    show ContDiff ℝ ⊤ (periodicLift (fun _ => c))
    have : periodicLift (fun _ : Torus3 => c) = fun _ => c := by ext y; simp [periodicLift]
    rw [this]; exact contDiff_const
  hDiff_add := fun f g hf hg => by
    show ContDiff ℝ ⊤ (periodicLift (fun x => f x + g x))
    have : periodicLift (fun x => f x + g x) = fun y => periodicLift f y + periodicLift g y := by
      ext y; simp [periodicLift]
    rw [this]; exact hf.add hg
  hDiff_smul := fun c f hf => by
    show ContDiff ℝ ⊤ (periodicLift (fun x => c * f x))
    have : periodicLift (fun x => c * f x) = fun y => c * periodicLift f y := by
      ext y; simp [periodicLift]
    rw [this]; exact hf.const_smul c
  hDiff_log := fun f hf hpos => by
    show ContDiff ℝ ⊤ (periodicLift (Real.log ∘ f))
    have hlift : periodicLift (Real.log ∘ f) = Real.log ∘ periodicLift f := rfl
    rw [hlift]
    exact hf.log (fun y => ne_of_gt (hpos (torusMk y)))
  hDiff_continuous := fun f hf => by
    -- hf : ContDiff ℝ ⊤ (periodicLift f), so periodicLift f is continuous
    -- periodicLift f = f ∘ torusMk, and torusMk is a quotient map
    -- Therefore f is continuous by the quotient map property
    rw [isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff]
    show Continuous (periodicLift f)
    exact hf.continuous
  hDiff_grad := fun f i hf => by
    -- periodicLift (fun x => gradX f x i) = fun y => fderiv ℝ (periodicLift f) y (Pi.single i 1)
    show ContDiff ℝ ⊤ (periodicLift (fun x => torusGradX f x i))
    have heq : periodicLift (fun x => torusGradX f x i) =
        fun y => fderiv ℝ (periodicLift f) y (Pi.single i 1) :=
      funext (fun y => periodicLift_torusGradX f i y)
    rw [heq]
    -- ContDiff ℝ ⊤ (periodicLift f) → ContDiff ℝ ⊤ (fderiv) → apply to Pi.single i 1
    exact (hf.fderiv_right le_top).clm_apply contDiff_const
  hCurlIntZero := fun F u hF => torus_hCurlIntZero F u (fun j => (hF j).of_le le_top)
  hHarmonic_const := fun φ hd => torus_hHarmonic_const φ hd
  hLaplacianMaxNonpos := fun φ x₀ hd => torus_hLaplacianMaxNonpos φ x₀ (hd.of_le le_top)
  hGradAdd := fun f g hf hg => torus_hGradAdd' f g (hf.of_le le_top) (hg.of_le le_top)
  hGradScalarMul := by
    intro c f x; ext i; simp only [torusGradX, Pi.smul_apply, smul_eq_mul]
    show fderiv ℝ (periodicLift (fun y => c * f y)) _ (Pi.single i 1) = _
    simp only [show periodicLift (fun y => c * f y) = fun y => c * periodicLift f y
      from by ext y; simp [periodicLift]]
    rw [fderiv_const_mul_always]; rfl
  hGradChainExp := by
    intro φ _hφ x i; simp only [torusGradX]
    show fderiv ℝ (periodicLift (fun y => Real.exp (φ y))) _ (Pi.single i 1) = _
    have hlift : periodicLift (fun y => Real.exp (φ y)) = fun y => Real.exp (periodicLift φ y) :=
      by ext y; simp [periodicLift]
    rw [hlift, fderiv_exp_comp_always, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hx₀ := (torusMk_surjective x).choose_spec
    show Real.exp (periodicLift φ _) * _ = Real.exp (φ x) * _
    simp [periodicLift, hx₀]
  hKillingToHarmonic := fun b hb_C1 hb_C2 hKilling =>
    torus_hKillingToHarmonic b (fun j => (hb_C1 j).of_le le_top)
      (fun j i => (hb_C2 j i).of_le le_top) hKilling
  hCurlZeroDivZeroHarmonic := fun F hF_C1 hF_C2 hcurl hdiv =>
    torus_hCurlZeroDivZeroHarmonic F (fun i => (hF_C1 i).of_le le_top)
      (fun i j => (hF_C2 i j).of_le le_top) hcurl hdiv
  hIBP_spatial := fun φ ψ i hφ hψ => torus_hIBP_spatial φ ψ i (hφ.of_le le_top) (hψ.of_le le_top)
  hSpatialVelocityFubini := by
    intro F _ hF_joint
    exact integral_integral_swap hF_joint
  hSpatialAdd := fun g₁ g₂ h1 h2 => integral_add h1 h2
  hGradIntegrable := by
    intro g hg i
    have h_cont : Continuous (fun x : Torus3 => torusGradX g x i) := by
      have hH_cont : Continuous (fun y : Fin 3 → ℝ => fderiv ℝ (periodicLift g) y (Pi.single i 1)) :=
        (hg.continuous_fderiv le_top).clm_apply continuous_const
      have heq : (fun x : Torus3 => torusGradX g x i) ∘ torusMk =
          fun y => fderiv ℝ (periodicLift g) y (Pi.single i 1) :=
        funext (fun y => periodicLift_torusGradX g i y)
      rw [isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff, heq]
      exact hH_cont
    rw [← integrableOn_univ]
    exact h_cont.continuousOn.integrableOn_compact isCompact_univ

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## Status of the FlatTorus3 instance on Fin 3 → AddCircle 1

**0 errors, 0 sorry's**

### Instance fields:
- All 21 fields proved (hDiff_velocityIntegral removed from FlatTorus3 — see below)
- hGradConst, hGradAdd, hGradScalarMul, hGradChainExp: proved
- hDivLinear: case analysis on differentiability
- hSpatialPos, hSpatialNonnegZero: with Continuous hypothesis
- hSpatialVelocityFubini: with joint integrability
- hSpatialAdd: with integrability hypotheses, via integral_add
- hGradIntegrable: proved via IsOpenQuotientMap.piMap
- IsSpatiallyDiff := ContDiff ℝ ⊤ ∘ periodicLift (smooth)
- hDiff_const, hDiff_add, hDiff_smul, hDiff_log, hDiff_grad: closure properties, all proved
- hCurlIntZero: forwarded to torus_hCurlIntZero (proved)
- hHarmonic_const: forwarded to torus_hHarmonic_const (proved, energy method)
- hIBP_spatial: forwarded to torus_hIBP_spatial (proved)
- hLaplacianMaxNonpos: 1D second derivative test + chain rule (proved)
- hKillingToHarmonic, hCurlZeroDivZeroHarmonic: Clairaut + algebraic argument (proved)

### Proved helper theorems (11+):
- torus_hIBP_spatial: core torus IBP (1D FTC + Fubini + periodicity)
- torus_hCurlIntZero: integral of curl = 0 (from IBP with φ=1)
- torus_hHarmonic_const: harmonic → constant on torus (energy method via IBP)
- torus_hGradConst, torus_hGradAdd', torus_hSpatialPos, torus_hSpatialNonnegZero
- torus_hSpatialVelocityFubini, torus_hLaplacianMaxNonpos
- torus_hKillingToHarmonic, torus_hCurlZeroDivZeroHarmonic
-/

end
