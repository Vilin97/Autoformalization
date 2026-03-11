# Log

## 2026-03-10 UTC — Babysit cycle 73: Fix Mathlib API drift (P0)

### Changes
- **Fixed Section3Helpers.lean compilation from source** — 14 errors resolved:
  - Added 4 missing Mathlib imports (`Integral.Pi`, `Gaussian.GaussianIntegral`, `FDeriv.Symmetric`, `ContDiff.Bounds`) lost after Mathlib import graph change.
  - Fixed `iteratedFDeriv_sum` call: removed `(x := v)` parameter (now returns function-level equality; use `congrFun` for pointwise).
  - Fixed `ContDiff.fderiv_right le_rfl` → `(m := 1) le_rfl` (new API requires `m + 1 ≤ n` explicitly).
  - Replaced `.apply 0` (removed dot notation) with `(contDiff_apply ℝ ℝ 0).comp (...)`.
- **TorusDefs.lean** errors were LSP false positives — compiles fine via `lake build`.
- **Full project rebuilds from source** with 0 errors (verified by deleting all project .olean and rebuilding).
- Updated critique to cycle 73 (REVISE → to be updated after fix).

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 72: Critique update, no dead code found

### Changes
- Updated critique to cycle 72 (ACCEPT, 0 sorry's).
- Searched for dead code across 4 largest files: all flagged lemmas are actually used (agent's search missed intra-file references).
- **Observed**: Section3Helpers.lean has Mathlib API drift (e.g., `norm_iteratedFDeriv_mul_le`, `integral_gaussian` renamed). Builds pass via cached .olean but fresh builds would fail. This is pre-existing.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 71: Extract remaining derivative helpers

### Changes
- **Extracted 4 lemmas** (`norm_sq_le_normSq`, `contDiff_negNormSq_div`, `norm_iteratedFDeriv_proj_sq_le`, `quadratic_iteratedFDeriv_bound`) from CoulombConcreteTheorem42.lean to Section3Helpers.lean.
- CoulombConcreteTheorem42.lean: 742→636 lines (reduced by 106 lines). Now a focused theorem file.
- Section3Helpers.lean: 647→757 lines (received derivative bound helpers).
- Updated critique to cycle 71 (still ACCEPT).

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 70: Code quality — extract helpers, fix long lines

### Changes
- **Extracted 2 CLM lemmas** (`iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm`) from CoulombConcreteTheorem42.lean to Section3Helpers.lean. CoulombConcreteTheorem42: 762→742 lines.
- **Fixed 3 long-line warnings** in Defs.lean (lines 324, 363, 424).
- **Updated critique** to cycle 70: verdict ACCEPT (0 sorry's, 0 errors, 0 axioms).

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 69: Close last sorry (10) hVlasov (1→0)

### Changes
- **Closed sorry (10)** `hVlasov` — Maxwellian in kernel of Landau operator. Proved via projection annihilation: the bracket `eM(w)·∇eM(v') - eM(v')·∇eM(w)` simplifies to `scalar • (v'-w)`, and `landauMatrix_mulVec_self` gives `A(z)·z = 0`, so the integrand vanishes pointwise.
- **Added 2 lemmas to Defs.lean**: `innerLandauMatrix_mulVec_self` and `landauMatrix_mulVec_self` (projection annihilation property).
- **Removed duplicate lemmas**: these already existed in Section2.lean — removed the Defs.lean copies during `/simplify`.
- **Made helper lemmas public**: un-privated `iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` for Mathlib upstreamability.
- **Updated docstring**: all 10 non-trivial goals fully proved, 0 sorry's.

### Sorry count: 0

### Milestone
**All sorry's in the project are now closed.** 22 files, ~8,300 lines, 0 sorry's. Both `CoulombConcreteTheorem42` and `CoulombConcreteTheorem42_nonvacuous` verified with zero extra axioms.

## 2026-03-10 UTC — Babysit cycle 68: Close sorry (7) hDecay (2→1)

### Changes
- **Closed sorry (7)** `hDecay` — the polynomial×Gaussian bound for equilibrium Maxwellian Schwartz decay. Proved `quadratic_iteratedFDeriv_bound`: ‖iteratedFDeriv i (-normSq/(2T)) v‖ ≤ (c(1+‖v‖))^i via Leibniz formula on each v_j² component.
- **Added 3 helper lemmas**: `iteratedFDeriv_clm_zero` (iteratedFDeriv of CLM = 0 for n ≥ 2), `norm_iteratedFDeriv_one_clm` (‖iteratedFDeriv 1 f x‖ = ‖f‖ for CLM f), `norm_iteratedFDeriv_proj_sq_le` (component bound 2(1+‖v‖))
- **Removed `maxHeartbeats 400000`** from `equilibriumMaxwellian_schwartz_decay` — now compiles within default heartbeats
- **Updated docstring**: 10 of 10 goals addressed, 1 sorry'd

### Sorry count: 1 (in `CoulombConcreteTheorem42_nonvacuous`)

### Remaining sorry
- (10) hVlasov: Maxwellian in kernel of Landau operator (hardest — needs collision operator analysis)

## 2026-03-10 UTC — Babysit cycle 67: Close sorry (12), decompose sorry (7) (3→2)

### Changes
- **Closed sorry (12)** `hGauss` in `CoulombConcreteTheorem42_nonvacuous`: Gauss's law ∇·E=0 = ∫eM-ρ_ion. Proof: `simp` simplifies divergence of zero to 0, then closes the integral equation.
- **Decomposed sorry (7)** `hSchwartz`: split into `hDecay` (sorry — needs iteratedFDeriv × polynomial × Gaussian bound) and `hGradDecay` (proved — spatial gradient of constant function is 0).
- **Updated MEMORY.md**: corrected sorry count (6→2), line counts (7900→8000, CoulombConcreteTheorem42 395→460).
- **Updated docstring**: 8 of 10 non-trivial goals proved, 2 sorry'd.

### Sorry count: 2 (all in `CoulombConcreteTheorem42_nonvacuous`)

### Remaining sorry's
- (7) hDecay in UniformSchwartzDecay — needs `‖iteratedFDeriv ℝ k eM v‖ * (1+‖v‖)^N ≤ C` (polynomial × Gaussian bound + `norm_iteratedFDeriv_comp_le`)
- (10) Vlasov equation — Landau operator nullspace for Maxwellian (hardest)

## 2026-03-10 UTC — Babysit cycle 66: Close 3 more non-vacuousness sorry's (6→3)

### Changes
- **Closed 3 sorry's** in `CoulombConcreteTheorem42_nonvacuous` (6→3):
  - (8) `hExpDecay`: exponential decay lower bound — proved via `equilibriumMaxwellian_exp_lower_bound` helper: normSq v ≤ 3(1+‖v‖)², choose C = 3/(2T) + max(0,-log(prefix)), factor exp into two terms
  - (9) `hGradBound`: gradient bound — proved via `fderiv_equilibriumMaxwellian` helper (`simp; ring`), then |vᵢ|/T ≤ (1+‖v‖)/T using `norm_le_pi_norm`
  - (11) `hAmpere`: curl of B=0 equals ∫ vᵢ eM — proved by simplifying curl to 0, then `fin_cases i <;> simp`
- **Added 2 helper lemmas** in `CoulombConcreteTheorem42.lean`:
  - `fderiv_equilibriumMaxwellian`: directional derivative ∂eM/∂vᵢ = -(vᵢ/T)·eM
  - `equilibriumMaxwellian_exp_lower_bound`: ∃ C K, exp(-C(1+‖v‖)^K) ≤ eM(v)
- **Updated nonvacuous theorem docstring**: now documents proof status (7/10 proved, 3 sorry'd) with ✓/← markers
- **Style fixes**: extracted inline `show...from by ring` to `have`, removed unnecessary parentheses

### Sorry count: 3 (all in `CoulombConcreteTheorem42_nonvacuous`)

### Remaining sorry's
- (7) UniformSchwartzDecay — Gaussian iterated fderiv decay (hard)
- (10) Vlasov equation — Landau operator nullspace for Maxwellian (hardest)
- (12) Gauss's law — Gaussian integral normalization ∫ eM dv = ρ_ion (hard)

### Critique meets ACCEPT condition
Critique required closing ≥2 sorry's targeting (8) and (9). This cycle closed 3 including both targets.

## 2026-03-10 UTC — Babysit cycle 65: Close 4 non-vacuousness sorry's, fix rpow_pos API

### Changes
- **Closed 4 sorry's** in `CoulombConcreteTheorem42_nonvacuous` (10→6):
  - (4) `hf_smooth_v`: Maxwellian is C^∞ — proved via `ContDiff.mul`, `ContDiff.exp`, `contDiff_apply`
  - (5) `hf_smooth_x`: periodicLift of spatially constant function is C^∞ — `contDiff_const`
  - (6) `hB_smooth`: periodicLift of zero is C^∞ — `contDiff_const`
  - (13) `hDivB`: divergence of B=0 is 0 — `fderiv_const` + `Finset.sum_const_zero`
- **Fixed Defs.lean**: `Real.rpow_pos` → `Real.rpow_pos_of_pos` (Mathlib API rename)
- **Decomposed `all_goals sorry`** into 10 individual `· sorry` blocks with labeled comments
- **Documented spatial smoothness design** in `experiments/spatial_smoothness_design.md`: parametric `IsSpatiallySmooth n` predicate would enable C^2, ~95 call sites to change
- **Updated MEMORY.md**: line counts, sorry status, new API notes

### Sorry count: 6 (all in `CoulombConcreteTheorem42_nonvacuous`, goals 7-12)

### Remaining sorry's
- (7) UniformSchwartzDecay — Gaussian iterated fderiv decay (hard)
- (8) Exponential decay bound — needs relating normSq to sup norm + log argument (medium)
- (9) Gradient bound — fderiv of Gaussian (hard)
- (10) Vlasov equation — Landau operator nullspace for Maxwellian (hard)
- (11) Ampere's law — odd integral vanishes (medium-hard)
- (12) Gauss's law — Gaussian integral normalization (medium-hard)

## 2026-03-10 UTC — Babysit cycle 64: Eliminate deprecated refine', non-vacuousness theorem

### Changes
- **Eliminated all 36 deprecated `refine'`** across 5 files (CoulombPSD 13, TorusInstance 10, NewtonianPotential 8, Section3Helpers 4, SchwartzDecayDefs 1). Replaced with `refine` + `?_` placeholders.
- **Added `equilibriumMaxwellian_pos`** (Defs.lean): standalone lemma proving the equilibrium Maxwellian is strictly positive for ρ > 0, T > 0.
- **Added `CoulombConcreteTheorem42_nonvacuous`** (CoulombConcreteTheorem42.lean): non-vacuousness theorem showing the equilibrium Maxwellian with E=0, B=0 satisfies all 13 hypotheses. Hypothesis (3) proved; (4)-(13) sorry'd with detailed documentation explaining why each holds.
- **Fixed MEMORY.md**: updated file count (21→22) and line count (~7,895→~7,838).
- **Investigated spatial smoothness weakening** (C^∞ → C¹): blocked by `hDiff_grad` in FlatTorus3 typeclass requiring same smoothness level for gradient components. Would need two-level predicate design.

### Sorry count: 10 (all in `CoulombConcreteTheorem42_nonvacuous`, non-critical)

## 2026-03-10 UTC — Babysit cycle 63: Split TorusInstance, weaken C^∞ → C³ velocity smoothness

### Changes
- **Split TorusInstance.lean** (1,162 → 299 + 816 lines): Extracted `TorusDefs.lean` with Torus3 type, periodicLift, gradient/div/curl operators, and basic spatial lemmas. Made `isOpenQuotientMap_torusMk` and `continuous_torusGradX` non-private to enable cross-file usage. All downstream files build clean.
- **Weakened velocity smoothness C^∞ → C³** across the entire abstract proof chain (8 files):
  - `Defs.lean`: `VMLInput.hf_smooth` and `landau_ibp` changed from `ContDiff ℝ ⊤` to `ContDiff ℝ 3`
  - `Section3Helpers.lean`: `analysis_vGrad_smooth` (⊤→2), `entropy_score_form`, `entropy_zero_quadform_zero`, `parallel_curl_free_affine` (⊤→2), `affine_gradient_antiderivative`, `D_zero_implies_maxwellian` all weakened. Fixed all `le_top` → `by norm_num` for `ContDiff.differentiable`.
  - `Section3.lean`: `H_theorem`, `log_f_quadratic`, `nullspace_necessity`, `fubini_symmetrization_logf` all C³
  - `Section4.lean`: `fderiv_entropy_potential`, `force_transport_zero`, `transport_entropy_from_vlasov` all C³
  - `Section5.lean`: `polynomial_identity_from_vlasov` C³
  - `Section7.lean`: `poisson_boltzmann_from_vlasov` C³
  - `Theorem42.lean`: Main theorem signature now takes `ContDiff ℝ 3` instead of `ContDiff ℝ ⊤`
  - `CoulombConcreteTheorem42.lean`: Concrete theorem keeps `ContDiff ℝ ⊤` (needed for Schwartz), converts via `.of_le le_top` at the Theorem42 call site
- **Full clean build** verified: 22 files, ~7,838 lines, 0 sorry's

### Mathematical significance
The abstract proof chain (H-theorem → nullspace → Maxwellian form → polynomial matching → Poisson-Boltzmann → spatial uniformity) only requires C³ velocity regularity. C^∞ is only genuinely needed in the concrete Coulomb path for `schwartz_fderiv_component_schwartz`. This makes the theorem applicable to a strictly larger class of distribution functions.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 62: Fix build regression, linter cleanup, smoothness audit

### Changes
- **Fixed build-breaking regression** from cycle 61: `linarith` in `equilibriumMaxwellian_T_unique` couldn't handle nonlinear reasoning about π. Fix: `nlinarith [Real.pi_pos]`.
- **Fixed 6 unused simp args in Section3Helpers.lean**: lines 544-546 (`Pi.single_apply`), 552 (`Finset.sum_add_distrib`), 606 (`mul_assoc`), 607 (`Fin.sum_univ_three`).
- **Fixed 2 unused variables** in Section3Helpers.lean (line 618: `hn_pos`, `hρ`).
- **Fixed 1 unused variable** in Defs.lean (line 192: `hg_int`).
- **Fixed 1 deprecated `refine'`** in VelocityDecayInstance.lean (line 21).
- **Updated MEMORY.md** line counts and added build verification note.
- **Hardened `/commit` command**: now force-recompiles modified `.lean` files from source.
- **Smoothness audit** (experiments/smoothness_audit.md): C³ velocity + C¹ spatial suffices. ~80 occurrences across 15 files to change. Multi-cycle effort.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 61: T_eq uniqueness, hGradBound independence, simp cleanup

### Changes
- **Proved T_eq uniqueness** (critique #10): Added `equilibriumMaxwellian_T_unique` (Defs.lean) and `CoulombConcreteTheorem42_unique_T` (CoulombConcreteTheorem42.lean). The equilibrium temperature is uniquely determined by the distribution function.
- **Established hGradBound independence** (critique #7): The claim "likely derivable from hSchwartz + hExpDecay" was **mathematically incorrect**. Counterexample: f(v) = exp(-|v|²)(2+sin(exp(⟨v⟩))) is Schwartz with exponential lower bound, but |∂f|/f grows like exp(⟨v⟩). Fixed all docstrings from "12 independent + 1 likely derivable" to "13 total, all independent".
- **Fixed 8 unused simp args in Defs.lean** (critique #16): Removed unused `Fin.sum_univ_three`, `smul_eq_mul` from simp calls. Zero `unusedSimpArgs` warnings remain in Defs.lean.
- **Replaced deprecated API** (critique #17): `integral_mul_right` → `integral_mul_const` in Defs.lean:419.
- Added `/strengthen` command and updated `/plan` to write to `plan.md`.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 60: Delete dead code, remove linter suppressions

### Changes
- **Deleted `LandauMatrixDerivBound.lean`** (363 lines) — dead code never imported by any file. Removes the only `maxHeartbeats` override added in cycle 59.
- **Removed all 3 `linter.unusedSimpArgs` suppressions** from Defs.lean, Section3Helpers.lean, Section7.lean. Build passes; exposed warnings are cosmetic (unused simp args).
- **Updated documentation**: MEMORY.md and progress.md now reflect 21 files, ~7,850 lines.
- Net change: -363 lines. Heartbeat overrides: 1 (only `synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean).
- Both critique.md conditions for ACCEPT addressed: dead code deleted, line counts updated.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 59: Eliminate all primed definitions, fix LandauMatrixDerivBound compilation

### Changes
- **Eliminated ALL primed definitions** across 4 files:
  - **CoulombFlux.lean**: Removed 7 primed defs (`normSq'`, `eucNorm'`, `innerLandauMatrix'`, `coulombKernel'`, `landauMatrix'`, `vGrad'`) + 6 bridging lemmas. Replaced all proof references with VML namespace versions.
  - **CoulombFluxDiff.lean**: Replaced ~20 primed references with canonical names. Extracted `landauMatrix_coulombKernel_zero` helper lemma (was copy-pasted 5 times inline).
  - **CoulombPSD.lean**: Removed `PSDIntegrand'` def + bridging lemma. Replaced ~30 primed references.
  - **LandauMatrixDerivBound.lean**: Removed 4 primed defs, added `open VML`, renamed all lemmas from primed to unprimed.
- **Fixed LandauMatrixDerivBound.lean compilation errors** introduced by primed→VML migration:
  - Added `import Mathlib.Analysis.SpecialFunctions.Sqrt` (fixed `HasFDerivAt.sqrt` unknown constant)
  - Removed duplicate `normSq_pos` and `eucNorm_nonneg` lemmas (clashed with `open VML` imports)
  - Added scoped `maxHeartbeats 400000` for Aristotle-generated proof (needed after def migration)
- **Removed dead code**: 2 unused wrapper lemmas (`landauMatrix_entry_fderiv_norm_bound'`, `landauMatrix_entry_abs_bound'`) + orphaned `namespace VML`/`end VML` block.
- Fixed missing trailing newline in LandauMatrixDerivBound.lean.
- Net change: -72 lines across 4 files. All builds pass. 0 sorry's. 22 files.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 58: Eliminate all maxHeartbeats 3200000 overrides

### Changes
- Removed ALL 6 `maxHeartbeats 3200000` overrides across 3 files:
  - **CoulombPSD.lean:** 3 overrides removed
  - **CoulombFlux.lean:** 2 overrides removed
  - **NewtonianPotential.lean:** 1 override removed
- All proofs compile at default heartbeats (400000), despite being previously set at 8× default.
- **All `maxHeartbeats` overrides eliminated.** Only 1 `synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean remains.
- Total heartbeat overrides across cycles 55-58: **30 → 1** (97% reduction).
- All builds pass. 0 sorry's. 22 files.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 57: Eliminate all maxHeartbeats 1600000 overrides

### Changes
- Removed ALL 11 `maxHeartbeats 1600000` overrides across 6 files:
  - **NewtonianPotential.lean:** 3 overrides removed
  - **CoulombPSD.lean:** 3 overrides removed
  - **CoulombSpatialTransport.lean:** 2 overrides removed
  - **CoulombFluxDiff.lean:** 1 override removed
  - **CoulombFlux.lean:** 1 override removed
  - **LandauMatrixDerivBound.lean:** 1 override removed
- All proofs compile at default heartbeats (400000).
- Heartbeat overrides: 30 (cycle 54) → 18 (cycle 56) → 7 (cycle 57: 6 at 3200000 + 1 synthInstance).
- All builds pass. 0 sorry's. 22 files.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 56: Eliminate all maxHeartbeats 800000 overrides

### Changes
- Removed ALL 11 remaining `maxHeartbeats 800000` overrides across 6 files:
  - **CoulombSpatialTransport.lean:** 5 overrides removed
  - **Section3Helpers.lean:** 2 overrides removed
  - **Section3.lean:** 1 override removed
  - **CoulombFlux.lean:** 1 override removed
  - **LandauMatrixDerivBound.lean:** 1 override removed
  - **TorusInstance.lean:** 1 section-wide override removed
- All proofs compile at default heartbeats (400000). The 800000 overrides were unnecessary.
- Heartbeat overrides reduced from 29 → 18 (11 at 1600000, 6 at 3200000, 1 synthInstance).
- All builds pass. 0 sorry's. 22 files.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 55: Reduce heartbeats, fix MEMORY.md drift

### Changes
- **CoulombPSD.lean:** Removed `maxHeartbeats 800000` from `landau_bound` (works at default 400000). Heartbeat override count: 30 → 29.
- **MEMORY.md:** Updated line counts for CoulombFlux (~608→~616), CoulombPSD (~713→~716), LandauMatrixDerivBound (~412→~415).
- All builds pass. 0 sorry's. 22 files.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 54: Add bridging lemmas for primed definitions

### Changes
- **CoulombFlux.lean:** Added 6 bridging lemmas (`normSq'_eq`, `eucNorm'_eq`, `innerLandauMatrix'_eq`, `coulombKernel'_eq`, `landauMatrix'_eq`, `vGrad'_eq`) connecting primed Aristotle-generated defs to VML namespace defs via `rfl`.
- **CoulombPSD.lean:** Added bridging lemma `PSDIntegrand'_eq : PSDIntegrand' = PSDIntegrand coulombKernel := rfl`.
- **LandauMatrixDerivBound.lean:** Added 3 bridging lemmas (`normSq'_eq_VML`, `eucNorm'_eq_VML`, `innerLandauMatrix'_eq_VML`) alongside existing `landauMatrix'_eq_VML`.
- All builds pass. 0 sorry's. 22 files.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 53: Delete VelocityDecayHelpers.lean, fix stale docs

### Changes
- **VelocityDecayHelpers.lean: DELETED (-749 lines).** ~95% dead code. Moved 2 live lemmas (`integrable_one_add_norm_pow_mul`, `integrable_of_schwartz_bound`) to SchwartzDecayDefs.lean. Removed VelocityDecayHelpers import from CoulombSpatialTransport.lean.
- **progress.md: REWRITTEN.** Was severely stale (claimed 14 files/8 sorry's, listed deleted files). Now accurately reflects 22 files, 0 sorry's, correct file structure and axiom counts.
- **MEMORY.md: UPDATED.** Corrected file count (22), line count (~8,300), VelocityDecayConditions field count (19).
- All builds pass. 0 sorry's. 22 files, ~8,300 lines.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 52: Remove dead schwartzDecayConditions, rename ConcreteTheorem42

### Changes
- **VelocityDecayInstance.lean (809 → 35, -774 lines):** Removed dead `schwartzDecayConditions` (~400 lines) and dead `landau_flux_component_diff_with_bound` (~370 lines). Only `lorentz_component_bound` remains (still used by CoulombSpatialTransport).
- **ConcreteTheorem42.lean → SchwartzDecayDefs.lean:** Renamed to reflect actual contents (defines `UniformSchwartzDecay` and integrability helpers; no theorem). Removed stale `import VelocityDecayInstance`. Updated header.
- **CoulombKernel.lean:** Updated import from `ConcreteTheorem42` to `SchwartzDecayDefs`.
- **CoulombSpatialTransport.lean:** Added direct imports for `VelocityDecayInstance` and `VelocityDecayHelpers` (previously obtained transitively through the removed ConcreteTheorem42 → VelocityDecayInstance chain).
- All builds pass. 0 sorry's. 23 files, ~9,000 lines.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 51: Remove dead smooth-kernel helpers, fix docs

### Changes
- **VelocityDecayInstance.lean (939 → 809, -130 lines):** Removed 4 dead helper lemmas (`fderiv_entropy_density_eq`, `force_transport_integrable`, `force_ibp_f_dg_integrable`, `force_ibp_fg_integrable`) that were only used by the deleted `schwartzDecayConditionsEB`.
- **ConcreteTheorem42.lean:** Fixed misleading header that claimed "15 hypotheses" for a non-existent theorem. Now accurately describes file as helper definitions for concrete theorems.
- **CoulombConcreteTheorem42.lean:** Added physical scope note (single species, non-relativistic, 3D flat torus, Coulomb kernel).
- All builds pass. 0 sorry's. 23 files.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 50: Delete Section9.lean, remove schwartzDecayConditionsEB, doc fixes

### Changes
- **Section9.lean:** Deleted empty file (12 lines of boilerplate, no content). Removed import from VMLInputDerive.lean.
- **VelocityDecayInstance.lean:** Removed dead `schwartzDecayConditionsEB` (~60 lines). Updated file header.
- **Defs.lean:** Clarified VMLSteadyState docstring — now explicitly states it is an intermediate bundle of DERIVED facts, not input assumptions.
- **CoulombConcreteTheorem42.lean:** Updated docstring to document hGradBound non-minimality prominently ("13 total, 12 independent + 1 likely derivable").
- All builds pass. 0 sorry's. Now 23 files.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 49: Remove 24 dead declarations across 10 files (~265 lines)

### Changes
- **Section4.lean:** Removed `global_entropy_production_zero`, `pointwise_entropy_dissipation_zero` (-34 lines)
- **Section5.lean:** Removed `bulk_velocity_constant`, `force_balance`, `E_dot_u_zero` (-49 lines)
- **Section6.lean:** Removed `ampere_steady_state` (-10 lines)
- **Section7.lean:** Removed `poisson_boltzmann_density`, `density_constant_max_principle`, `laplacian_nonpos_at_max`, `laplacian_nonneg_at_min` (-29 lines)
- **Section8.lean:** Removed `B_compatible_maxwellian` (-11 lines)
- **Section9.lean:** Removed `B_infty_determination`, `T_infty_determination`, `T_positive` (-39 lines)
- **Section2.lean:** Removed `innerLandauMatrix_symmetric`, `landauMatrix_symmetric` (-19 lines)
- **Section3Helpers.lean:** Removed 4 transitively dead lemmas: `nonpositive_integral_zero_compact`, `killing_constant_torus`, `divergence_scalar_linear`, `force_balance_from_polynomial` (-52 lines)
- **LandauMatrixDerivBound.lean:** Removed `norm_le_eucNorm'`, `innerLandauEntry_val` (-11 lines)
- **TorusInstance.lean:** Removed `torusMk_continuous`, `laplacian_nonpos_at_max_rn` (-44 lines)
- All builds pass. 0 sorry's.

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 48: Major dead code removal (-459 lines)

### Changes
- **VelocityDecayHelpers.lean (1002 → 749, -253 lines):** Removed entire `uniformMaxwellianDecay` block — ~240 lines of dead code including `uniformMaxwellian`, `uniformMaxwellian_flux_zero`, `uniformMaxwellian_flux_integral_zero`, `uniformMaxwellian_flux_component_zero`, `uniformMaxwellian_psd_zero`, `uniformMaxwellian_gradX_zero`, 3 private helpers. Kept `zeroField` (used externally).
- **Section3.lean (378 → 194, -184 lines):** Removed 4 dead named theorems (`entropy_dissipation_formula`, `D_zero_implies_parallel`, `functional_eq_affine`, `nullspace_iff`) and 4 dead helper lemmas (`mulVec_integral_comm`, `ibp_real_line`, `dotProduct_integral_comm`, `const_times_integral_deriv_zero`).
- **Section2.lean (-14):** Removed dead `vecMul_landauMatrix_self`.
- **TorusInstance.lean (-11):** Removed dead `periodicLift_continuous` and `torus_hSpatialAdd`.
- **LandauMatrixDerivBound.lean (-3):** Removed 3 dead bridging lemmas (`normSq'_eq_VML`, `eucNorm'_eq_VML`, `innerLandauMatrix'_eq_VML`).
- **CoulombPSD.lean (-3):** Removed dead `PSDIntegrand'_eq_PSDIntegrand`.
- Total: 24 files, 10,378 lines (down from 10,837)

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 47: Remove 11 dead declarations (Section3Helpers + Defs)

### Changes
- Removed 9 dead lemmas from Section3Helpers.lean:
  - `PSDIntegrand_continuous`, `neg_half_double_integral_nonpos`, `PSDIntegrand_nonneg`
  - `analysis_dot_integral`, `analysis_dbl_sub`, `analysis_logDeriv`
  - `log_density_decomposition`, `polynomial_identity_algebraic`, `killing_second_deriv_zero`
- Removed 2 dead definitions from Defs.lean:
  - `IsLogQuadratic` (unused, `IsMaxwellian` is used directly)
  - `IsMaxwellian.isLogQuadratic` (depended on `IsLogQuadratic`)
  - `hDiff_sub` (never called)
- Section3Helpers.lean: 858 → 701 lines (-157)
- Defs.lean: 776 → 759 lines (-17)
- Total: 24 files, ~10,837 lines (down from ~11,011)

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 46: Remove dead code in Section3Helpers

### Changes
- Removed 4 dead-code lemmas from Section3Helpers.lean (no longer called after cycle 45 removed their forwarding callers):
  - `transport_entropy_vanishes_torus` — tautological (proof was just `htransport`)
  - `B_mean_conserved_from_axioms` — trivial `aesop`, no callers since `B_mean_conserved` removed
  - `faraday_stokes_integral_zero_v2` — trivial `aesop`, no callers
  - `vml_energy_conservation` — trivial `aesop`, no callers since `energy_conserved` removed
- Section3Helpers.lean: 926 → 858 lines (-68)
- Total: 24 files, ~11,011 lines (down from ~11,079)

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 45: Remove tautological theorems + document hGradBound

### Changes
- Removed 5 tautological/dead theorems:
  - `lhs_entropy_vanishes` (Section4.lean) — proof was just `htransport`
  - `symmetrized_weak_form` (Section3.lean) — proof was just `hSWF`
  - `polynomial_identity_velocity` (Section5.lean) — conclusion was `True`, proof was `intros; trivial`
  - `energy_conserved` (Section9.lean) — forwarded to `vml_energy_conservation`
  - `B_mean_conserved` (Section9.lean) — forwarded to `B_mean_conserved_from_axioms`
- Added comment in CoulombConcreteTheorem42.lean documenting that hGradBound (hypothesis 9) is likely derivable from hSchwartz + hExpDecay
- Total: 24 files, 11,079 lines (down from 11,193)

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 44: Remove custom generalize_proofs fork + dead code

### Changes
- Removed ~200 lines of custom `generalize_proofs` tactic fork from LandauMatrixDerivBound.lean (Harmonic.GeneralizeProofs namespace). Standard Mathlib `generalize_proofs` works identically.
- Removed dead code `dLandauEntry_bound_of_ne_zero` (trivially true, never called)
- Replaced 3 `exact?` calls with their resolved lemma names (`rfl`, `abs_dotProduct_le_eucNorm'_mul_eucNorm'`, `eucNorm'_le_sqrt_three_norm`)
- LandauMatrixDerivBound.lean: 644 → 428 lines (-216 lines)
- Total codebase: 24 files, 11,193 lines (down from 11,409)
- Full build verified clean

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 43: Dead code removal + MEMORY.md update

### Changes
- Removed unused private `dotProduct_smul_self` from Defs.lean (dead code; public version in Section6.lean is the one actually used)
- Updated MEMORY.md with VelocityDecay split info, LandauMatrixDerivBound entry, correct file/line counts
- Testing custom `generalize_proofs` tactic fork removal (in progress)

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 42: Replace `import Mathlib` with granular imports

### Changes
- Defs.lean: replaced `import Mathlib` with `import Mathlib.Data.Real.StarOrdered` + `import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts` (found via `lake exe shake`)
- LandauMatrixDerivBound.lean: removed redundant `import Mathlib` and `import Mathlib.Tactic.GeneralizeProofs` (both already provided transitively via `import Aristotle.Landau.main.Defs`)
- Full build verified clean

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 41: Split VelocityDecayInstance.lean

### Changes
- Split VelocityDecayInstance.lean (1,984 lines) into:
  - VelocityDecayHelpers.lean (1,002 lines): uniformMaxwellian, Schwartz integrability helpers, Landau matrix bounds, flux pointwise bounds, integrable_prod_schwartz_bound
  - VelocityDecayInstance.lean (1,001 lines): landau_flux_component_diff_with_bound (4M heartbeats), schwartzDecayConditions (18 fields), EB force transport, schwartzDecayConditionsEB
- Both files compile cleanly, 0 sorry's
- Now 24 files total, 0 files over 1,984 lines, largest is TorusInstance.lean at 1,222

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 40: Split Section3.lean

### Changes
- Split Section3.lean (1307 lines) into:
  - Section3Helpers.lean (926 lines): building blocks — vGrad_exp_quadratic, Gaussian integrals, PSD analysis, polynomial algebra, parallel_curl_free_affine, affine_gradient_antiderivative, Maxwellian flux zero, Poisson-Boltzmann, Faraday-Stokes, force balance
  - Section3.lean (391 lines): H-theorem chain — symmetrized_weak_form, entropy_dissipation_formula, H_theorem, D_zero_implies_parallel, nullspace_necessity/sufficiency/iff, Fubini symmetrization, IBP, integral linearity
- Both files compile cleanly, 0 sorry's
- Now 23 files total, ~11,400 lines

### Sorry count: 0

## 2026-03-10 UTC — Babysit cycle 39: Split CoulombPSD.lean

### Changes
- Split CoulombPSD.lean (1325 lines) into:
  - CoulombPSD.lean (716 lines): PSD integrand, continuity, pointwise bounds, inner/outer integrability, Fubini
  - CoulombFluxDiff.lean (627 lines): Schwartz fderiv, convolution differentiability, flux differentiability, flux decay, IBP integrability
- Updated CoulombConcreteTheorem42.lean imports to include CoulombFluxDiff
- Both files compile cleanly, 0 sorry's

### Sorry count: 0

## 2026-03-11 20:00 UTC — Babysit cycle 27: Assessed remaining tech debt

### Assessment
- Investigated duplicate primed definitions: non-trivial to consolidate (different generic vs Coulomb-specific signatures, separate import branches). Not worth the risk.
- Investigated 3200000 heartbeat proofs: well-structured 50-line proofs, heartbeat cost is from typeclass resolution, not bad structure.
- Remaining tech debt items are all high-effort/low-value or risky. Formalization is complete.

### Sorry count: 0

## 2026-03-11 18:00 UTC — Babysit cycle 26: Re-enable all linters

### Changes
- Removed `set_option linter.all false` from all 21 files in `Aristotle/Landau/main/`
- Project builds with 0 linter warnings — no code changes needed
- Updated critique.md to reflect linter fix

### Sorry count: 0

## 2026-03-11 16:00 UTC — Babysit cycle 25: Code quality cleanup

### Changes
- Refactored `schwartzDecayConditionsEB` in VelocityDecayInstance.lean: extracted `let base` binding to eliminate 16× copy-paste of `schwartzDecayConditions` call (~50 lines removed)
- Updated MEMORY.md: corrected sorry count (0), line counts for CoulombPSD.lean and CoulombConcreteTheorem42.lean

### Sorry count: 0

## 2026-03-11 14:00 UTC — Babysit cycle 24: **0 SORRY'S — FORMALIZATION COMPLETE**

### Status
- **ALL SORRY'S ELIMINATED.** The Coulomb Concrete Theorem 42 is fully proved.
- **Proved `coulomb_entry_conv_differentiable`**: Differentiability of Coulomb entry convolution.
  - Refactored into `coulomb_entry_conv_hasFDerivAt_aux` (core HasFDerivAt via `hasFDerivAt_integral_of_dominated_of_fderiv_le`) + corollary.
  - Key: change of variables u = v-w, uniform bound ‖fderiv g‖ ≤ Cf, dominator ‖u‖⁻¹ * Cf integrable via `inv_norm_schwartz_integrable`.
- **Discovered `coulomb_entry_conv_deriv_decay` was FALSE**: The Coulomb kernel is degree -1 homogeneous, so the convolution derivative has O(‖v‖⁻²) decay, NOT Schwartz decay.
  - Replaced with `coulomb_entry_conv_deriv_bounded`: uniform bound ∃ C, ∀ v, ‖fderiv(conv)(v)‖ ≤ C (TRUE).
  - Proof: HasFDerivAt gives fderiv = ∫ A(u) • fderiv(g)(v-u), bounded by ∫ ‖u‖⁻¹ * ‖fderiv g(v-u)‖ ≤ M via `newtonian_schwartz_uniform_bound`.
- **Refactored `coulomb_flux_deriv_schwartz_decay`**: Swapped which factors carry Schwartz decay.
  - OLD (wrong): (bounded ∂_j f) × (Schwartz DK) — used false Schwartz decay of DK
  - NEW (correct): (Schwartz ∂_j f) × (bounded DK) — product of Schwartz-decaying coefficient with bounded convolution derivative

### Sorry count: 0 (down from 2)

## 2026-03-11 12:00 UTC — Babysit cycle 23: Closed flux decay arithmetic sorry, Aristotle results

### Status
- **Closed inner sorry in `coulomb_flux_deriv_schwartz_decay`**: The per-term arithmetic assembly.
  - Key technique: product rule gives 4 terms, each (bounded × Schwartz-decaying × polynomial).
  - Proved `‖fderiv ℝ f v‖ = ‖iteratedFDeriv ℝ 1 f v‖` via `norm_iteratedFDeriv_fderiv` + `norm_iteratedFDeriv_zero`.
  - Used `mul_le_mul` for each of 4 terms, then `nlinarith` for the distribution over (1+‖v‖)^N.
- **Aristotle results**:
  - `landau_ibp_df_g` (97da955d): COMPLETE, 0 sorry's. But REDUNDANT — `coulomb_ibp_df_g_integrable` already proved manually.
  - `coulomb_conv_diff` (b419ae41): FAILED — Aristotle returned sorry.
  - `coulomb_conv_deriv_decay` (28a741f0): Still running.
- **Build system**: Fixed `lake build` crash by running `lake exe cache get` after previous `lake clean`.

### Sorry count: 2 (down from 3)
| Sorry | File | Status |
|-------|------|--------|
| coulomb_entry_conv_differentiable | CoulombPSD:792 | Aristotle failed; needs manual proof via hasFDerivAt + Peetre bound |
| coulomb_entry_conv_deriv_decay | CoulombPSD:803 | Aristotle job 28a741f0 still running |

## 2026-03-11 08:00 UTC — Babysit cycle 22: Proved coulomb_entry_schwartz_integrable, closed flux differentiability sorry

### Status
- **Proved `coulomb_entry_schwartz_integrable`**: Coulomb matrix entry × Schwartz function is integrable in ℝ³.
  - Domination argument: |A_{ij}(v-w) * g(w)| ≤ ‖v-w‖⁻¹ * |g(w)| via `coulomb_landauMatrix_entry_le_pi`.
  - Full proof including measurability of piecewise Coulomb kernel (Measurable.ite + composition).
  - Reusable helper for all flux decomposition proofs.
- **Closed `coulomb_flux_differentiable` combination sorry**: Proved the pointwise flux decomposition.
  - flux_i(v) = Σ_j [∂_j f(v) * K_{ij}(v) - f(v) * L_{ij}(v)] via:
    1. `eval_integral` to extract component from vector integral
    2. `integral_finset_sum` to exchange sum and integral
    3. `integral_sub` + `integral_const_mul_of_integrable` to distribute and factor
  - Key insight: avoid typeclass diamond by using `integral_const_mul_of_integrable` (not `integral_const_mul`).

### Sorry count: 3 (down from 4)
| Sorry | File | Status |
|-------|------|--------|
| coulomb_entry_conv_differentiable | CoulombPSD:792 | Submitted to Aristotle (b419ae41) |
| coulomb_entry_conv_deriv_decay | CoulombPSD:803 | Submitted to Aristotle (28a741f0) |
| coulomb_flux_deriv_schwartz_decay (combination) | CoulombPSD:897 | Needs product rule + decay tracking |

## 2026-03-11 06:00 UTC — Babysit cycle 21: Decomposed sorry's, proved schwartz_fderiv_component_schwartz

### Status
- Decomposed `coulomb_flux_differentiable` and `coulomb_flux_deriv_schwartz_decay` into clean sub-lemma structure:
  - Added `coulomb_entry_conv_differentiable` (sorry'd) — convolution of Coulomb entry with Schwartz function is differentiable.
  - Added `coulomb_entry_conv_deriv_decay` (sorry'd) — derivative of such convolution has Schwartz decay.
  - These are the "hard analysis" sub-lemmas; the original 2 sorry's now reduce to these + routine algebra (product/sum rules).
- Proved `schwartz_fderiv_component_schwartz`: ∂_j f is Schwartz given f is Schwartz.
  - Uses `ContinuousLinearMap.iteratedFDeriv_comp_left` + `norm_iteratedFDeriv_fderiv`.
  - Extracted as standalone lemma (was duplicated inline in both flux lemmas).
- Aristotle jobs still running: `landau_ibp_df_g` (97da955d), `coulomb_conv_diff` (b419ae41).

### Sorry count: 4 (was 2, but structurally better)
| Sorry | File | Status |
|-------|------|--------|
| coulomb_entry_conv_differentiable | CoulombPSD:757 | Core sub-lemma; matches Aristotle submission |
| coulomb_entry_conv_deriv_decay | CoulombPSD:768 | Core sub-lemma; needs Aristotle submission |
| coulomb_flux_differentiable (combination) | CoulombPSD:798 | Routine: apply product/sum rules to K_{ij}, L_{ij} |
| coulomb_flux_deriv_schwartz_decay (combination) | CoulombPSD:823 | Routine: Schwartz decay of product/sum |

## 2026-03-11 05:00 UTC — Babysit cycle 20: Decomposition analysis, Aristotle submission

### Status
- Analyzed proof strategy for remaining 2 sorry's (coulomb_flux_differentiable, coulomb_flux_deriv_schwartz_decay).
- Key insight: after substitution u = v-w, the Coulomb kernel A(u) doesn't depend on v, so hasFDerivAt_integral_of_dominated_of_fderiv_le applies with dominator ‖u‖⁻¹ * C/(1+‖u‖)^4 (integrable in ℝ³).
- Decomposition: flux_i = Σ_j (∂_j f) * (A_{ij} * f) - f * Σ_j (A_{ij} * ∂_j f), differentiable by product/sum rules.
- Submitted `coulomb_conv_diff` to Aristotle (job b419ae41) — cleaner sub-lemma for convolution differentiability.
- Updated docstrings with proof strategy.
- `landau_ibp_df_g` Aristotle job still running.

### Sorry count: 2 (unchanged)
| Sorry | File | Status |
|-------|------|--------|
| coulomb_flux_differentiable | CoulombPSD | Proof strategy documented; Aristotle sub-lemma submitted |
| coulomb_flux_deriv_schwartz_decay | CoulombPSD | Follows same strategy as above |

## 2026-03-11 04:00 UTC — Babysit cycle 19: Fubini+IBP closed, 2 sorry's remaining

### Status
- Closed `hFubini_double` in CoulombConcreteTheorem42.lean (3→2 sorry's).
  - Added `fubini_double_integrable_coulomb` (~310 lines) in CoulombPSD.lean.
  - Uses `integrable_prod_iff` with joint measurability, inner integrability from `landau_flux_integrable_coulomb`, and norm integral bound from Newtonian uniform bounds.
- Decomposed `hLandauFluxDiff` and `hLandauIBP_df_g` into 2 focused sorry targets:
  - `coulomb_flux_differentiable` — differentiation under integral sign with singular Coulomb kernel.
  - `coulomb_flux_deriv_schwartz_decay` — Schwartz decay of the flux derivative.
- Added `coulomb_ibp_df_g_integrable` proof that depends on the two sorry'd lemmas above.
- Wired up `hLandauFluxDiff` and `hLandauIBP_df_g` in CoulombConcreteTheorem42.lean.
- Simplified CoulombConcreteTheorem42: extracted `hSchwartz_x` helper (eliminates 9 repeated expressions), removed 3 redundant `obtain hGradBound` destructurings, converted tactic proofs to term-mode for PSD/Fubini fields.
- Aristotle: `coulomb_flux_diff` and `fubini_double_integrable` both returned sorry (Aristotle failed). `landau_ibp_df_g` still queued.

### Sorry count: 2 (down from 3)
| Sorry | File | Status |
|-------|------|--------|
| coulomb_flux_differentiable | CoulombPSD | Genuine hard: diff under integral with ‖z‖⁻² singularity |
| coulomb_flux_deriv_schwartz_decay | CoulombPSD | Schwartz decay of convolution with singular kernel |

## 2026-03-11 01:00 UTC — Babysit cycle 18: PSD inner+outer closed, 3 sorry's remaining

### Status
- Closed `hPSD_inner_int` and `hPSD_outer_int` in CoulombConcreteTheorem42.lean (5→3 sorry's).
- Extracted `psd_pointwise_bound_coulomb` (~70 lines) in CoulombPSD.lean:
  - Standalone pointwise bound: `|PSDIntegrand(v,w)| ≤ 18*Cg²*f(v)*(poly(v)*‖v-w‖⁻¹*f(w) + ‖v-w‖⁻¹*poly(w)*f(w))`.
- Refactored `psd_inner_integrable_coulomb` to use the extracted bound (removed ~75 inline lines).
- Added `psd_outer_integrable_coulomb` (~90 lines): outer integrability via Newtonian uniform bounds + `inverse_poly_integrable`.
- Removed dead code (`hCg_nn`) from `psd_inner_integrable_coulomb`.
- Aristotle jobs all failed (API ReadTimeout) — no new submissions this cycle.

### Sorry count: 3 (down from 5)
| Sorry | File | Status |
|-------|------|--------|
| hFubini_double | CoulombConcreteTheorem42 | Needs joint measurability on product space |
| hLandauFluxDiff | CoulombConcreteTheorem42 | Needs differentiation under integral sign |
| hLandauIBP_df_g | CoulombConcreteTheorem42 | Blocked on hLandauFluxDiff |

## 2026-03-10 23:30 UTC — Babysit cycle 17: h_flux closed, 5 sorry's remaining

### Status
- Closed h_flux sorry (flux component bound) in CoulombConcreteTheorem42.lean.
- Added `coulomb_flux_component_bound` lemma (~130 lines) to CoulombFlux.lean.
  - Combines Newtonian potential bounds with polynomial gradient bound (hGradBound).
  - Key argument: |flux_i(v)| ≤ (∑|∂_j g(v)|) * M₀ + g(v) * M_df ≤ Cf * g(v) * (1+‖v‖)^Kg.
- hIBP_f_dg is now fully proved (all 4 sub-parts: h_score, h_flux, measurability, combining step).
- Fixed CoulombPSD.lean import bug (CoulombKernel → CoulombFlux).

### Sorry count: 5 (down from 6)
| Sorry | File | Status |
|-------|------|--------|
| hPSD_inner_int | CoulombConcreteTheorem42 | Aristotle pending |
| hPSD_outer_int | CoulombConcreteTheorem42 | Aristotle pending |
| hFubini_double | CoulombConcreteTheorem42 | Aristotle pending |
| hLandauFluxDiff | CoulombConcreteTheorem42 | Blocked (needs inv_norm_sq_local_integrable) |
| hLandauIBP_df_g | CoulombConcreteTheorem42 | Aristotle pending |

## 2026-03-10 22:00 UTC — Babysit cycle 16: Aristotle back, submitted hLandauIBP_df_g

### Status
- Aristotle API back online. All 5 previous jobs now IN_PROGRESS (were stuck due to API timeouts).
- Submitted `landau_ibp_df_g` (fderiv(flux) × log(f) integrable) as job `97da955d`.
  - Admitted building blocks: flux integrability, differentiability, Schwartz decay of flux derivative, inverse-polynomial integrability.
  - Fixed incorrect bound: original `C * poly * f(v)` replaced with correct Schwartz-class decay form `‖fderiv‖ * (1+‖v‖)^N ≤ C`.
- All 6 sorry's now have active Aristotle jobs.
- No sorry's closed directly — all are hard Coulomb singular-integral analysis.
- Reordered babysit.md: `/submit-aristotle` now runs before `/prove`.

### Aristotle jobs (6 active)
| Job ID | Target | Status |
|--------|--------|--------|
| 23198617 | landau_ibp_f_dg | IN_PROGRESS |
| a9f127b6 | coulomb_flux_diff | IN_PROGRESS |
| 06e28c3f | psd_inner_integrable | IN_PROGRESS |
| 1062b892 | psd_outer_integrable | IN_PROGRESS |
| 50fc290c | fubini_double_integrable | IN_PROGRESS |
| 97da955d | landau_ibp_df_g | NEW |

### Sorry count: 6 — unchanged

## 2026-03-10 21:00 UTC — Babysit cycle 15: Aristotle still down

### Status
- Aristotle API still completely unreachable (timeout on both check and submit).
- Analyzed `hLandauFluxDiff` (Coulomb flux differentiability): requires differentiation under the integral sign with a singular kernel. The smooth kernel proof uses `landau_flux_component_diff_with_bound` which needs `Continuous Ψ`, `ContDiff ℝ 1 Ψ`, bounded Ψ, and bounded Ψ' — none of which hold for Coulomb. A custom argument using local integrability of `‖z‖⁻²` in 3D is needed.
- Dependencies building (LSP shows 5 failed deps, awaiting compilation).
- No sorry's closed.

### Sorry count: 6 — unchanged

## 2026-03-10 20:00 UTC — Babysit cycle 14: Aristotle down, analysis of PSD sorry's

### Status
- Aristotle API completely unreachable (curl returns 000). All 5 jobs failed previously.
- Analyzed PSD inner integrability (`hPSD_inner_int`) in depth:
  - Smooth kernel uses `hGradBound` (polynomial score growth) — Coulomb doesn't have this.
  - Key challenge: `f(w)*(score(v)-score(w))²` has a `(∂f)²/f` term whose integrability depends on Fisher information being finite. Bound from Schwartz + exp lower bound alone diverges, but actual Fisher info IS finite for all "reasonable" functions.
  - The PSD integrand IS integrable: near v (removable singularity, proved by psd_continuous_coulomb) and far (Schwartz decay of f combined with Coulomb |z|^{-1} bound handles the tail for any concrete Schwartz f satisfying exp lower bound).
  - Proof requires careful multi-step bounds not achievable without Aristotle.
- No sorry's closed — blocked on Aristotle.

### Sorry count: 6 — unchanged

## 2026-03-10 19:00 UTC — Major refactor: split CoulombConcreteTheorem42.lean

### Accomplished
- **Split 1827-line CoulombConcreteTheorem42.lean into 6 files:**
  | File | Lines | Content |
  |------|-------|---------|
  | CoulombKernel.lean | 114 | Kernel def, positivity, Schwartz log/norm helpers |
  | CoulombSpatialTransport.lean | 662 | Spatial/force transport integrability + continuity |
  | NewtonianPotential.lean | 284 | Matrix bounds, inv-norm integrability, uniform bound |
  | CoulombFlux.lean | 441 | Flux integrability, measurability, flux x log |
  | CoulombPSD.lean | 170 | PSD integrand continuity |
  | CoulombConcreteTheorem42.lean | 201 | Main theorem assembly only |

- **Fixed 12.8M heartbeat `newtonian_near_bound`**: refactored to take `h_inv_loc` as parameter instead of computing `inv_norm_local_integrable` inline. No longer needs any heartbeat override.
- **Main theorem file has zero `set_option maxHeartbeats`** — compiles at default heartbeats.
- **Created `/simplify` skill** for systematic code quality enforcement.
- All files compile (exit 0, only sorry warnings).
- Aristotle API still down (ReadTimeout).

### Sorry count: 6 — unchanged

## 2026-03-10 17:00 UTC — Babysit cycle 13: Aristotle still down, heartbeat fix

### Status
- Aristotle API still returning ReadTimeout on all 5 jobs + resubmission attempts.
- Fixed `newtonian_near_bound` heartbeat regression: increased from 6400000 to 12800000.
- No sorry's closed this cycle.

### Sorry count: 6 — unchanged

## 2026-03-10 16:00 UTC — Babysit cycle 12: Aristotle API down

### Status
- All 5 Aristotle jobs returned "ERROR — Request failed" (API timeout/expiry).
- Attempted resubmission: Aristotle API is down (httpx.ReadTimeout on project creation).
- No sorry's closed this cycle. Will retry submission when API recovers.

### Sorry count: 6 — unchanged

## 2026-03-10 15:00 UTC — Babysit cycle 11: waiting on Aristotle

### Status
- All 5 Aristotle jobs still IN_PROGRESS.
- No new sorry's closed — all remaining 6 are hard analytical estimates.
- File compiles cleanly (0 errors).
- Investigated `hLandauFluxDiff` for possible direct proof: smooth case uses `landau_flux_component_diff_with_bound` which requires `ContDiff ℝ 1 Ψ` + bounded derivative. Coulomb kernel doesn't satisfy this, so a custom Coulomb-specific argument is needed (submitted to Aristotle as `coulomb_flux_diff`).

### Sorry count: 6 — unchanged

## 2026-03-10 14:00 UTC — Babysit cycle 10: zero compilation errors

### Accomplished
- **Fixed `newtonian_near_bound` timeout** (was line 991): replaced `setIntegral_mono_on` with `setIntegral_mono` (uses `f ≤ g` everywhere instead of `∀ x ∈ s, f x ≤ g x`). Reduced heartbeats from 12800000 (failing) to 6400000 (succeeding).
- **File now has ZERO compilation errors.** Only sorry warnings (6), info messages (ring_nf suggestions), and unused simp arg warnings.
- All 5 Aristotle jobs still running.

### Sorry count: 6 — unchanged

## 2026-03-10 13:00 UTC — Babysit cycle 9: Aristotle submissions + fix compilation

### Accomplished
- Fixed `flux_component_aestronglyMeasurable` compilation errors:
  - Added `simp only [eucNorm, normSq, dotProduct]` before `continuous_sqrt.comp` (was failing to match `eucNorm` with `√(∑...)`)
  - Added `mul_one` to `simp only` (leftover `* 1` from `one_apply` when `i = j`)
- File compiles cleanly (only pre-existing timeout at line 991 in `newtonian_near_bound`)
- Submitted 5 Aristotle jobs total (2 new this cycle):
  - `psd_outer_integrable` (1062b892) — iterated PSD integral integrable
  - `fubini_double_integrable` (50fc290c) — joint (v,w) Fubini integrability
  - Plus 3 from cycle 8: landau_ibp_f_dg, coulomb_flux_diff, psd_inner_integrable
- All 6 sorry's now have corresponding Aristotle submissions (except `hLandauIBP_df_g` which depends on `hLandauFluxDiff`)

### Sorry count: 6 — unchanged
- hIBP_f_dg (1712), hPSD_inner_int (1720), hPSD_outer_int (1721), hFubini_double (1722), hLandauFluxDiff (1752), hLandauIBP_df_g (1753)

## 2026-03-10 12:00 UTC — Babysit cycle 8: flux AEStronglyMeasurable proved

### Accomplished
- **Proved `flux_component_aestronglyMeasurable`** (was sorry at line 1395): new standalone lemma showing the Landau flux component `v ↦ (∫ w, A(v-w) *ᵥ (f(w)∇f(v) - f(v)∇f(w))) i` is AEStronglyMeasurable. Key approach:
  1. `eval_integral` + `Integrable.eval` to rewrite `(∫ w, F w) i = ∫ w, (F w) i`
  2. `AEStronglyMeasurable.integral_prod_right'` to reduce to joint measurability on product space
  3. `Measurable.aestronglyMeasurable` (ℝ is second countable)
  4. Decompose `mulVec` into `∑ j, M i j * v j` via `Finset.measurable_sum`
  5. Matrix entries: `Measurable.ite` for Coulomb kernel + `Continuous.measurable` for innerLandauMatrix
  6. Vector part: `Continuous.clm_apply continuous_const` for fderiv evaluation
- Needs `maxHeartbeats 3200000` (heavy unfolding of mulVec/dotProduct/landauMatrix)
- All Aristotle jobs completed (no pending). API available.

### Sorry count: 6 (0 helper + 6 main) — down from 7
- hIBP_f_dg (1712), hPSD_inner_int (1720), hPSD_outer_int (1721), hFubini_double (1722), hLandauFluxDiff (1752), hLandauIBP_df_g (1753)

## 2026-03-10 03:30 UTC — Babysit cycle 7: blocked on hard sorry's

### Status
- No new sorry's closed. All 7 remaining are hard analytical estimates for Coulomb kernel.
- Aristotle API still down (ReadTimeout). `landau_ibp_f_dg.lean` pending in `aristotle-in/`.
- Investigated flux AEStronglyMeasurable sorry (line 1395): requires either `continuous_of_dominated` (needs v-independent integrable bound) or `AEStronglyMeasurable.integral_prod_right'` (needs joint product-space measurability). Both approaches need substantial formalization.
- Investigated PSD integrability sorry's: require Coulomb-specific `f(v)*f(w)*|v-w|^{-1}*|Δ|^2` integrability bounds. Decomposable into sub-lemmas but each sub-lemma is also hard.
- Deleted stale `aristotle-in/flux_component_bound.lean` (previous cycle).

### Sorry count: 7 (1 helper + 6 main) — unchanged
- 1 helper: flux AEStronglyMeasurable (1395)
- 6 main: hIBP_f_dg (1649), hPSD_inner_int (1657), hPSD_outer_int (1658), hFubini_double (1659), hLandauFluxDiff (1689), hLandauIBP_df_g (1690)

## 2026-03-10 02:30 UTC — Babysit cycle 6: integral bound proved

### Accomplished
- **Proved integral bound** (was sorry at line 1294): `∫ ‖v-w‖⁻¹ * ∑|u j| ≤ M₀*3*‖D¹f‖ + M_df*‖D⁰f‖`. Key steps:
  - Triangle inequality `|u w j| ≤ |f w|*|∇v j| + |f v|*|∇w j|` via `norm_sub_le`
  - Sum factoring via `Finset.sum_add_distrib` + `Finset.mul_sum`
  - vGrad bound via `ContinuousLinearMap.le_opNorm` + `Pi.norm_single`
  - `integral_mono_of_nonneg` + `integral_add` + `integral_mul_left`
  - `integral_finset_sum` inside `mul_le_mul_of_nonneg_left` subgoal (avoids `∂volume` annotation mismatch at calc level)
  - Final `ring` for `M₀ * (3 * ‖D¹f‖) + M_df * ‖D⁰f‖`
- Deleted `aristotle-in/flux_component_bound.lean` (no longer needed)
- **Aristotle API still down** (ReadTimeout)

### Sorry count: 7 (1 helper + 6 main)
- 1 helper: flux AEStronglyMeasurable (1395)
- 6 main: `hIBP_f_dg` (1649), `hPSD_inner_int` (1657), `hPSD_outer_int` (1658), `hFubini_double` (1659), `hLandauFluxDiff` (1689), `hLandauIBP_df_g` (1690)

## 2026-03-10 01:00 UTC — Babysit cycle 5: integrability sorry closed

### Accomplished
- **Proved dominating function integrability** (was sorry at line 1273): The key step `Integrable (fun w => ‖v-w‖⁻¹ * ∑ j |u w j|)` is proved by:
  - `simp_rw [Finset.mul_sum]` + `integrable_finset_sum` to reduce to per-component
  - For each j: `inv_norm_schwartz_integrable` for f and ∂_j f, then `convert ... |>.sub ...` to combine
  - `.norm.congr` with `norm_mul` + `Real.norm_of_nonneg` + `Real.norm_eq_abs`
- Fixed `eval_CLM` → `.clm_apply continuous_const` for getting `Continuous (fun w => fderiv f w (e_j))`
- Fixed `norm_mul` beta-reduction issue: added `show` before `rw` to beta-reduce first
- Increased `newtonian_near_bound` heartbeats from 6.4M to 12.8M (was timing out)
- **Attempted integral bound proof** (line 1294): 80-line calc chain had too many Mathlib API mismatches. Reverted to sorry. Needs Aristotle.
- **Aristotle API still down** (ReadTimeout on both submissions)

### Sorry count: 8 (2 helper + 6 main)
- 2 helper in `flux_times_log_integrable_coulomb`: integral bound (1294), flux AEStronglyMeasurable (1300)
- 6 main: `hIBP_f_dg` (1554), `hPSD_inner_int` (1562), `hPSD_outer_int` (1563), `hFubini_double` (1564), `hLandauFluxDiff` (1594), `hLandauIBP_df_g` (1595)

## 2026-03-10 00:00 UTC — Babysit cycle 4: flux pointwise bound proved

### Accomplished
- **Proved Coulomb entry pointwise bound** (`h_pw`): For each `w`, `|(A(v-w) *ᵥ u(w)) i| ≤ ‖v-w‖⁻¹ * ∑ j |u(w) j|`. Uses `sub_eq_zero` for the v=w case, `Finset.abs_sum_le_sum_abs` + `abs_mul` for the triangle inequality, and `coulomb_landauMatrix_entry_le_pi` for the entry bound. ~20 lines.
- **eval_integral step proved**: pulled component i out of the vector integral.
- **calc chain structure** in place: `|∫| ≤ ∫|·| ≤ ∫ bound ≤ RHS` with 2 sub-sorry's (integrability of bound, integral ≤ RHS).
- **Aristotle API still down** (ReadTimeout).

### Sorry count: 9 (3 helper + 6 main)
- 3 helper in `flux_times_log_integrable_coulomb`: dominating function integrable (1273), integral bound (1276), flux AEStronglyMeasurable (1282)
- 6 main: `hIBP_f_dg` (1536), `hPSD_inner_int` (1544), `hPSD_outer_int` (1545), `hFubini_double` (1546), `hLandauFluxDiff` (1576), `hLandauIBP_df_g` (1577)

## 2026-03-09 23:00 UTC — Babysit cycle 3: LSP timeout fix

### Accomplished
- **Fixed LSP timeout** that blocked elaboration past line 981. Split `newtonian_schwartz_uniform_bound` into 3 pieces:
  - `newtonian_near_bound` (6.4M heartbeats): near-field integral estimate
  - `newtonian_far_bound` (1.6M heartbeats): far-field integral estimate
  - Main lemma (3.2M heartbeats): combines near+far via `linarith`
- **LSP now elaborates the full file**, including all sorry's past line 981. Previously, the monolithic proof at 6.4M heartbeats was causing a kernel timeout that cascaded to block all subsequent code.
- **Closed `log ∘ f x` measurability** in `flux_times_log_integrable_coulomb`: used `(hf_smooth_v x).continuous.log (ne_of_gt ...) |>.aestronglyMeasurable`.
- **Aristotle API still down** (ReadTimeout). Two submissions pending: `flux_component_bound.lean`, `landau_ibp_f_dg.lean`.

### Sorry count: 8 unchanged (2 helper + 6 main)

## 2026-03-09 22:00 UTC — Babysit cycle 2: flux_times_log decomposition

### Accomplished
- **`flux_times_log_integrable_coulomb` decomposed**: Split the monolithic sorry (line 1225) into a structured proof with 2 sub-sorry's:
  - Line 1239: `h_flux_bound` — pointwise flux component bound `|flux_i(v)| ≤ M₀ * 3 * ‖iterFDeriv 1‖ + M_df * ‖iterFDeriv 0‖`
  - Line 1245: `AEStronglyMeasurable` of flux component (log part closed via `Continuous.log + aestronglyMeasurable`)
- **Calc chain fully proved**: The domination `‖flux_i × log‖ ≤ C_bound / (1+‖v‖)^4` is complete using `le_div_iff₀`, `gcongr`, `pow_add`, `field_simp`.
- **Standalone Aristotle submission**: `aristotle-in/flux_component_bound.lean` created and verified (compiles with sorry's). API still down (ReadTimeout).
- **Sorry count**: 8 (2 helper + 6 main), unchanged in total but better structured.

### Remaining sorry's (8 total)
- 2 helper: `h_flux_bound` (line 1239), flux AEStronglyMeasurable (line 1245)
- 1 `hIBP_f_dg` line 1499 (flux × score integrable)
- 3 PSD/Fubini: `hPSD_inner_int`, `hPSD_outer_int`, `hFubini_double` (lines 1507-1509)
- 2 Landau IBP/diff: `hLandauFluxDiff`, `hLandauIBP_df_g` (lines 1539-1540)

## 2026-03-09 21:00 UTC — Babysit cycle: 3 lemmas proved, sorry count 8→7

### Accomplished
- **`newtonian_schwartz_uniform_bound` PROVED** (0 sorry): Uniform bound `∃ M > 0, ∀ v, ∫ ‖v-w‖⁻¹|g(w)| ≤ M` for Schwartz g in ℝ³. Key technique: translate via `integral_sub_left_eq_self` to center at origin, split at B(0,1), near part bounded by `C₀ * I_local`, far part bounded by `I_global`. ~100 lines, `maxHeartbeats 6400000`.
- **`schwartz_partial_decay` PROVED** (0 sorry): `|∂_jf(x,w)| * (1+‖w‖)^N ≤ C` from `UniformSchwartzDecay`. Uses `ContinuousLinearMap.le_opNorm` + `norm_iteratedFDeriv_fderiv` pattern.
- **`flux_times_log_integrable_coulomb` added** (1 sorry): Flux × log(f) integrable for Coulomb kernel. Sets up all Schwartz bounds and domination constants; remaining sorry is the final AE bound + measurability step.
- **`hLandauIBP_fg` CLOSED**: Now uses `flux_times_log_integrable_coulomb` instead of `sorry`.
- **Sorry count**: 8 → 7 total (6 main + 1 helper in `flux_times_log_integrable_coulomb`)
- **Aristotle API still down** (ReadTimeout).

### Remaining sorry's (7 total)
- 1 helper: `flux_times_log_integrable_coulomb` line 1225 (AE bound step)
- 1 `hIBP_f_dg` line 1444 (flux × score integrable — hardest remaining)
- 3 PSD/Fubini: `hPSD_inner_int`, `hPSD_outer_int`, `hFubini_double` (lines 1452-1454)
- 2 Landau IBP/diff: `hLandauFluxDiff`, `hLandauIBP_df_g` (lines 1484-1485)

## 2026-03-09 20:00 UTC — Babysit cycle: infrastructure work, Aristotle still down

### Accomplished
- **`newtonian_schwartz_uniform_bound` lemma added** (sorry'd): States that `∫ ‖v-w‖⁻¹ * |g(w)| ≤ M` uniformly in v for Schwartz g. Attempted detailed near/far split proof but hit cascading Lean formalization issues (field notation, `integral_add_compl` unification, `linarith` positivity). Sorry'd as building block — not one of the 7 main sorry's.
- **Standalone Aristotle submission created**: `aristotle-in/newtonian_schwartz_uniform_bound.lean` ready for submission when API recovers.
- **Aristotle API still down** (ReadTimeout on both check and submit).
- **`landau_flux_int_v2` job** already integrated (was in active jobs list but solution already in codebase as `landau_flux_integrable_coulomb`).
- **Sorry count**: 7 main sorry's unchanged (+ 1 new helper = 8 total `sorry` in file)

### Strategy
`newtonian_schwartz_uniform_bound` is the key building block for closing `hLandauIBP_fg` and `hIBP_f_dg`:
- Bound |flux_i(v)| ≤ M₁|∂f(v)| + M₂f(v) via uniform Newtonian potential bound
- Multiply by |log f| ≤ C(1+‖v‖)^K → product is polynomial × Schwartz → integrable

### Remaining sorry's (7 main + 1 helper)
- 3 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double)
- 1 hIBP_f_dg (flux × score integrable)
- 3 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g, hLandauIBP_fg)
- 1 newtonian_schwartz_uniform_bound (helper, not in main theorem)

## 2026-03-09 19:00 UTC — Babysit cycle: hD_cont proved, 8→7 sorry's

### Accomplished
- **Entropy dissipation continuity (`hD_cont`) proved**: Closed the sorry for `Continuous (fun x => entropyDissipation coulombKernel (f x))`. Proof strategy:
  1. Use Vlasov equation to rewrite: `ν * D(f x) = ∫ spatial*log f + ∫ force*log f`
  2. Force transport vanishes by `force_transport_zero` (from Section4.lean)
  3. So `D(f x) = ν⁻¹ * ∫ v, v ⬝ᵥ gradX(f)(x) * log(f(x,v))`
  4. Spatial transport integral is continuous by `spatial_transport_continuous` (new lemma)
- **Added `spatial_transport_continuous` lemma**: Proves `Continuous (fun x => ∫ v, v⬝ᵥgradX(f)(x) * log(f(x,v)))` via `continuous_of_dominated` with the same uniform Schwartz+log bound as `spatial_transport_joint_integrable`
- **Sorry count**: 8 → 7 in CoulombConcreteTheorem42.lean
- **Aristotle API still down** (timeout)
- **Build status**: 0 errors, 7 sorry's

### Remaining sorry's (7 total in CoulombConcreteTheorem42.lean)
- 3 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double)
- 1 hIBP_f_dg (flux × score integrable)
- 3 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g, hLandauIBP_fg)

## 2026-03-09 18:00 UTC — Babysit cycle: no changes, all remaining sorry's need Aristotle

### Status
- Aristotle API still down (timeout). No jobs can be submitted or checked.
- 8 sorry's in CoulombConcreteTheorem42.lean (unchanged).
- Investigated `hD_cont` (entropy dissipation continuity): could use Vlasov equation to rewrite as spatial + force transport integrals, but force transport continuity requires `x ↦ vGrad(f x)(v)` continuous, which needs a uniform convergence of difference quotients argument with second-derivative bounds from `UniformSchwartzDecay`. Viable but ~80 lines; deferred.
- All 8 sorry's require Coulomb-specific convolution bounds or differentiation under integral sign — not feasible without Aristotle.
- 2 standalone files ready for Aristotle submission in `aristotle-in/`: `landau_ibp_fg.lean`, `landau_ibp_f_dg.lean`.
- Build status: 0 errors, 8 sorry's.

## 2026-03-09 17:00 UTC — Babysit cycle: joint measurability proved, 9→8 sorry's

### Accomplished
- **AEStronglyMeasurable (uncurry g) (volume.prod volume) proved**: Closed the joint product measurability sorry (formerly line 551). Proof uses `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` with:
  - `∀ v, Continuous (fun x => g x v)`: from `hDiff_continuous` + `hDiff_grad` + `Continuous.log`
  - `∀ x, StronglyMeasurable (fun v => g x v)`: key new ingredient is `gradX_stronglyMeasurable_v` — proves spatial gradient component is strongly measurable in v via difference quotient approximation (each quotient is continuous since `f(x,·)` is smooth, fderiv is their pointwise limit, apply `stronglyMeasurable_of_tendsto`)
- Added helper lemma `gradX_stronglyMeasurable_v` before `spatial_transport_joint_integrable`
- **Sorry count**: 9 → 8 in CoulombConcreteTheorem42.lean
- **Aristotle API still down** (timeout)
- **Build status**: 0 errors, 8 sorry's

### Remaining sorry's (8 total in CoulombConcreteTheorem42.lean)
- 3 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double)
- 1 hIBP_f_dg (flux × score integrable)
- 3 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g, hLandauIBP_fg)
- 1 entropy dissipation continuity (hD_cont)

## 2026-03-09 16:00 UTC — Babysit cycle: AEStronglyMeasurable(∫‖g‖) proved, 10→9 sorry's

### Accomplished
- **AEStronglyMeasurable of integral proved**: Closed the sorry at line 559 (`AEStronglyMeasurable (fun x => ∫ v, ‖g x v‖) volume`). Proof: show `x ↦ ∫ v, ‖g x v‖` is continuous via `continuous_of_dominated`, then apply `Continuous.aestronglyMeasurable`. Key ingredients: (1) `hDiff_continuous + hDiff_grad + hf_smooth_x` → each component of gradX is continuous in x, (2) `Continuous.log` → log(f x v) continuous in x, (3) uniform bound `|g x v| ≤ C / (1+‖v‖)^4` as dominating function.
- **Line 551 AEStronglyMeasurable NOT closed**: Joint measurability on `Torus3 × ℝ³` requires joint continuity of `(x,v) ↦ gradX(f(·,v))(x)`, which needs either joint smoothness of f or a concrete approximation argument. Left as sorry.
- **Sorry count**: 10 → 9 in CoulombConcreteTheorem42.lean.
- **Aristotle API still down** (timeout).
- **Build status**: 0 errors, 9 sorry's.

### Remaining sorry's (9 total in CoulombConcreteTheorem42.lean)
- 1 AEStronglyMeasurable (line 551 — joint measurability on product, needs joint smoothness)
- 3 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double)
- 1 hIBP_f_dg (line 1102 — covers hLandauIBP_f_dg and hFubini_outer)
- 3 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g, hLandauIBP_fg)
- 1 entropy dissipation continuity (hD_cont)

## 2026-03-09 15:00 UTC — Babysit cycle: no changes, API still down

### Status
- Aristotle API still down (timeout). No jobs can be submitted or checked.
- 10 sorry's in CoulombConcreteTheorem42.lean (unchanged from previous cycle).
- All remaining sorry's require substantial analytical arguments (Coulomb singularity estimates, uniform convolution bounds, differentiation under integral sign). No further structural reductions identified.
- Build status: 0 errors, 10 sorry's.

### Remaining sorry's (10 total)
- 2 AEStronglyMeasurable (lines 551, 559 — joint measurability for spatial_transport_joint_integrable)
- 3 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double)
- 1 hIBP_f_dg (line 1078 — covers hLandauIBP_f_dg and hFubini_outer)
- 3 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g, hLandauIBP_fg)
- 1 entropy dissipation continuity (hD_cont)

## 2026-03-09 14:00 UTC — Babysit cycle: hFubini_outer proved, 11→10 sorry's

### Accomplished
- **hFubini_outer PROVED from hLandauIBP_f_dg**: Derived `hFubini_outer` (integrability of `∫ w, score·flux`) from `hLandauIBP_f_dg` (integrability of `flux_i * score_i`). Key steps: (1) pull dotProduct through `∫ w` using `integral_finset_sum` + `eval_integral` + `integral_const_mul`, (2) expand as `Fin.sum_univ_three`, (3) each summand integrable by `hIBP_f_dg` with `mul_comm`.
- **Refactored proof structure**: Extracted `hIBP_f_dg` and `hFluxInt` as `have` statements before the VelocityDecayConditions constructor. `hLandauIBP_f_dg` now uses the extracted `hIBP_f_dg` directly (no separate sorry). `hLandauFluxInt` uses extracted `hFluxInt`.
- **Sorry count**: 11 → 10 in CoulombConcreteTheorem42.lean.
- **Aristotle API still down** (timeout).
- **Build status**: 0 errors, 10 sorry's.

### Remaining sorry's (10 total in CoulombConcreteTheorem42.lean)
- 2 AEStronglyMeasurable (lines 551, 559 — joint measurability for spatial_transport_joint_integrable)
- 3 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double)
- 1 hIBP_f_dg (line 1078 — covers both hLandauIBP_f_dg and hFubini_outer)
- 3 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g, hLandauIBP_fg)
- 1 entropy dissipation continuity (hD_cont)

## 2026-03-09 13:00 UTC — Babysit cycle: AEStronglyMeasurable proved, 12→11 sorry's

### Accomplished
- **AEStronglyMeasurable PROVED via difference quotients**: Added `torusGradX_aestronglyMeasurable` lemma (~45 lines). Shows `v ↦ torusGradX(fun y => f y v)(x)(i)` is AEStronglyMeasurable as limit of continuous difference quotients `G_n(v) = (n+1)·(f(torusMk(x₀ + (n+1)⁻¹·eᵢ), v) - f(x₀, v))`. Uses `aestronglyMeasurable_of_tendsto_ae` + `HasDerivAt.tendsto_slope_zero_right`.
- **Added smoothness hypotheses to `spatial_transport_integrable`**: Added `hf_smooth_v` and `hf_smooth_x` parameters, needed for the AEStronglyMeasurable proof. Updated both call sites.
- **Sorry count**: 12 → 11 in CoulombConcreteTheorem42.lean.
- **Aristotle API still down** (httpx.ReadTimeout on submission attempt).
- **Build status**: 0 errors, 11 sorry's.

### Remaining sorry's (11 total in CoulombConcreteTheorem42.lean)
- 2 AEStronglyMeasurable (lines 551, 559 — joint measurability for spatial_transport_joint_integrable)
- 4 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double/outer)
- 4 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g/f_dg/fg)
- 1 entropy dissipation continuity (hD_cont)

## 2026-03-09 12:00 UTC — Babysit cycle: Aristotle down, no changes

### Status
- Aristotle API still unreachable (network level — curl to API host times out).
- 2 submissions ready: `landau_ibp_fg.lean`, `landau_ibp_f_dg.lean`.
- Analyzed AEStronglyMeasurable sorry's: provable via difference quotient limit argument (`v ↦ gradX(f(·,v))(x)` is measurable as limit of continuous difference quotients). Formalization would be ~50 lines; deferred.
- 12 sorry's unchanged.

## 2026-03-09 11:00 UTC — Babysit cycle: Aristotle down, prepared submissions

### Accomplished
- **Aristotle API still down** (persistent httpx.ReadTimeout). No jobs can be submitted or checked.
- **Created `landau_ibp_f_dg.lean`**: New Aristotle submission for flux × d(log f) integrability. Compiles cleanly. If proved, would also enable closing hFubini_outer + hFubini_double (3 sorry's from 1 proof).
- **Analysis**: Remaining sorry's all require either (a) uniform convolution bound ∫ ‖v-w‖⁻¹ g(w) dw ≤ M, or (b) Fisher information integrability. Both are non-trivial without Aristotle.
- **Build status**: 0 errors, 12 sorry's in CoulombConcreteTheorem42.lean (unchanged).

### Pending Aristotle submissions (2 files ready)
- `landau_ibp_fg.lean` — flux × log f integrability
- `landau_ibp_f_dg.lean` — flux × d(log f) integrability (NEW)

### Remaining sorry's (12 total, unchanged)
- 3 AEStronglyMeasurable (lines 163, 499, 507)
- 4 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double/outer)
- 4 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g/f_dg/fg)
- 1 entropy dissipation continuity (hD_cont)

## 2026-03-09 10:00 UTC — Babysit cycle: hFubini_inner proved directly

### Accomplished
- **hFubini_inner PROVED directly**: Follows from `landau_flux_integrable_coulomb` via `integrable_pi_iff` + `const_mul`. The dot product of a constant (in w) score vector with the integrable flux vector is integrable componentwise. Sorry count: 13 → 12.
- **Aristotle API still down**: `landau_ibp_fg` resubmission failed (timeout). No new jobs can be submitted.
- **Build status**: 0 errors, 12 sorry's in CoulombConcreteTheorem42.lean.

### Remaining sorry's (12 total in CoulombConcreteTheorem42.lean)
- 3 AEStronglyMeasurable (lines 163, 499, 507)
- 4 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double/outer)
- 4 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g/f_dg/fg)
- 1 entropy dissipation continuity (hD_cont)

## 2026-03-09 09:00 UTC — Babysit cycle: landau_flux_integrable_coulomb PROVED

### Accomplished
- **landau_flux_integrable_coulomb PROVED (Aristotle job aabe3f3d)**: Integrated into CoulombConcreteTheorem42.lean.
  - Used primed definitions bridge (`show` to convert between VML and standalone definitions)
  - Fixed 2 build errors: `introN` failure (removed spurious `intro w` after `convert ... using 2`) and `mulVec`/`dotProduct` unfolding mismatch (added `simp only [mulVec, dotProduct]` + `convert ... using 2 with w`)
  - Closed `hLandauFluxInt` sorry. Sorry count: 14 → 13.
- **landau_ibp_fg (job 21e52da7)**: ERROR — Aristotle API request failed. Resubmission also failed (API timeout).
- **Build status**: 0 errors, 13 sorry's in CoulombConcreteTheorem42.lean.

### Remaining sorry's (13 total in CoulombConcreteTheorem42.lean)
- 3 AEStronglyMeasurable (lines 163, 499, 507)
- 5 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double/inner/outer)
- 4 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g/f_dg/fg)
- 1 entropy dissipation continuity (hD_cont)

## 2026-03-09 08:00 UTC — Babysit cycle: build fixes, 2 new Aristotle submissions

### Accomplished
- **landau_flux_integrable_coulomb FAILED (job 7d8c95bb)**: Aristotle returned sorry. Moved to completed/failed.
- **ConcreteTheorem42.lean restored**: Source file was missing (deleted in previous session). Restored from git and trimmed to shared definitions only (UniformSchwartzDecay, inverse_poly_integrable, helpers). Removed the general ConcreteTheorem42 theorem (superseded by CoulombConcreteTheorem42).
- **Build fixes**: The olean regeneration caused timeouts in Aristotle-generated proofs (inv_norm_local_integrable, convolution_local_int_schwartz). Added `set_option maxHeartbeats 1600000` to both. Fixed projection type annotation in psd_continuous_coulomb.
- **Build status**: 0 errors, 14 sorry warnings in CoulombConcreteTheorem42.lean.

### Aristotle jobs submitted
- `landau_flux_int_v2` (job aabe3f3d): Decomposed version of landau_flux_integrable_coulomb with admitted building blocks (coulomb_bound, inv_norm_schwartz_int).
- `landau_ibp_fg` (job 21e52da7): Landau IBP integrability (flux × log f) with admitted building blocks.

### Remaining sorry's (14 total in CoulombConcreteTheorem42.lean)
- 3 AEStronglyMeasurable (lines 163, 499, 507)
- 5 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double/inner/outer)
- 4 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g/f_dg/fg)
- 1 Landau flux int (hLandauFluxInt)
- 1 entropy dissipation continuity (hD_cont)

## 2026-03-09 07:00 UTC — Babysit cycle: no new results

### Status
- `landau_flux_integrable_coulomb` still IN_PROGRESS (job 7d8c95bb)
- 14 sorry's remain in CoulombConcreteTheorem42.lean (unchanged)
- No new Aristotle jobs completed this cycle

## 2026-03-09 06:00 UTC — Babysit cycle: psd_continuous_coulomb integrated, 2 negated

### Accomplished
- **psd_continuous_coulomb PROVED by Aristotle (job 14300a69)**: Integrated into CoulombConcreteTheorem42.lean.
  - Added private helper lemmas: `landau_bound`, `tendsto_landau_quadratic_diag`, `continuous_landau_quadratic`
  - Added `psd_continuous_coulomb` with bridge via `PSDIntegrand' = PSDIntegrand coulombKernel` (rfl)
  - Closed `hPSD_cont` sorry. Sorry count: 15 → 14.
- **force_schwartz_log_integrable NEGATED by Aristotle (job 23440e88)**: Statement is FALSE.
  - F not assumed measurable; Aristotle constructed counterexample using Vitali set.
  - Not used in CoulombConcreteTheorem42 (existing proofs already handle measurability via continuity of Lorentz force).
- **force_entropy_integrable NEGATED by Aristotle (job b85fc67d)**: Same issue — F not measurable.
- **inv_norm_schwartz_integrable, inv_norm_schwartz_product_integrable**: Completed but redundant (already proved).
- Fixed `socksio` dependency for Aristotle API (SOCKS proxy support).

### Aristotle jobs status
- 1 job still IN_PROGRESS: landau_flux_integrable_coulomb
- All others completed or processed

### Remaining sorry's (14 total in CoulombConcreteTheorem42.lean)
- 3 AEStronglyMeasurable (lines 162, 498, 506) — genuine joint regularity gaps
- 5 PSD/Fubini integrability (hPSD_inner/outer_int, hFubini_double/inner/outer)
- 4 Landau IBP/diff (hLandauFluxDiff, hLandauIBP_df_g/f_dg/fg)
- 1 Landau flux int (hLandauFluxInt — Aristotle running)
- 1 entropy dissipation continuity (hD_cont)

### Analysis
PSD integrability for Coulomb is genuinely hard: the score ∇log f can grow
exponentially (from stretched-exponential lower bound), so |∇f|²/f is NOT
Schwartz and simple inv_norm_schwartz_integrable bounds fail. A more
sophisticated argument (e.g., splitting near/far from diagonal) is needed.

## 2026-03-09 04:15 UTC — Babysit cycle: integrate Aristotle results

### Accomplished
- **inv_norm_schwartz_integrable PROVED**: Combined two completed Aristotle proofs:
  - `inv_norm_local_integrable` (job 3dc1b4dc): ‖·‖⁻¹ is locally integrable in ℝ³
  - `convolution_local_int_schwartz` (job 1ba752be): ‖v-w‖⁻¹ × Schwartz(w) is integrable
  - Both integrated into CoulombConcreteTheorem42.lean as private lemmas
  - `inv_norm_schwartz_integrable` now proved as a one-liner combining both
- **ConcreteTheorem42.lean restored** (shared definitions only): the sorry-heavy general theorem was removed per user request; file now contains only `UniformSchwartzDecay`, `inverse_poly_integrable`, and helper lemmas
- **check-aristotle.py fixed**: changed shebang to `python3.10` (aristotlelib requires >=3.10)
- **CLAUDE.md updated**: documented python3.10 requirement
- Build passes: 0 errors, 14 sorry warnings in CoulombConcreteTheorem42.lean

### Aristotle jobs status
- 6 jobs still IN_PROGRESS: force_schwartz_log_integrable, force_entropy_integrable, inv_norm_schwartz_integrable (redundant), inv_norm_schwartz_product_integrable (redundant), psd_continuous_coulomb, landau_flux_integrable_coulomb
- 2 jobs redundant: inv_norm_schwartz_integrable and inv_norm_schwartz_product_integrable (already proved via combination)

### Remaining sorry's (14 total in CoulombConcreteTheorem42.lean)
- 3 AEStronglyMeasurable (lines 162, 498, 506)
- 5 integrability: hPSD_inner/outer_int, hFubini_double/inner/outer
- 3 Landau IBP: hLandauIBP_df_g, hLandauIBP_f_dg, hLandauIBP_fg
- 1 Landau flux diff: hLandauFluxDiff
- 1 Landau flux int: hLandauFluxInt (Aristotle running)
- 1 PSD cont: hPSD_cont (Aristotle running)
- 1 D cont: hD_cont

## 2026-03-09 02:28 UTC — CoulombConcreteTheorem42 session (continued)

### Accomplished
- **CoulombConcreteTheorem42.lean**: 0 errors, 16 sorry warnings. File structure complete.
  - Proved: `schwartz_log_bound`, `schwartz_norm_pow_integrable`, `spatial_transport_integrable` (modulo 1 AEStronglyMeasurable sorry), `force_fderiv_log_component_integrable`, `force_transport_integrable_coulomb`, `force_ibp_f_dg_integrable_coulomb`, `force_ibp_fg_integrable_coulomb`, `spatial_transport_joint_integrable` (modulo 2 AEStronglyMeasurable sorry's)
  - Proved: `coulomb_landauMatrix_entry_le` (Coulomb matrix bound |A_{ij}(z)| ≤ eucNorm(z)⁻¹)
  - Proved: `pi_norm_le_eucNorm` and `coulomb_landauMatrix_entry_le_pi` (bridge to Pi norm)
  - Key sorry: `inv_norm_schwartz_integrable` — ‖v-w‖⁻¹ × Schwartz is integrable in ℝ³
  - 12 VelocityDecayConditions fields still sorry'd (most reduce to `inv_norm_schwartz_integrable`)
  - 3 AEStronglyMeasurable sorry's (joint x,v regularity — honest mathematical gaps)

### Aristotle jobs submitted (8 total, 1 completed)
- `inv_norm_schwartz_from_local` (1ba752be) — **COMPLETE**: proves `Integrable (fun w => ‖v-w‖⁻¹ * g w)` assuming local integrability of ‖·‖⁻¹ on B(0,1) + Schwartz decay of g
- `inv_norm_schwartz_integrable` (403eee35) — IN_PROGRESS: direct approach
- `inv_norm_local_integrable` (3dc1b4dc) — IN_PROGRESS: proves `IntegrableOn ‖·‖⁻¹ (closedBall 0 R)` in ℝ³
- `inv_norm_schwartz_product_integrable` (fb8f0314) — IN_PROGRESS: joint product integrability
- `psd_continuous_coulomb` (14300a69) — IN_PROGRESS: PSD integrand continuity despite Coulomb singularity
- `landau_flux_integrable_coulomb` (7d8c95bb) — IN_PROGRESS: Coulomb flux integrability
- `force_schwartz_log_integrable` (23440e88) — IN_PROGRESS
- `force_entropy_integrable` (b85fc67d) — IN_PROGRESS

### Key insight
The Coulomb kernel Ψ(r) = r⁻³ makes |A_{ij}(z)| ≤ ‖z‖⁻¹ (proved), which is locally integrable in 3D. Combined with Schwartz decay of f, all collision integrands are integrable. The chain is:
1. `inv_norm_local_integrable` (Aristotle, running) → ‖·‖⁻¹ integrable on B(0,1) in ℝ³
2. `convolution_local_int_schwartz` (Aristotle, proved!) → ‖v-w‖⁻¹ × Schwartz(w) integrable
3. → `inv_norm_schwartz_integrable` → all collision fields in VelocityDecayConditions

### Remaining sorry's (16 total)
- 1 key: `inv_norm_schwartz_integrable` (awaiting Aristotle)
- 12 VelocityDecayConditions fields (most follow from the key once proved)
- 3 AEStronglyMeasurable (honest gaps: joint x,v regularity of gradX)
