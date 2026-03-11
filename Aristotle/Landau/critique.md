# Adversarial Critique -- 2026-03-11 UTC (Cycle 112, Deep Review)

## Verdict: CONDITIONAL ACCEPT

---

## 0. Errors

`lake build Aristotle.Landau.main.CoulombConcreteTheorem42` -- **clean, 0 errors.**

`lean_verify` on `VML.CoulombConcreteTheorem42`: **0 axioms, 0 warnings.**

There are 3 unused `simp` argument warnings in `Defs.lean` (lines 98, 103, 108: `Fin.sum_univ_three` is unused in `simp` calls within `IsMaxwellian_params_unique`). These are lint warnings, not errors, and do not affect soundness. Minor cleanup opportunity.

---

## 1. Sorry's

**0 sorry's** across all 32 files (9,589 lines). The only occurrences of "sorry" in the codebase are in documentation comments describing resolved status. No `admit`, `native_decide`, `unsafe`, `implemented_by`, or `extern` found.

---

## 2. Hidden Axioms

`lean_verify` confirms **0 non-standard axioms** on the main theorem `VML.CoulombConcreteTheorem42`. The proof depends only on the standard Lean 4 axioms (propext, Quot.sound, Classical.choice) inherited from Mathlib.

No `axiom`, `opaque`, or `Lean.Elab.Command` declarations in user code.

---

## 3. Circularity

The import DAG is acyclic:

```
Defs -> VMLStructures, Section2, FlatTorus3Lemmas, TorusDefs -> TorusIntegration -> TorusInstance
     -> Section3Helpers -> Section3 -> Section4, Section5
     -> Section6, Section7, Section8
     -> VMLInputDerive -> Theorem42
SchwartzDecayDefs -> CoulombKernel -> Coulomb* files -> CoulombConcreteTheorem42
```

No circular imports detected. The abstract proof chain (Sections 2-8) is cleanly separated from the Coulomb concrete instantiation.

---

## 4. Hypothesis Audit

### 4a. The 23 FlatTorus3 axioms

The `FlatTorus3` typeclass has 23 property fields. All 23 are proved in `TorusInstance.lean` for `Torus3 = Fin 3 -> AddCircle 1`. Key observations:

- **IsSpatiallyDiff := ContDiff R top (periodicLift f)**: This is C-infinity, stronger than necessary. The abstract axioms only need C1 or C2 regularity in several places (e.g., `hIBP_spatial`, `hHarmonic_const`). The instance coerces with `hf.of_le le_top`, which is sound but slightly wasteful. Not a correctness issue.

- **hSpatialVelocityFubini**: The abstract axiom takes `(forall x, Integrable (F x))` as a first argument, but the concrete instance discards it (`_ hF_joint`). This is technically fine -- `integral_integral_swap` only needs joint integrability. However, the abstract axiom is **stronger than necessary** for its concrete witness: it requires per-section integrability that is never used. This is not a bug (the axiom is satisfied), but it is a design smell.

- **hLaplacianMaxNonpos**: The proof in `TorusInstance.lean` goes through a careful 1D second derivative test argument (`second_deriv_nonpos_at_local_max'`). I verified this is properly proved (no sorry).

All 23 fields: **VERIFIED SOUND**.

### 4b. The VelocityDecayConditions structure (19 fields)

All 19 fields of `VelocityDecayConditions` are proved in `CoulombConcreteTheorem42.lean` for the Coulomb kernel. Each field corresponds to an integrability or regularity condition required by the abstract proof chain. These are genuine mathematical requirements, not vacuously true.

---

## 5. Hypothesis Audit of the Main Theorem

`CoulombConcreteTheorem42` takes 13 hypotheses:

| # | Name | Type | Independent? | Necessary? |
|---|------|------|-------------|------------|
| 1 | hnu | 0 < nu | Yes | Yes (D=0 requires nu > 0 to factor) |
| 2 | hrho_ion | 0 < rho_ion | Yes | Yes (normalization to equilibrium Maxwellian) |
| 3 | hf_pos | forall x v, 0 < f x v | Yes | Yes (log f well-defined, score form) |
| 4 | hf_smooth_v | forall x, ContDiff R top (f x) | Yes | Yes (Frechet derivatives, IBP) |
| 5 | hf_smooth_x | forall v, ContDiff R top (periodicLift (fun x => f x v)) | Yes | Yes (spatial chain rule, transport) |
| 6 | hB_smooth | forall i, ContDiff R top (periodicLift (fun x => B x i)) | Yes | Yes (harmonic -> constant) |
| 7 | hSchwartz | UniformSchwartzDecay f | Yes | Yes (all integrability conditions) |
| 8 | hLogGrowth | poly log growth | **See note** | Yes (flux x log integrability) |
| 9 | hGradBound | poly score bound | Yes | Yes (PSD integrability for Coulomb singularity) |
| 10 | hVlasov | Vlasov equation | Yes | Yes (core PDE) |
| 11 | hAmpere | Ampere's law | Yes | Yes (curl B = J) |
| 12 | hGauss | Gauss's law | Yes | Yes (div E = rho - rho_ion) |
| 13 | hDivB | div B = 0 | Yes | Yes (solenoidal constraint) |

**Note on hLogGrowth (hypothesis 8):** The docstring at line 40-41 explains that hGradBound is independent of hSchwartz + hLogGrowth with a counterexample (f(v) = exp(-|v|^2)(2 + sin(exp(<v>)))). However, the **reverse independence** is less clear: is hLogGrowth independent of hSchwartz?

**Analysis:** hSchwartz gives an upper bound |f(x,v)| <= C/(1+||v||)^N for any N. This implies log f(x,v) <= log C. But it does NOT give a lower bound on f, so it does NOT bound -log f(x,v). The hLogGrowth hypothesis bounds |log f| from both sides, which requires a lower bound on f (stretched-exponential or similar). So **yes, hLogGrowth is genuinely independent of hSchwartz**.

However, **hLogGrowth is implied by hSchwartz + hf_pos + a stretched-exponential lower bound on f**. The theorem does not explicitly assume a lower bound on f, yet hLogGrowth encodes one implicitly. This is an honest design choice: the lower bound is bundled into hLogGrowth rather than stated separately. The documentation at `schwartz_log_bound` in `CoulombKernel.lean` makes this explicit.

**ISSUE (Medium): The relationship between hypotheses 7, 8, 9 deserves clearer documentation in the main theorem docstring.** Currently, the docstring explains why (9) is independent of (7)+(8), but does not explain why (8) is independent of (7). A reader might wonder: "If f is Schwartz, doesn't log f have polynomial growth?" The answer is no (Schwartz only gives an upper bound), but this should be stated.

---

## 6. Mathematical Correctness

### 6a. The proof chain is mathematically sound

The proof follows the standard structure for VML steady-state characterization:
1. H-theorem: D(f) <= 0 (PSD of Landau matrix)
2. Transport entropy: integral of D = 0 on the torus (Vlasov + IBP)
3. D(f) = 0 at each x (nonneg + integral = 0 on compact domain)
4. D = 0 => f is local Maxwellian (PSD equality case => parallel scores => affine gradient => log-quadratic)
5. Polynomial matching of Vlasov coefficients (temperature constant, Killing equation for drift, force balance)
6. Drift = 0 (Ampere + Stokes on T^3)
7. Density constant (Poisson-Boltzmann + maximum principle on T^3)
8. E = 0 (force balance + grad a = 0)
9. B constant (curl = 0, div = 0, harmonic on T^3)

This is the correct argument from the physics/PDE literature (Desvillettes, Villani, Guo, Strain).

### 6b. Coulomb kernel definition

`coulombKernel r = if r <= 0 then 1 else r ^ (-3 : R)`.

The extension to r <= 0 is correctly documented as irrelevant: the Landau matrix `A(z) = Psi(|z|) * (|z|^2 I - zz^T)` vanishes at z = 0 regardless of Psi(0), because the inner matrix `|z|^2 I - zz^T` is zero when z = 0. Setting Psi(r) = 1 for r <= 0 ensures the global positivity `forall r, 0 < Psi r` that the abstract theorem requires. **Sound.**

### 6c. The Fubini symmetrization

`fubini_symmetrization_logf` (Section3.lean, line 138) proves the key identity for the entropy dissipation. The proof swaps integration order via Fubini, uses `landauMatrix_sub_comm` (A(w-v) = A(v-w) by evenness), and flux antisymmetry. **Sound.**

### 6d. Nonvacuousness

`CoulombConcreteTheorem42_nonvacuous` (CoulombNonvacuous.lean, line 226) constructs a witness: f = equilibriumMaxwellian, E = 0, B = 0. All 13 hypotheses are verified.

**Minor note on Ampere (hypothesis 11):** The proof uses `simp` to close the goal that `curl 0 = fun i => integral v_i * eM`. The LHS is clearly 0 (curl of constant). The RHS should be `integral v_i * eM(v) dv = 0` by odd symmetry of v_i * eM(v). The proof closes by `fin_cases i <;> simp [...]`, which means `simp` is handling both sides. Since the `curl 0 = 0` part is trivial, `simp` is likely closing `integral v_i * eM = 0` directly. This is correct because on the LHS side, `curl 0 = 0`, and on the RHS, it needs `integral v_i * eM = 0`. But **`simp` might be closing this by reducing `fun i => integral v_i * eM` to something trivially equal to 0 through normalization, not by proving the integral is zero**. Let me check: the `fin_cases i` produces 3 goals, each of the form `0 - 0 = integral v_i * eM`. Actually looking more carefully, the `simp` lemmas applied include `Matrix.cons_val_*` and `Matrix.head_*`, which only simplify the curl side. The integral side is left as-is. So the goal after `simp` must be `0 = integral v_i * eM`, which would need the odd integral to be zero. Since `simp` closes it, Lean must be computing this. **Verified: the proof is sound** (the build succeeds).

---

## 7. Code Quality

### 7a. maxHeartbeats overrides (2 remaining)

| File | Line | Value |
|------|------|-------|
| TorusIntegration.lean | 85 | 400000 |
| NewtonianPotential.lean | 85 | 800000 |

Both are within the 800000 ceiling. The TorusIntegration one covers `integral_derivative_periodic_zero`, a complex box-integral Fubini proof. The NewtonianPotential one covers an integrability argument. Neither is unreasonable.

### 7b. Files over 500 lines (5 files)

| File | Lines |
|------|-------|
| Defs.lean | 507 |
| TorusIntegration.lean | 436 |
| GaussianHelpers.lean | 474 |
| VMLInputDerive.lean | 449 |
| Section3Helpers.lean | 613 |

Section3Helpers.lean at 613 lines exceeds the 600-line soft limit. It contains the core analytical lemmas (parallel implies affine, affine gradient antiderivative, entropy score form, D=0 implies Maxwellian). These are tightly coupled and splitting would be artificial.

### 7c. Proofs over 150 lines (3 proofs)

| File | Proof | Lines |
|------|-------|-------|
| CoulombFluxDiff.lean | `coulomb_flux_deriv_schwartz_decay` | ~183 |
| Theorem42.lean | `Theorem42` | ~178 |
| Section3Helpers.lean | `parallel_curl_free_affine` | ~157 |

All under 200. These are structurally complex proofs where further decomposition has diminishing returns.

### 7d. Unused simp arguments (3 occurrences in Defs.lean)

Lines 98, 103, 108: `Fin.sum_univ_three` is flagged as unused by the linter. Trivial cleanup.

### 7e. Line length violation (1 occurrence in Defs.lean)

Line 98 exceeds the 100-character limit. Trivial cleanup.

### 7f. Broad `simp +decide` usage (103 occurrences)

Most are in `Fin 3` case analysis where `decide` is the appropriate discharger. Low priority.

---

## 8. Documentation Lies

### 8a. MEMORY.md line counts are approximate

MEMORY.md states "CoulombFlux.lean (~597 lines)" but actual is 186 lines. "CoulombPSD.lean (~750 lines)" but actual is 298 lines. "CoulombFluxDiff.lean (~616 lines)" but actual is 250 lines. These are stale from before file splits. The MEMORY.md disclaimer "Note: File line counts in this file are approximate and may drift" covers this, but the drift is severe (3-4x off).

**ISSUE (Low): MEMORY.md file line counts are severely outdated and should be refreshed.**

### 8b. Coulomb file structure documentation

MEMORY.md lists 7 Coulomb files but actual count is 10:
- CoulombKernel.lean, CoulombSpatialTransport.lean (listed as CoulombSpatialTransport.lean),
  NewtonianPotential.lean, CoulombFlux.lean, CoulombPSD.lean, CoulombFluxDiff.lean,
  CoulombConcreteTheorem42.lean (all listed)
- CoulombFluxBound.lean, CoulombFluxConv.lean, CoulombForceTransport.lean,
  CoulombPSDHelpers.lean, CoulombNonvacuous.lean (NOT listed)

**ISSUE (Low): MEMORY.md Coulomb file inventory is incomplete.**

---

## 9. Generalization Opportunities

### 9a. Generalize beyond T^3 (HARD, DEFERRED)

The abstract proof chain works for any `FlatTorus3 X`. The bottleneck is the Coulomb-specific integrability proofs, which are stated for `Torus3`. Generalizing to an abstract `FlatTorus3` would require parameterizing the Coulomb files.

### 9b. Dimension generalization (HARD)

Everything is hard-coded to `Fin 3`. The abstract structures (`FlatTorus3`, `VelocityDecayConditions`) and the Coulomb kernel are all 3-dimensional. Generalizing to `Fin n` would require significant refactoring.

### 9c. Multi-species (HARD)

The theorem covers single-species VML. Multi-species requires coupling multiple distribution functions through the collision operator.

### 9d. Mathlib upstreamability

Candidates:
1. `iteratedFDeriv_clm_zero` (IteratedDerivHelpers.lean) -- strongest candidate
2. `inverse_poly_integrable` (SchwartzDecayDefs.lean) -- general utility
3. `schwartz_pointwise_decay`, `schwartz_fderiv_component_decay` (SchwartzDecayDefs.lean)
4. `poisson_boltzmann_max_principle` (GaussianHelpers.lean) -- very general PDE lemma
5. `second_deriv_nonpos_at_local_max'` (TorusInstance.lean) -- basic calculus fact

---

## 10. Mathlib Upstreamability

See 9d above. The `poisson_boltzmann_max_principle` and `second_deriv_nonpos_at_local_max'` are the most generally useful.

---

## Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 5 | Hypothesis 8 independence not documented | Medium | **NEW** |
| 7d | 3 unused simp arguments in Defs.lean | Low | NEW |
| 7e | 1 line length violation in Defs.lean | Low | NEW |
| 7b | Section3Helpers.lean at 613 lines | Low | Open |
| 7c | 3 proofs over 150 lines | Low | Open (diminishing returns) |
| 7f | 103 `simp +decide` calls | Low | Open |
| 8a | MEMORY.md line counts severely outdated | Low | NEW |
| 8b | MEMORY.md Coulomb file inventory incomplete | Low | NEW |
| 9a | Generalize beyond T^3 | Low | Deferred (hard) |
| 9d | Mathlib PR for helper lemmas | Low | Open (5 candidates) |

---

## Conditions for ACCEPT

**CONDITIONAL ACCEPT.** The formalization is mathematically sound, fully verified by the Lean 4 kernel with 0 sorry's and 0 non-standard axioms. The proof chain is correct and follows the established literature.

The single medium-severity issue is:
- **Document why hypothesis 8 (hLogGrowth) is independent of hypothesis 7 (hSchwartz)** in the main theorem docstring. Currently, the docstring carefully explains why hypothesis 9 is independent of 7+8, but omits the analogous explanation for hypothesis 8. A reader encountering "Schwartz decay" and "polynomial log growth" as separate hypotheses will naturally ask whether the second follows from the first. It does not (Schwartz gives only an upper bound on f, not a lower bound), but this should be stated explicitly for the same reason hypothesis 9's independence is stated.

Promoting to full ACCEPT once this documentation is added. All other issues are low severity.
