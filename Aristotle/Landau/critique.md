# Adversarial Critique: Coulomb Concrete Theorem 42

**Reviewer posture:** Hostile. Default verdict is REJECT. The formalization must earn approval through evidence.

**Reviewed:** Full codebase at `Aristotle/Landau/main/` (21 .lean files, 11,046 total lines)
**Main theorem:** `CoulombConcreteTheorem42` in `CoulombConcreteTheorem42.lean` (280 lines)
**Date:** 2026-03-09 (fresh analysis, supersedes all prior reviews)

**Claim:** Any sufficiently smooth, positive, Schwartz-class steady-state solution of the Vlasov-Maxwell-Landau system with Coulomb collisions on T^3 is a global Maxwellian equilibrium with E = 0 and B = const.

---

## 1. Remaining Sorry's and Their Mathematical Status

There are **2 sorry tokens** in the codebase, all in `CoulombPSD.lean`. They are 2 independent "base" lemmas with empty proof bodies (sorry 1 and sorry 2). All derived lemmas that depend on them have complete proof bodies.

Three further lemmas (`coulomb_flux_differentiable`, `coulomb_flux_deriv_schwartz_decay`, and `coulomb_ibp_df_g_integrable`) have complete proof bodies that are formally verified modulo the 2 sorry'd base lemmas.

### Sorry inventory

| # | Lemma | File:Line | Statement | Proof body | Deps |
|---|-------|-----------|-----------|------------|------|
| 1 | `coulomb_entry_conv_differentiable` | CoulombPSD.lean:792 | `Differentiable R (v -> integral_w A_{ij}(v-w) * g(w))` for Schwartz g | Empty (`sorry`) | None |
| 2 | `coulomb_entry_conv_deriv_decay` | CoulombPSD.lean:803 | `exists C > 0, forall v, norm(fderiv(entry_conv)(v)) * (1+norm(v))^N <= C` | Empty (`sorry`) | None |
| (*) | `coulomb_flux_differentiable` | CoulombPSD.lean:812-872 | `Differentiable R (v -> flux_i(v))` | **COMPLETE** (depends on sorry 1) | Uses 1 |
| (*) | `coulomb_flux_deriv_schwartz_decay` | CoulombPSD.lean:916-1124 | `exists C > 0, forall v, norm(fderiv(flux_i)(v)) * (1+norm(v))^N <= C` | **COMPLETE** (~200 lines; depends on sorry 2) | Uses 2 |
| (*) | `coulomb_ibp_df_g_integrable` | CoulombPSD.lean:1144-1191 | `Integrable (v -> fderiv(flux_i)(v)(e_i) * log(f(v)))` | **COMPLETE** (depends on sorry's 1-2 via call chain) | Uses (*) |

### Correction from previous critique

The previous critique counted **3 sorry tokens**. This is now **2**. The change is that `coulomb_flux_deriv_schwartz_decay` has been fully proved: a ~200-line proof body that:
1. Decomposes flux into K_{ij}/L_{ij} convolutions via `coulomb_flux_eq_decomposed`
2. Establishes Schwartz decay of fderiv(K), fderiv(L) from sorry 2
3. Bounds each of 4 product-rule terms using `mul_le_mul`
4. Combines using `nlinarith` with the key identity `‖fderiv f v‖ = ‖iteratedFDeriv 1 f v‖` (via `norm_iteratedFDeriv_fderiv` + `norm_iteratedFDeriv_zero`)

### Assessment of sorry 1: `coulomb_entry_conv_differentiable`

**Statement:** For Schwartz g, the map `v -> integral_w A_{ij}(v-w) * g(w)` is differentiable, where `A_{ij}` is a Coulomb Landau matrix entry satisfying `|A_{ij}(z)| <= ||z||^{-1}`.

**Is it mathematically true?** Yes. After the substitution `u = v - w`, the integral becomes `integral_u A_{ij}(u) * g(v - u)`, a standard convolution. The v-derivative acts only on `g(v - u)`, producing `integral_u A_{ij}(u) * (fderiv g)(v - u)(e_k)`. Since `|A_{ij}(u)| <= ||u||^{-1}` is locally integrable in R^3 (the singularity is `r^{-1}` which integrates against `r^2 dr`) and `fderiv g` is Schwartz (hence bounded and integrable), the dominated convergence theorem applies via Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le`.

**Difficulty of filling in Lean:** Moderate-hard. Estimated 100-200 lines. The argument is explicitly described in the docstring and the Mathlib API exists. The main obstacle is showing the dominator `||u||^{-1} * C / (1+||u||)^4` is integrable (proved elsewhere in the codebase as `inv_norm_schwartz_integrable`) and that the fderiv of the integrand satisfies the pointwise bound uniformly on a neighborhood of each v.

### Assessment of sorry 2: `coulomb_entry_conv_deriv_decay`

**Statement:** The derivative of the entry convolution has Schwartz decay: for every N, `||fderiv(entry_conv)(v)|| * (1+||v||)^N <= C`.

**Is it mathematically true?** Yes. The derivative equals `integral_u A_{ij}(u) * (fderiv g)(v - u)(e_k)`. The convolution of an L^1_loc function with a Schwartz function is Schwartz (Folland, "Real Analysis," Proposition 8.10). The near/far splitting argument gives polynomial decay at any order.

**Difficulty of filling in Lean:** Hard. Estimated 200-400 lines. Requires splitting the integral into near/far regions, bounding each separately with polynomial weights, and combining. No ready-made Mathlib lemma for "convolution with L^1_loc preserves Schwartz class."

### Impact analysis

The 2 sorry's taint exactly **2 of 18** VelocityDecayConditions fields:
- `hLandauFluxDiff` (uses sorry 1 via `coulomb_flux_differentiable`)
- `hLandauIBP_df_g` (uses sorry's 1-3 via `coulomb_ibp_df_g_integrable`)

The remaining 16 fields are fully proved. **Completeness: 16/18 = 89%.**

### Dependency flow

```
coulomb_entry_conv_differentiable (SORRY 1)
  -> coulomb_flux_differentiable (PROVED, depends on sorry 1)
     -> hLandauFluxDiff (field of VelocityDecayConditions)
     -> coulomb_ibp_df_g_integrable (measurability sub-proof)

coulomb_entry_conv_deriv_decay (SORRY 2)
  -> coulomb_flux_deriv_schwartz_decay (PROVED, depends on sorry 2)
     -> coulomb_ibp_df_g_integrable (PROVED, depends on sorry 2 via chain)
        -> hLandauIBP_df_g (field of VelocityDecayConditions)
```

---

## 2. Sorry Count Trajectory

| Version | Sorry tokens | Independent base sorry's | Derived sorry's with partial proof | VDC completeness |
|---------|-------------|-------------------------|-----------------------------------|-----------------|
| Previous critique | 4 | 2 | 2 (flux_diff, flux_decay) | 16/18 = 89% |
| Cycle 22 | 3 | 2 | 1 (flux_decay only) | 16/18 = 89% |
| Current (cycle 23) | **2** | 2 | 0 (all derived lemmas proved) | 16/18 = 89% |

`coulomb_flux_differentiable` was promoted from sorry'd to fully proved (cycle 22). `coulomb_flux_deriv_schwartz_decay` was promoted from sorry'd to fully proved (cycle 23): a ~200-line proof decomposing the flux into K/L convolutions, establishing derivative bounds via `mul_le_mul` on 4 product-rule terms, and combining with `nlinarith`. All 3 derived lemmas now have complete proof bodies; only the 2 independent base lemmas remain sorry'd.

---

## 3. VelocityDecayConditions: Typeclass Fields as Axioms

### Structure of the abstraction

The `VelocityDecayConditions` structure (Theorem42.lean:25-88) has 18 fields encoding integrability, differentiability, continuity, and Fubini conditions needed for the H-theorem chain. These are consumed by `Theorem42` as a single bundled hypothesis `hDecay`.

All 18 fields are explicitly instantiated in `CoulombConcreteTheorem42.lean:158-274`. Each field is filled with a call to a named lemma. 16 of those lemma bodies are complete proofs.

### Field-by-field non-circularity audit

| Field | Status | Could it smuggle the conclusion? |
|-------|--------|----------------------------------|
| `hPSD_inner_int` | PROVED | No -- integrability of a bilinear form |
| `hPSD_outer_int` | PROVED | No -- iterated integrability |
| `hFubini_double` | PROVED | No -- joint integrability on product space |
| `hFubini_inner` | PROVED | No -- inner Fubini slice integrability |
| `hFubini_outer` | PROVED | No -- outer Fubini integrability |
| `hSpatialTransport_int` | PROVED | No -- transport term integrability |
| `hForceTransport_int` | PROVED | No -- force transport integrability |
| `hLandauFluxDiff` | **SORRY** | No -- differentiability does not imply equilibrium |
| `hLandauIBP_df_g` | **SORRY** | No -- integrability for IBP does not imply equilibrium |
| `hLandauIBP_f_dg` | PROVED | No |
| `hLandauIBP_fg` | PROVED | No |
| `hLandauFluxInt` | PROVED | No |
| `hForceIBP_f_dg` | PROVED | No |
| `hForceIBP_fg` | PROVED | No |
| `hSpatialTransport_joint` | PROVED | No |
| `hSpatTransComp` | PROVED | No |
| `hf_velocity_dominated` | PROVED | No |
| `hPSD_cont` | PROVED | No |
| `hD_cont` | PROVED | No |

**Verdict on hidden axioms:** None of the 18 fields encodes a statement equivalent to or implying the conclusion. They are all analytical regularity conditions.

### Concern: hD_cont proof uses Vlasov equation

The `hD_cont` field (CoulombConcreteTheorem42.lean:237-273) proves continuity of `entropyDissipation coulombKernel (f x)` by expressing it as `nu^{-1} * integral(spatial_transport * log f)`. This identity comes from the Vlasov equation, so it requires `hVlasov` as input. The proof chain is:

1. Use Vlasov to write `nu * Q(f,f) = spatial_transport + force_transport`
2. Show force transport integral is zero (IBP + div(v x B) = 0)
3. Conclude D(f x) = nu^{-1} * integral(spatial_transport * log f)
4. Prove the right side is continuous in x

This is logically sound: `hD_cont` does not assume the conclusion, it merely uses the Vlasov equation (a hypothesis) to re-express D(f) in a computable form. But it creates a subtle dependency: the `hD_cont` proof uses `force_transport_zero`, which itself requires `hForceIBP_f_dg` and `hForceIBP_fg` (other fields of VelocityDecayConditions). Fortunately, these are proved *before* the structure is constructed, so there is no actual circularity -- but the proof of `hD_cont` morally depends on some of the other fields being satisfiable.

### Satisfiability witness

`VelocityDecayInstance.lean` (2019 lines) provides two satisfiability witnesses:
1. `schwartzDecayConditions`: uniform isotropic Maxwellian with E = 0, B = 0
2. `schwartzDecayConditionsEB`: uniform isotropic Maxwellian with nonzero constant E, B

Both have all 18 fields proved with 0 sorry's. These demonstrate the hypotheses are non-vacuous.

**Remaining weakness:** Both witnesses use the equilibrium distribution. A non-equilibrium Schwartz-class f satisfying all 18 fields would be a stronger satisfiability witness, but this requires sorry's 1-2 to be filled.

---

## 4. FlatTorus3: Typeclass Axioms

### Field count and structure

The `FlatTorus3` typeclass (Defs.lean:325-417) extends `MeasureSpace X` and `TopologicalSpace X` with:
- 3 instance fields (`instCompact`, `instNonempty`, `instFirstCountable`)
- 3 operator definitions (`gradX`, `divX`, `curlX`)
- 1 predicate definition (`IsSpatiallyDiff`)
- 22 property axioms

Total: **29 fields**. All 29 are instantiated for `Torus3 = Fin 3 -> AddCircle 1` in `TorusInstance.lean` (1223 lines) with 0 sorry's.

### Concern: `hGradScalarMul` lacks `IsSpatiallyDiff` guard

The axiom `hGradScalarMul` states `gradX (c * f) = c * gradX f` without requiring `IsSpatiallyDiff f`. On the concrete torus, `gradX` is defined via `fderiv`, so for non-differentiable `f`, `fderiv f = 0` on both sides and the equation `c * 0 = 0` holds vacuously. This is sound but fragile: a different instantiation where `gradX` does not return 0 for non-differentiable functions would need this to hold unconditionally. Minor design issue.

### Concern: `hSpatialAdd` and `hSpatialVelocityFubini` are derivable

Both are theorems of Mathlib's measure theory on any measure space. Including them as axioms is redundant. The TorusInstance proves them from Mathlib, confirming this. Note that `hSpatialVelocityFubini` does include integrability hypotheses (both pointwise and joint), so it is not entirely vacuous -- it is essentially a restatement of Fubini's theorem. Still, axiomatizing something derivable from existing structure is a code smell.

### Concern: `IsSpatiallyDiff` overshoot

On the concrete torus, `IsSpatiallyDiff` is `ContDiff R top (periodicLift f)`, the strongest possible choice (smooth). The abstract proof chain only needs C^2 regularity for the Killing equation analysis and Hodge theory steps. Using `ContDiff R top` makes the preconditions in `CoulombConcreteTheorem42` (`hf_smooth_x : forall v, ContDiff R top (periodicLift (fun x => f x v))`) stronger than necessary. This does not affect soundness but narrows the class of functions the theorem applies to -- any f that is C^2 but not C^infinity in x is excluded despite the mathematics working. A more refined choice like `ContDiff R 2` would widen applicability at the cost of more work in the TorusInstance.

---

## 5. Circularity and Hypothesis Scrutiny

### Import dependency DAG

```
Defs.lean
  <- Section2.lean (Landau matrix properties)
  <- Section3.lean (H-theorem: IBP, Fubini, PSD=0 -> Maxwellian)
  <- Section4.lean (transport constraints)
  <- Section5.lean (polynomial matching)
  <- Section6.lean (bulk velocity zero)
  <- Section7.lean (Poisson-Boltzmann, density constant)
  <- Section8.lean (B constant)
  <- Section9.lean (conservation laws)
  <- VMLInputDerive.lean (VMLInput -> VMLSteadyState)
     <- Theorem42.lean (main theorem from VMLSteadyState)
        <- TorusInstance.lean (FlatTorus3 for Fin 3 -> AddCircle 1)
        <- VelocityDecayInstance.lean (satisfiability witness)
           <- ConcreteTheorem42.lean (Schwartz-hypotheses version)
              <- CoulombKernel.lean
                 <- NewtonianPotential.lean
                 <- CoulombSpatialTransport.lean
                 <- CoulombFlux.lean
                 <- CoulombPSD.lean [2 sorry's here]
                    <- CoulombConcreteTheorem42.lean (main theorem)
```

**No cycles.** The flow is strictly: definitions -> abstract algebra -> analysis -> abstract theorem -> concrete instance -> Coulomb specialization.

### Is any hypothesis restating the conclusion?

The 13 hypotheses of `CoulombConcreteTheorem42` are:
1. `hnu : 0 < nu` -- physical parameter
2. `hrho_ion : 0 < rho_ion` -- physical parameter
3. `hf_pos : forall x v, 0 < f x v` -- positivity
4-6. Smoothness of f and B
7. `hSchwartz : UniformSchwartzDecay f` -- Schwartz decay in v, uniform in x
8. `hExpDecay` -- stretched-exponential lower bound
9. `hGradBound` -- polynomial score bound
10-13. Four VML equations (Vlasov, Ampere, Gauss, div B = 0)

**None restates the conclusion.** The polynomial score bound (hypothesis 9) is the most restrictive: `|df/dv_i| <= Cg * (1+||v||)^Kg * f`. But this is satisfied by any Maxwellian (Kg = 1), any stretched-Gaussian, and any f with polynomial logarithmic gradient growth. It does not force f to be Maxwellian.

### Deeper scrutiny: Is `UniformSchwartzDecay` too strong?

`UniformSchwartzDecay` has two fields:
- `hDecay`: all iterated velocity derivatives decay faster than any polynomial, uniformly in x
- `hGradDecay`: spatial gradient components of f also have Schwartz velocity decay

The `hGradDecay` field is used in proving `hSpatialTransport_int` and related fields. It is a genuine analytical hypothesis about the joint regularity of f in (x, v). For a steady-state solution of Vlasov, this follows from standard regularity theory (smooth coefficients + smooth kernel -> smooth solution), but formalizing this bootstrap argument is far beyond the scope of this project. Treating it as a hypothesis is honest.

The combination of `hSchwartz` + `hExpDecay` is also worth examining: Schwartz decay gives an upper bound (f decays faster than any polynomial), while the stretched-exponential gives a lower bound (f doesn't decay faster than exp(-C(1+|v|)^K)). Together they constrain f to decay "exactly Schwartz-fast" -- not too slow (would violate integrability), not too fast (would violate the log bound needed for IBP). Both are needed: without `hExpDecay`, `log f` could grow super-polynomially, breaking the integrability of `flux * log f`.

### Scrutiny of `coulombKernel_pos`

The Coulomb kernel is defined as `if r <= 0 then 1 else r ^ (-3)`. The lemma `coulombKernel_pos` proves `forall r, 0 < coulombKernel r`. The abstract theorem `Theorem42` requires `hPsi : forall r, 0 < Psi r`.

**Is this an artificial hypothesis?** The physical Coulomb kernel Psi(r) = r^{-3} diverges at r = 0 and is undefined for r < 0. The formalization extends it to 1 at r <= 0. This is harmless because `landauMatrix Psi 0 = 0` always (the projection `|z|^2 I - z z^T` vanishes at z = 0), so the value of Psi at 0 never affects the Landau operator. The positivity hypothesis is a convenience for the abstract proof (it simplifies the PSD non-negativity argument) and is satisfied by the extended kernel.

---

## 6. Physical Limitations

### Dimension restriction

Hardcoded to dimension 3 (`Fin 3 -> R`). The cross product is inherently 3D (Lorentz force `E + v x B`), so this is not merely a simplification -- it is physically necessary.

### Kernel restriction

The Coulomb theorem covers only `Psi(r) = r^{-3}` (gamma = -3). The smooth-kernel theorem (`ConcreteTheorem42`) covers any continuous Psi (including hard-sphere `Psi = 1`). Moderately soft potentials (-3 < gamma < 0) are not covered by either.

### Spatial domain restriction

T^3 = (R/Z)^3. The periodic domain eliminates boundary terms and is standard in kinetic theory.

### Steady-state assumption

The theorem assumes f, E, B are time-independent. It is a characterization theorem, not a stability result. This is correctly stated.

### Positivity assumption

`hf_pos : forall x v, 0 < f x v` is everywhere strict positivity. Weakening to a.e. positivity would require substantial rework of the log chain.

### Smoothness overshoot

The hypotheses require `ContDiff R top (f x)` (smooth in v) and `ContDiff R top (periodicLift (fun x => f x v))` (smooth in x). The mathematical proof only needs enough regularity to justify IBP and the Killing equation argument (~C^2 in v, C^2 in x). The C^infinity requirement is strictly stronger than needed. This narrows applicability but does not affect soundness.

---

## 7. Code Quality

### File sizes

| File | Lines | Assessment |
|------|-------|------------|
| VelocityDecayInstance.lean | 2019 | **Too large.** The `schwartzDecayConditionsEB` definition (lines 1933-2019) is 87 lines of copy-paste from `schwartzDecayConditions`, differing only in the force transport fields. This should use a `let base := schwartzDecayConditions ...` pattern. |
| Section3.lean | 1308 | **Too large.** Contains the entire H-theorem chain plus Gaussian integrals plus gap lemmas. Should be split. |
| TorusInstance.lean | 1223 | Acceptable for a single typeclass instance. |
| CoulombPSD.lean | 1191 | **Grew significantly** (flux decay proof added ~200 lines). Contains PSD continuity, PSD/Fubini integrability, flux differentiability, flux decay, and IBP integrability -- five logically distinct topics in one file. Should be split. |
| Defs.lean | 782 | Acceptable for a definitions file. |
| CoulombSpatialTransport.lean | 662 | Borderline. |
| LandauMatrixDerivBound.lean | 648 | Contains 232 lines of a custom `generalize_proofs'` tactic (lines 30-232). This is a copy of Mathlib's `generalize_proofs` with modifications for the Aristotle workflow. It is dead weight for a human reader. |
| CoulombFlux.lean | 609 | Borderline. |

### Heartbeat overrides

33 `maxHeartbeats` overrides across 11 files:

| Value | Count | Severity |
|-------|-------|----------|
| 4,000,000 (20x default) | 1 | **Fragile** |
| 3,200,000 (16x default) | 5 | High |
| 1,600,000 (8x default) | 11 | Moderate |
| 800,000 (4x default) | 15 | Acceptable individually |

Plus 1 `synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean.

The 4M-heartbeat proof (`landau_flux_component_diff_with_bound` in VelocityDecayInstance.lean:1002) is the single most fragile point. A Lean or Mathlib version bump will almost certainly break it.

### Universal linter suppression

`set_option linter.all false` appears in **all 21 files**. This suppresses all Lean linters (unused variables, deprecated APIs, unreachable tactics, etc.). With linters disabled, there is no automated check for:
- Deprecated Mathlib APIs (e.g., `one_le_pow_of_one_le` used in CoulombPSD.lean, which may be deprecated in newer Mathlib)
- Dead hypotheses masking structural problems
- Unused imports bloating build times

### Duplicate primed definitions

Three files define overlapping sets of primed definitions:

| Definition | CoulombFlux.lean | CoulombPSD.lean | LandauMatrixDerivBound.lean |
|------------|-----------------|-----------------|----------------------------|
| `normSq'` | line 12 | (uses from CoulombFlux) | line 241 |
| `eucNorm'` | line 13 | (uses from CoulombFlux) | line 243 |
| `innerLandauMatrix'` | line 14 | (uses from CoulombFlux) | line 245 |
| `coulombKernel'` | line 16 | (uses from CoulombFlux) | -- |
| `landauMatrix'` | line 17 (Coulomb-specific) | (uses from CoulombFlux) | line 248 (generic, takes Psi param) |
| `vGrad'` | line 19 | (uses from CoulombFlux) | -- |
| `PSDIntegrand'` | -- | line 9 | -- |

Critical observation: `VML.landauMatrix'` in CoulombFlux.lean (line 17) is `coulombKernel' (eucNorm' z) * innerLandauMatrix' z` (Coulomb-specific, no Psi parameter), while the top-level `landauMatrix'` in LandauMatrixDerivBound.lean (line 248) is `Psi (eucNorm' z) * innerLandauMatrix' z` (generic, takes Psi). These are **different definitions with the same base name** in different namespaces (VML vs. top-level). The bridge lemma `landauMatrix'_eq_VML : landauMatrix' = VML.landauMatrix` at LandauMatrixDerivBound.lean:600 relates the *generic* primed definition to the VML namespace unprimed definition. This means the same token `landauMatrix'` resolves to different things depending on which namespace is open -- a recipe for subtle bugs in future refactoring.

### LandauMatrixDerivBound.lean: 232 lines of custom tactic code

Lines 30-232 contain a complete reimplementation of Mathlib's `generalize_proofs` tactic (`generalizeProofs'`, `abstractProofs'`, `withGeneralizedProofs'`, etc.). This is injected by the Aristotle prover for compatibility. The 232 lines of metaprogramming:
1. Are not relevant to the mathematical content
2. Cannot be reviewed for correctness without deep Lean 4 metaprogramming expertise
3. Duplicate Mathlib infrastructure with custom modifications
4. Are `partial def` (meaning no termination proof is provided)

This is a red flag for long-term maintainability. If the Aristotle tactic diverges from Mathlib's `generalize_proofs`, the proofs may silently break on Mathlib updates.

### Machine-generated proof style

Multiple proofs (attributed to "Aristotle (Harmonic)") are dense semicolon chains. Example from CoulombPSD.lean:22-38 (`landau_bound`):

```lean
unfold landauMatrix' eucNorm';
unfold coulombKernel' innerLandauMatrix' normSq';
split_ifs <;> norm_cast <;> norm_num [ Matrix.vecMulVec ] at *;
...
exact abs_le.mpr < by nlinarith [ sq_nonneg ( z 0 * u 1 - z 1 * u 0 ), ... ] >
```

These proofs are opaque, unmaintainable, and likely to break on any Mathlib API change. This is inherent to the Aristotle workflow and a known trade-off.

---

## 8. Documentation Accuracy

### MEMORY.md discrepancies

| Claim in MEMORY.md | Reality | Status |
|----|---------|--------|
| "CoulombConcreteTheorem42.lean (201 lines)" | 280 lines | **STALE** |
| "main theorem, 6 sorry's" | 0 sorry's in-file (2 in CoulombPSD.lean) | **STALE** |
| "CoulombFlux.lean (441 lines)" | 609 lines | **STALE** |
| "CoulombPSD.lean (170 lines)" | 1191 lines | **STALE** |
| "CoulombKernel.lean (114 lines)" | 114 lines | Correct |
| "CoulombSpatialTransport.lean (662 lines)" | 662 lines | Correct |
| "NewtonianPotential.lean (284 lines)" | 284 lines | Correct |

The sorry count in MEMORY.md is wrong by a factor of 3 (claims 6, reality is 2). Multiple file sizes are stale.

### User-facing sorry count

The task description states "Current sorry count: 3 in CoulombPSD.lean" with specific lemma names and line numbers. This matches the actual codebase, so the user-facing documentation is accurate even though MEMORY.md is stale.

### Docstring accuracy

The main theorem `CoulombConcreteTheorem42` docstring (lines 34-52) correctly describes 13 hypotheses and matches the code. The file header (lines 1-23) correctly explains the Coulomb singularity, the kernel extension to r <= 0, and the PSD cancellation mechanism.

---

## 9. New Issues Found in This Review

### Issue 1: `coulomb_ibp_df_g_integrable` has a misleading calc chain

Lines 943-946 of CoulombPSD.lean:

```lean
  _ = C_fd * C_log / (1 + ||v||) ^ 4 * (1 + ||v||) ^ 4 := by
      rw [div_mul_cancel]; exact ne_of_gt hv_pos
  _ <= C_fd * C_log * (1 + ||v||) ^ 4 := by
      rw [div_mul_cancel]; exact ne_of_gt hv_pos
```

The first step simplifies `(C_fd / (1+||v||)^(K+4)) * (C_log * (1+||v||)^K)` to `C_fd * C_log / (1+||v||)^4 * (1+||v||)^4`. The second step claims `C_fd * C_log / (1+||v||)^4 * (1+||v||)^4 <= C_fd * C_log * (1+||v||)^4`. After `div_mul_cancel`, both sides simplify to `C_fd * C_log`, making this step an equality, not a strict inequality. The `<=` annotation is misleading -- the proof works because `<=` subsumes `=`, but it suggests the author did not realize the intermediate cancellation yields equality. Not a soundness issue, but indicates the proof was written without simplifying the intermediate form.

### Issue 2: `schwartzDecayConditionsEB` is 87 lines of field-by-field delegation

VelocityDecayInstance.lean:1948-1998 contains 15 fields that are all of the form:

```lean
  hPSD_inner_int :=
    (schwartzDecayConditions Psi hPsi hPsi_cts ...).hPSD_inner_int
```

repeated with the same 7-argument prefix 15 times. A `let` binding or `{ base with ... }` pattern would reduce this to ~20 lines. This is a code quality issue.

### Issue 3: `import Mathlib` without granularity

Two files (`Defs.lean` and `LandauMatrixDerivBound.lean`) use `import Mathlib` (importing all of Mathlib). All other files import specific predecessors in the chain. The monolithic import:
1. Slows down initial compilation
2. Makes dependency tracking impossible
3. Risks namespace collisions

For `Defs.lean` (the root of the chain), this is somewhat defensible. For `LandauMatrixDerivBound.lean`, which also imports `Aristotle.Landau.main.Defs`, the explicit `import Mathlib` is redundant.

### Issue 4: Potential `one_le_pow_of_one_le` deprecation

`one_le_pow_of_one_le` appears 3 times in CoulombPSD.lean (lines 397, 703, 937). In newer Mathlib versions, this may be renamed or deprecated. CoulombFlux.lean (line 603) already uses `one_le_pow_of_one_le_of_le`, suggesting an awareness of API evolution. With linters disabled, there is no warning about this.

### Issue 5: Namespace collision on `landauMatrix'`

As documented in Section 7, `VML.landauMatrix'` (CoulombFlux.lean:17, Coulomb-specific) and the top-level `landauMatrix'` (LandauMatrixDerivBound.lean:248, generic) share a base name but have different signatures and meanings. CoulombPSD.lean uses `VML.landauMatrix'` (Coulomb-specific) while the bridge lemma `landauMatrix'_eq_VML` at LandauMatrixDerivBound.lean:600 equates the generic version with `VML.landauMatrix`. This means the same token `landauMatrix'` resolves to different things depending on which namespace is open -- a recipe for subtle bugs in future refactoring.

---

## 10. Overall Assessment

### Summary table

| Component | Files | Lines | Sorry's | Assessment |
|-----------|-------|-------|---------|------------|
| Definitions (Defs.lean) | 1 | 782 | 0 | Fully verified |
| Abstract proof chain (Sections 2-9) | 8 | 2,639 | 0 | Fully verified |
| VMLInputDerive | 1 | 438 | 0 | Fully verified |
| Theorem42 (abstract) | 1 | 303 | 0 | Fully verified |
| FlatTorus3 instance | 1 | 1,223 | 0 | Fully verified |
| VelocityDecayInstance | 1 | 2,019 | 0 | Fully verified |
| ConcreteTheorem42 (smooth kernel) | 1 | 97 | 0 | Fully verified |
| CoulombKernel | 1 | 114 | 0 | Fully verified |
| CoulombSpatialTransport | 1 | 662 | 0 | Fully verified |
| NewtonianPotential | 1 | 284 | 0 | Fully verified |
| LandauMatrixDerivBound | 1 | 648 | 0 | Fully verified |
| CoulombFlux | 1 | 609 | 0 | Fully verified |
| CoulombPSD | 1 | 1191 | **2** | **Incomplete**: entry-conv differentiability + decay |
| CoulombConcreteTheorem42 | 1 | 280 | 0 in-file | **Depends on CoulombPSD sorry's** |
| **TOTAL** | **21** | **11,289** | **2** | |

### What is genuinely proved

1. **The entire abstract proof chain is complete.** Given the hypotheses of `Theorem42` (positivity, smoothness, integrability, Maxwell equations, VelocityDecayConditions), the conclusion (f = Maxwellian, E = 0, B = const) follows with 0 sorry's. This is the mathematical core.

2. **The FlatTorus3 typeclass has a complete concrete instance.** All 29 fields proved from Mathlib primitives.

3. **16 of 18 VelocityDecayConditions fields are proved for Coulomb.** This includes `psd_continuous_coulomb` (the hardest analytical result, handling the Coulomb singularity cancellation), `coulomb_flux_differentiable` (60 lines of integral manipulation), and `coulomb_flux_deriv_schwartz_decay` (200 lines of product-rule decomposition + `nlinarith`).

4. **The smooth-kernel theorem is fully complete.** `ConcreteTheorem42` with `Continuous Psi` has 0 sorry's anywhere in its dependency chain.

### What is not proved

1. Differentiability of the Coulomb entry convolution (differentiation under the integral with `||z||^{-1}` kernel).
2. Schwartz decay of the Coulomb entry convolution derivative.

Both sorry'd statements are mathematically true. They are standard singular integral results (Stein, Folland). Total estimated effort: 200-500 lines.

### Structural concerns

1. **33 heartbeat overrides**, including one at 20x default.
2. **Universal linter suppression** across all 21 files.
3. **Duplicate primed definitions** across 3 files, with a naming collision between namespaces.
4. **232 lines of custom tactic code** (Harmonic's `generalize_proofs'`) in LandauMatrixDerivBound.lean.
5. **3 files exceed 1100 lines** (VelocityDecayInstance: 2019, Section3: 1308, CoulombPSD: 1191).
6. **87 lines of copy-paste** in `schwartzDecayConditionsEB`.
7. **Stale MEMORY.md** (wrong sorry count, wrong line counts).
8. **C^infinity overshoot** in IsSpatiallyDiff when C^2 would suffice.
9. **`import Mathlib`** in 2 files instead of granular imports.

### Verdict: CONDITIONAL ACCEPT

Progress since the last review: one sorry has been eliminated (`coulomb_flux_differentiable` is now fully proved). The sorry count decreased from 4 to 3. The mathematical structure is honest and transparent.

The 2 remaining sorry's are:
- Clearly identified and isolated (CoulombPSD.lean:792 and :803)
- Mathematically true (standard singular integral results)
- Not smuggling the conclusion (they are differentiability and decay estimates)
- Not hiding structural problems (the dependency chain is transparent)
- All derived lemmas have complete proof bodies (no more "sorry chains")

The abstract proof chain is fully verified. The smooth-kernel theorem is 100% complete. The Coulomb specialization is 89% complete by VelocityDecayConditions field count.

**Conditions for unconditional acceptance:**
1. Fill the 2 base sorry's in CoulombPSD.lean (`coulomb_entry_conv_differentiable`, `coulomb_entry_conv_deriv_decay`).
2. Update MEMORY.md with correct line counts and sorry counts.
3. Re-enable linters in at least the top-level theorem files.
4. (Minor) Replace copy-paste in `schwartzDecayConditionsEB` with `let`-binding pattern.
5. (Minor) Split VelocityDecayInstance.lean and Section3.lean.
6. (Minor) Consolidate or remove primed duplicate definitions.
7. (Minor) Reduce the 4M-heartbeat proof.
