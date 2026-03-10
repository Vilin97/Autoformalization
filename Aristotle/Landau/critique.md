# Adversarial Critique — 2026-03-10 UTC (Cycle 59)

## Verdict: CONDITIONAL ACCEPT

Cycle 59 eliminated all primed definitions and fixed LandauMatrixDerivBound.lean compilation. But this introduced a NEW maxHeartbeats override (the 30th → 1 → 2 trajectory is going the wrong direction). The orphaned file problem was discovered but not addressed. Several structural weaknesses persist.

---

## 1. Sorry's

**0 sorry's across 22 files, 8,213 lines.** `lean_verify` on both `VML.Theorem42` and `VML.CoulombConcreteTheorem42` returns zero non-standard axioms and zero warnings.

I found no issue.

---

## 2. Hidden Axioms

Standard Lean axioms only (`propext`, `Classical.choice`, `Quot.sound`). No `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, or `implemented_by`.

The **22 property axioms of `FlatTorus3`** (Defs.lean:308-400) are all validated by the concrete `Torus3` instance in TorusInstance.lean. The `IsSpatiallyDiff` predicate remains an opaque abstraction rather than leveraging Mathlib's `ContDiff` infrastructure — this is a design limitation, not a correctness issue.

I found no issue with hidden axioms.

---

## 3. Circularity

**Is VelocityDecayConditions satisfiable by a non-equilibrium f for the Coulomb kernel?**

Still not formally verified. The hypotheses (hf_pos + hSchwartz + hExpDecay + hGradBound + hVlasov) are standard in kinetic theory, and a slight perturbation of a Maxwellian should satisfy them all except hVlasov. But no formal proof of satisfiability exists. The theorem could vacuously hold if no non-equilibrium steady state satisfies these hypotheses.

This remains the single most important structural weakness. Not fatal (the theorem is a conditional statement and the hypotheses are natural), but the formalization would be significantly strengthened by exhibiting even one non-trivial solution.

---

## 4. Hypothesis Audit

### CoulombConcreteTheorem42 (13 explicit hypotheses)

| # | Name | Necessary? | Could weaken? |
|---|------|-----------|--------------|
| 1 | `hν : 0 < ν` | Yes | No |
| 2 | `hρ_ion : 0 < ρ_ion` | Yes | No |
| 3 | `hf_pos : ∀ x v, 0 < f x v` | Yes (log f) | Could use a.e. positivity (hard) |
| 4 | `hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x)` | Overkill | C² or C³ suffices |
| 5 | `hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift ...)` | Overkill | C² suffices |
| 6 | `hB_smooth : ∀ i, ContDiff ℝ ⊤ (periodicLift ...)` | Overkill | C¹ suffices |
| 7 | `hSchwartz : UniformSchwartzDecay f` | Yes | Could specify exact decay rates needed |
| 8 | `hExpDecay` | Likely derivable from 7+9 | Non-minimal |
| 9 | `hGradBound` | Likely derivable from 7+8 | Non-minimal |
| 10 | `hVlasov` | Yes (the PDE) | No |
| 11 | `hAmpere` | Yes | No |
| 12 | `hGauss` | Yes | No |
| 13 | `hDivB` | Yes | No |

**Key issue: hGradBound (hypothesis 9) is claimed "likely derivable" in the docstring but this has NOT been verified.** The argument is: Schwartz gives |∂f| = O((1+|v|)^{-N}), exponential lower bound gives f ≥ exp(-C(1+|v|)^K), so |∂f|/f ≤ O((1+|v|)^{-N}) · exp(C(1+|v|)^K). For any polynomial bound, choose N >> K. But the ratio needs to be bounded by a FIXED polynomial Cg·(1+|v|)^Kg for ALL v, not just asymptotically. This requires showing the exponential-times-inverse-polynomial is eventually dominated, which it IS (for N > K, (1+|v|)^{-N}·exp(C(1+|v|)^K) → 0), so a global polynomial bound exists by compactness of [0, ∞). **The claim is mathematically correct** but nontrivial to formalize. Still, the docstring should either prove it or stop calling it "likely."

### FlatTorus3 typeclass (22 property axioms)

All validated by Torus3 instance. The abstraction is adequate but could be replaced by a more Mathlib-native design using `CompactSpace`, `SmoothManifoldWithCorners`, etc. This would improve reusability but is a significant refactor.

### VelocityDecayConditions (19 fields)

All 19 proved inline in CoulombConcreteTheorem42. The bundle makes the abstract theorem statement readable but obscures what's actually needed.

---

## 5. Mathematical Correctness

The proof follows the standard Desvillettes-Villani strategy faithfully: H-theorem → D=0 → local Maxwellian → polynomial matching → temperature constant → Killing → drift = 0 → Poisson-Boltzmann → density constant → E = 0 → B constant. Zero sorry's and kernel verification settle this formally.

I found no divergence from the standard proof.

---

## 6. Code Quality

### 6a. LandauMatrixDerivBound.lean is dead code (NEW)

**This file is not imported by any other file in the project.** Grep for `import.*LandauMatrixDerivBound` returns zero matches. The lemmas `landauMatrix_entry_fderiv_norm_bound` and `landauMatrix_entry_abs_bound` are proved but never used in the proof chain. They apply to smooth bounded kernels, not the singular Coulomb kernel.

Cycle 59 spent effort fixing this file's compilation (adding imports, removing duplicates, adding heartbeat overrides) for code that is NEVER EXECUTED in the proof chain. This is wasted work. The file should either be:
- Deleted (if truly unnecessary), or
- Imported where needed and integrated into the proof

### 6b. maxHeartbeats overrides: 2 total (REGRESSION)

| File | Override | Reason |
|------|----------|--------|
| CoulombSpatialTransport.lean:9 | `synthInstance.maxHeartbeats 160000` | HSMul typeclass resolution |
| LandauMatrixDerivBound.lean:291 | `maxHeartbeats 400000` | **NEW** (cycle 59) — Aristotle proof after primed→VML migration |

Cycles 55-58 eliminated all 29 `maxHeartbeats` overrides. Cycle 59 added one back. The `400000` value is exactly the default, which means the proof just barely compiles. Any future Mathlib update could break it. The override was added to a dead file.

### 6c. Files over 600 lines (6 files)

| File | Lines |
|------|-------|
| TorusInstance.lean | 1,162 |
| Defs.lean | 761 |
| CoulombPSD.lean | 703 |
| CoulombSpatialTransport.lean | 662 |
| Section3Helpers.lean | 637 |
| CoulombFluxDiff.lean | 618 |

TorusInstance.lean at 1,162 lines is the most pressing — it should be split.

### 6d. Primed definitions — RESOLVED (cycle 59)

All 11 primed definitions and bridging lemmas eliminated across 4 files. Proofs now use VML namespace defs directly.

### 6e. Linter suppressions (3 files)

`set_option linter.unusedSimpArgs false` in Defs.lean, Section3Helpers.lean, Section7.lean. Minor but should be investigated — unused simp args may indicate proof fragility.

### 6f. Aristotle-generated code in LandauMatrixDerivBound.lean

This file contains machine-generated proofs with extremely long lines (300+ chars), deprecated API usage (`div_add_div_same`), unused simp args, and `refine'` instead of `refine`. It is unmaintainable in its current form. Since it's also dead code, this compounds the problem.

---

## 7. Documentation Lies

### MEMORY.md

Claims "~8,300 lines" — actual is 8,213. Off by ~1%. Acceptable but should be updated.

Claims LandauMatrixDerivBound.lean is "~415 lines" — actual is 363 lines (after cycle 59 cleanup). Should update.

### progress.md

Claims "22 files, ~8,300 lines, 0 sorry's" — close enough to 8,213. No fatal discrepancy.

### critique.md (previous cycle)

Previous critique (cycle 58) stated "0 maxHeartbeats + 1 synthInstance = 1 total" overrides. After cycle 59, the count is 1 maxHeartbeats + 1 synthInstance = 2 total. This was properly reflected in the log but the old critique is now stale (which is expected since we're rewriting it).

---

## 8. Generalization Opportunities

### 8a. Weaken smoothness: C^∞ → C^k (FEASIBLE)

The proof uses at most 2nd spatial derivatives and finite-order velocity derivatives. Replacing `ContDiff ℝ ⊤` with `ContDiff ℝ k` for k = 2 or 3 would strengthen the theorem. **Effort: Medium.** Requires auditing every `ContDiff` usage.

### 8b. Prove hGradBound from hSchwartz + hExpDecay (FEASIBLE)

As analyzed above, the polynomial score bound IS derivable from Schwartz decay + stretched-exponential lower bound. Formalizing this would reduce the hypothesis count from 13 to 12 and eliminate the non-minimality disclaimer. **Effort: Medium-High.** Requires formalizing the compactness argument for exponential-polynomial bounds.

### 8c. Uniqueness of T_eq (EASY)

The conclusion asserts `∃ T_eq > 0` but not `∃! T_eq`. Since the Gaussian integral `∫ exp(-|v|²/2T) dv = (2πT)^{3/2}` is strictly monotone in T, uniqueness follows from the normalization `∫ f = ρ_ion`. **Effort: Low.**

### 8d. Generalize beyond T³: general flat compact manifolds (HARD)

The `FlatTorus3` typeclass is designed for `Fin 3 → AddCircle 1`. Generalizing to arbitrary flat compact Riemannian manifolds would require significant refactoring of the typeclass and replacing dimension-specific proofs (e.g., `fin_cases i` for `Fin 3`). **Effort: Very High.**

### 8e. Generalize beyond Coulomb: soft potentials (HARD)

Only the Coulomb kernel Ψ(r) = r^{-3} is handled concretely. The abstract Theorem42 works for any Ψ > 0, but all 19 VelocityDecayConditions fields must be re-proved for each new kernel. For moderately soft potentials (r^γ with -3 < γ < 0), the singularity is weaker and the proofs should be easier. **Effort: High.**

### 8f. Delete or integrate LandauMatrixDerivBound.lean (EASY)

This orphaned file should either be deleted (saving 363 lines of dead code) or integrated into the proof chain. If the derivative bounds are genuinely useful (e.g., for proving differentiability of flux for non-Coulomb kernels), they should be imported where needed. If not, they're dead weight. **Effort: Low.**

---

## 9. Mathlib Upstreamability

### 9a. `inverse_poly_integrable` (SchwartzDecayDefs.lean:38)

`C/(1+‖v‖)^4` integrable on ℝ³. Too specialized for Mathlib but could be generalized to arbitrary dimension and exponent > dim.

### 9b. Torus IBP and harmonic function lemmas (TorusInstance.lean)

`torus_hIBP_spatial`, `torus_hHarmonic_const`, `torus_hCurlIntZero`. These would need refactoring to use Mathlib's `AddCircle` and `SmoothManifoldWithCorners` APIs. **Medium priority.**

### 9c. `integrable_of_schwartz_bound` (SchwartzDecayDefs.lean)

Domination lemma for Schwartz-class functions. Could fit in `MeasureTheory.Function.L1Space`. **Medium priority.**

### 9d. `inv_norm_schwartz_integrable` (NewtonianPotential.lean)

Shows `∫ ‖v-w‖⁻¹ |g(w)| dw < ∞` for Schwartz g in ℝ³. This is a standard fact about Newtonian potentials. **Medium priority** — would need generalization to arbitrary dimension.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | ~~VelocityDecayHelpers.lean: ~700 lines dead code~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 2 | ~~11 primed definitions + bridging lemmas~~ | ~~Minor~~ | **RESOLVED** (cycle 59) |
| 3 | ~~progress.md severely stale~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 4 | ~~MEMORY.md stale~~ | ~~Minor~~ | **RESOLVED** (cycle 53) |
| 5 | ~~29 maxHeartbeats overrides~~ | ~~Minor~~ | **RESOLVED** (cycles 55-58) |
| 6 | 6 files over 600 lines (TorusInstance at 1,162) | Minor | Open |
| 7 | hGradBound "likely derivable" — unverified claim | Epistemic | Open |
| 8 | No non-equilibrium VDC instance for Coulomb | Epistemic | Open |
| 9 | C^∞ smoothness overkill (C² suffices) | Minor | Open |
| 10 | Uniqueness of T_eq not proved | Minor | Open |
| 11 | ~~MEMORY.md line counts drifted~~ | ~~Trivial~~ | **RESOLVED** (cycle 55) |
| 12 | LandauMatrixDerivBound.lean is dead code (363 lines) | Minor | **NEW** |
| 13 | maxHeartbeats 400000 added to dead file (cycle 59) | Trivial | **NEW** |
| 14 | MEMORY.md line counts stale again (8,300 vs 8,213) | Trivial | **NEW** |

### Conditions for ACCEPT

1. **Delete or integrate LandauMatrixDerivBound.lean** — 363 lines of dead code with a heartbeat override is unacceptable
2. **Update MEMORY.md** line counts to reflect current reality
3. All other issues are recommended improvements, not blocking
