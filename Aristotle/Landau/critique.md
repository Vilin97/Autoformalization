# Adversarial Critique — 2026-03-10 UTC (Cycle 61)

## Verdict: CONDITIONAL ACCEPT

Cycle 61 proved T_eq uniqueness and corrected the false claim that hGradBound is derivable. All 8 unused simp args in Defs.lean fixed. The formalization is mathematically stronger than any previous cycle. Remaining issues are code quality (large files, unused simp args in Section3Helpers) and epistemic (circularity, C^∞ overkill).

---

## 1. Sorry's

**0 sorry's across 21 files, 7,895 lines.** `lean_verify` on `VML.CoulombConcreteTheorem42`, `VML.CoulombConcreteTheorem42_unique_T`, and `VML.Theorem42` returns zero non-standard axioms and zero warnings.

I found no issue.

---

## 2. Hidden Axioms

Standard Lean axioms only. No `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, or `implemented_by`.

The 22 property axioms of `FlatTorus3` are all validated by the concrete `Torus3` instance. `IsSpatiallyDiff` remains opaque rather than using Mathlib's `ContDiff` — a design limitation, not a correctness issue.

I found no issue with hidden axioms.

---

## 3. Circularity

**Is VelocityDecayConditions satisfiable by a non-equilibrium f for the Coulomb kernel?**

Still not formally verified. The hypotheses (hf_pos + hSchwartz + hExpDecay + hGradBound + hVlasov) are standard in kinetic theory, but no formal proof of satisfiability exists. The theorem could vacuously hold if no non-equilibrium steady state satisfies all 13 hypotheses simultaneously.

This remains the single most important structural weakness.

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
| 8 | `hExpDecay` | Yes | Independent |
| 9 | `hGradBound` | Yes | **Independent** (cycle 61 corrected the false "likely derivable" claim) |
| 10 | `hVlasov` | Yes (the PDE) | No |
| 11 | `hAmpere` | Yes | No |
| 12 | `hGauss` | Yes | No |
| 13 | `hDivB` | Yes | No |

**Cycle 61 correction:** hGradBound was previously claimed "likely derivable from hSchwartz + hExpDecay". This is **false**: for f(v) = exp(-|v|²)(2 + sin(exp(⟨v⟩))), the function is Schwartz with stretched-exponential lower bound, but |∂f|/f grows like exp(⟨v⟩), which is not polynomial. The hypothesis list is now understood to be independent (all 13 necessary).

### Conclusion strength

Cycle 61 added `CoulombConcreteTheorem42_unique_T`, proving T_eq is the unique temperature satisfying the Maxwellian identity. This addresses critique #10.

---

## 5. Mathematical Correctness

The proof follows the standard Desvillettes-Villani strategy faithfully. Zero sorry's and kernel verification settle this formally.

I found no divergence from the standard proof.

---

## 6. Code Quality

### 6a. Unused simp args: Defs.lean CLEAN, Section3Helpers.lean still dirty

Defs.lean now has zero `unusedSimpArgs` warnings (cycle 61 fixed all 8). Section3Helpers.lean still has ~30 warnings. These are cosmetic but indicate fragile proofs.

### 6b. maxHeartbeats overrides: 1 total

| File | Override | Reason |
|------|----------|--------|
| CoulombSpatialTransport.lean:9 | `synthInstance.maxHeartbeats 160000` | HSMul typeclass resolution |

Acceptable.

### 6c. Files over 600 lines (5 files)

| File | Lines |
|------|-------|
| TorusInstance.lean | 1,162 |
| Defs.lean | 776 |
| CoulombPSD.lean | 703 |
| CoulombSpatialTransport.lean | 662 |
| Section3Helpers.lean | 635 |

TorusInstance.lean at 1,162 lines remains the most pressing split candidate.

### 6d. Style issues in Section3Helpers.lean

- 3 uses of `refine'` (deprecated)
- Multiple `multiGoal` violations
- Unused variables (`hn_pos`, `hρ`, `hf_smooth`, `hf_pos`)
- Lines exceeding 600 characters

---

## 7. Documentation Lies

### MEMORY.md

Claims "21 files, ~7,850 lines" — actual is 21 files, 7,895 lines. Off by ~0.6%. Should update.

### progress.md

Claims "21 files, ~7,850 lines" — same minor drift.

---

## 8. Generalization Opportunities

### 8a. Weaken smoothness: C^∞ → C^k (FEASIBLE)

The proof uses at most 2nd spatial derivatives and finite-order velocity derivatives. Replacing `ContDiff ℝ ⊤` with `ContDiff ℝ k` for k = 2 or 3 would strengthen the theorem. **Effort: Medium.**

### 8b. Generalize beyond T³: general flat compact manifolds (HARD)

The `FlatTorus3` typeclass is designed for `Fin 3 → AddCircle 1`. Generalizing to arbitrary flat compact Riemannian manifolds would require replacing dimension-specific proofs. **Effort: Very High.**

### 8c. Generalize beyond Coulomb: soft potentials (HARD)

Only the Coulomb kernel Ψ(r) = r^{-3} is handled concretely. For moderately soft potentials (r^γ with -3 < γ < 0), the singularity is weaker and the VDC proofs should be easier. **Effort: High.**

### 8d. Exhibit a non-equilibrium satisfying instance (MEDIUM)

Address the circularity concern by constructing a non-trivial f satisfying all 13 hypotheses except hVlasov (showing the non-PDE hypotheses are jointly satisfiable), or finding a time-dependent solution that satisfies all 13 at t=0. **Effort: Medium.**

### 8e. Clean up Section3Helpers unused simp args (EASY)

~30 unused simp argument warnings. Tedious but low risk. **Effort: Low.**

---

## 9. Mathlib Upstreamability

### 9a. `inverse_poly_integrable` (SchwartzDecayDefs.lean:38)

Generalizable to arbitrary dimension and exponent > dim. **Medium priority.**

### 9b. Torus IBP and harmonic function lemmas (TorusInstance.lean)

Would need refactoring to Mathlib's `AddCircle` and `SmoothManifoldWithCorners`. **Medium priority.**

### 9c. `equilibriumMaxwellian_T_unique` (Defs.lean — NEW)

The injectivity of T ↦ equilibriumMaxwellian ρ T could be useful in other contexts. Would need generalization beyond dimension 3. **Low priority.**

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | ~~VelocityDecayHelpers.lean: ~700 lines dead code~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 2 | ~~11 primed definitions + bridging lemmas~~ | ~~Minor~~ | **RESOLVED** (cycle 59) |
| 3 | ~~progress.md severely stale~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 4 | ~~MEMORY.md stale~~ | ~~Minor~~ | **RESOLVED** (cycle 53) |
| 5 | ~~29 maxHeartbeats overrides~~ | ~~Minor~~ | **RESOLVED** (cycles 55-58) |
| 6 | 5 files over 600 lines (TorusInstance at 1,162) | Minor | Open |
| 7 | ~~hGradBound "likely derivable" — false claim~~ | ~~Epistemic~~ | **RESOLVED** (cycle 61 — corrected to "independent") |
| 8 | No non-equilibrium VDC instance for Coulomb | Epistemic | Open |
| 9 | C^∞ smoothness overkill (C² suffices) | Minor | Open |
| 10 | ~~Uniqueness of T_eq not proved~~ | ~~Minor~~ | **RESOLVED** (cycle 61) |
| 11 | ~~MEMORY.md line counts drifted~~ | ~~Trivial~~ | **RESOLVED** (cycle 55) |
| 12 | ~~LandauMatrixDerivBound.lean is dead code~~ | ~~Minor~~ | **RESOLVED** (cycle 60) |
| 13 | ~~maxHeartbeats 400000 added to dead file~~ | ~~Trivial~~ | **RESOLVED** (cycle 60) |
| 14 | ~~MEMORY.md line counts stale (8,300 vs 8,213)~~ | ~~Trivial~~ | **RESOLVED** (cycle 60) |
| 15 | ~~3 linter.unusedSimpArgs suppressions~~ | ~~Minor~~ | **RESOLVED** (cycle 60) |
| 16 | ~30 unused simp args in Section3Helpers.lean | Minor | Open (Defs.lean CLEAN as of cycle 61) |
| 17 | ~~Deprecated `integral_mul_right` in Defs.lean~~ | ~~Trivial~~ | **RESOLVED** (cycle 61) |
| 18 | Style issues in Section3Helpers (refine', multiGoal, long lines) | Minor | Open |
| 19 | MEMORY.md line count drift (7,850 vs 7,895) | Trivial | **NEW** |

### Conditions for ACCEPT

1. **Fix MEMORY.md line counts** — trivial, should match reality
2. All other issues are recommended improvements, not blocking
