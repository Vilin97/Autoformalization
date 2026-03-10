# Adversarial Critique — 2026-03-10 UTC (Cycle 64)

## Verdict: CONDITIONAL ACCEPT

Cycle 63 split TorusInstance (1,162 → 299 + 816) and weakened velocity smoothness from C^∞ to C³ across 8 files. Good structural progress. But the previous critique was **dishonest**: it claimed "No deprecated refine' remain" when 36 uses exist across 5 files. That lie persisted for at least 2 cycles.

---

## 0. Errors

`lake build Aristotle.Landau.main.CoulombConcreteTheorem42` — **clean, no errors.**

---

## 1. Sorry's

**0 sorry's across 22 files, 7,838 lines.** `lean_verify` on both `VML.CoulombConcreteTheorem42` and `VML.Theorem42` returns zero non-standard axioms.

I found no issue.

---

## 2. Hidden Axioms

Standard Lean axioms only (`propext`, `Classical.choice`, `Quot.sound`). No `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, or `implemented_by`.

The 22 property axioms of `FlatTorus3` are all validated by the concrete `Torus3` instance.

I found no issue.

---

## 3. Circularity

**Is VelocityDecayConditions satisfiable by a non-equilibrium f for the Coulomb kernel?**

Still not formally verified. The theorem could vacuously hold if no non-equilibrium steady state satisfies all 13 hypotheses simultaneously.

This remains the single most important structural weakness.

---

## 4. Hypothesis Audit

### CoulombConcreteTheorem42 (13 explicit hypotheses)

All 13 hypotheses are independent and necessary (established cycle 61).

Velocity smoothness weakened to C³ in abstract chain (cycle 63). Concrete theorem still takes C^∞ (needed for Schwartz). **Spatial smoothness (hypotheses 5-6) still C^∞ — C¹ suffices per the audit.** This is the next weakening target.

---

## 5. Mathematical Correctness

The proof follows the standard Desvillettes-Villani strategy. Zero sorry's and kernel verification settle this.

I found no divergence.

---

## 6. Code Quality

### 6a. Deprecated `refine'` tactic: 36 uses across 5 files

**The cycle 62 critique falsely claimed "No deprecated refine' remain."** This was wrong. There are 36 uses:

| File | Count |
|------|-------|
| CoulombPSD.lean | 13 |
| TorusInstance.lean | 10 |
| NewtonianPotential.lean | 8 |
| Section3Helpers.lean | 4 |
| SchwartzDecayDefs.lean | 1 |

These should be replaced with `refine` (structured) or `exact`/`apply` where appropriate.

### 6b. maxHeartbeats overrides: 1 total

| File | Override | Reason |
|------|----------|--------|
| CoulombSpatialTransport.lean:9 | `synthInstance.maxHeartbeats 160000` | HSMul typeclass resolution |

Acceptable.

### 6c. Files over 600 lines (6 files)

| File | Lines |
|------|-------|
| TorusInstance.lean | 816 |
| Defs.lean | 776 |
| CoulombPSD.lean | 703 |
| CoulombSpatialTransport.lean | 662 |
| Section3Helpers.lean | 625 |
| CoulombFluxDiff.lean | 618 |

TorusInstance was split in cycle 63 (from 1,162 to 816) but still exceeds 600. Defs.lean at 776 is the next split candidate.

---

## 7. Documentation Lies

### MEMORY.md

**Stale.** Claims "21 files, ~7,895 lines" — now 22 files, 7,838 lines. TorusDefs.lean was added in cycle 63 but MEMORY.md was not updated. The "Sorry Status" section also says "21 files" and "(as of cycle 53)" — should be updated.

### Previous critique.md

**Lied about refine'.** Issue #16 was marked RESOLVED claiming all deprecated `refine'` were fixed. Only 3 files (Section3Helpers, Defs, VelocityDecayInstance) were actually fixed. The other 5 files with `refine'` were never touched.

---

## 8. Generalization Opportunities

### 8a. Weaken spatial smoothness: C^∞ → C¹ (FEASIBLE)

The velocity smoothness was weakened to C³ in cycle 63. The spatial smoothness (`hf_smooth_x`, `hB_smooth`) is still C^∞ but the audit showed C¹ suffices. However, `IsSpatiallyDiff` is defined as `ContDiff ℝ ⊤ (periodicLift f)` in the FlatTorus3 typeclass, so this requires changing the typeclass definition. **Medium effort.**

### 8b. Exhibit a non-equilibrium VDC-satisfying instance (MEDIUM)

Address the circularity concern. Construct a non-equilibrium Schwartz-class distribution and verify it satisfies all 13 hypotheses. **Medium effort.**

### 8c. Generalize beyond T³: general flat compact manifolds (HARD)

Requires rewriting the FlatTorus3 typeclass to abstract over dimension and manifold structure. **Very high effort.**

---

## 9. Mathlib Upstreamability

### 9a. `inverse_poly_integrable` (SchwartzDecayDefs.lean)

Generalizable to arbitrary dimension and exponent > dim. **Medium priority.**

### 9b. Torus IBP and harmonic function lemmas (TorusInstance.lean)

Would need refactoring to Mathlib's `AddCircle` and `SmoothManifoldWithCorners`. **Medium priority.**

### 9c. `equilibriumMaxwellian_T_unique` (Defs.lean)

Injectivity of T ↦ equilibriumMaxwellian ρ T. **Low priority.**

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | ~~VelocityDecayHelpers.lean: ~700 lines dead code~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 2 | ~~11 primed definitions + bridging lemmas~~ | ~~Minor~~ | **RESOLVED** (cycle 59) |
| 3 | ~~progress.md severely stale~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 4 | ~~MEMORY.md stale~~ | ~~Minor~~ | **RESOLVED** (cycle 53) |
| 5 | ~~29 maxHeartbeats overrides~~ | ~~Minor~~ | **RESOLVED** (cycles 55-58) |
| 6 | 6 files over 600 lines (TorusInstance 816, Defs 776) | Minor | Open |
| 7 | ~~hGradBound "likely derivable" — false claim~~ | ~~Epistemic~~ | **RESOLVED** (cycle 61) |
| 8 | No non-equilibrium VDC instance for Coulomb | Epistemic | Open |
| 9 | ~~C^∞ velocity smoothness overkill~~ | ~~Minor~~ | **RESOLVED** (cycle 63, weakened to C³) |
| 10 | ~~Uniqueness of T_eq not proved~~ | ~~Minor~~ | **RESOLVED** (cycle 61) |
| 11 | ~~MEMORY.md line counts drifted~~ | ~~Trivial~~ | **RESOLVED** (cycle 55) |
| 12 | ~~LandauMatrixDerivBound.lean is dead code~~ | ~~Minor~~ | **RESOLVED** (cycle 60) |
| 13 | ~~maxHeartbeats 400000 added to dead file~~ | ~~Trivial~~ | **RESOLVED** (cycle 60) |
| 14 | ~~MEMORY.md line counts stale (8,300 vs 8,213)~~ | ~~Trivial~~ | **RESOLVED** (cycle 60) |
| 15 | ~~3 linter.unusedSimpArgs suppressions~~ | ~~Minor~~ | **RESOLVED** (cycle 60) |
| 16 | 36 deprecated `refine'` across 5 files | Minor | Open |
| 17 | ~~Deprecated `integral_mul_right` in Defs.lean~~ | ~~Trivial~~ | **RESOLVED** (cycle 61) |
| 18 | Cosmetic: multiGoal violations, long lines | Trivial | Open |
| 19 | MEMORY.md stale (says 21 files, should be 22) | Trivial | Open |
| 20 | ~~Build verification: must force-recompile modified files~~ | ~~Process~~ | **RESOLVED** (cycle 62) |
| 21 | C^∞ spatial smoothness overkill (C¹ suffices) | Minor | Open |

### Conditions for ACCEPT

Fix issues #16 (refine'), #19 (MEMORY.md), and make progress on at least one of #6, #8, or #21.
