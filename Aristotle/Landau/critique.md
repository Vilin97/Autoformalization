# Adversarial Critique — 2026-03-10 UTC (Cycle 58)

## Verdict: ACCEPT WITH MINOR REVISIONS

Cycles 55-58 eliminated ALL 29 `maxHeartbeats` overrides (all were unnecessary — every proof compiles at default 400000). Only 1 `synthInstance.maxHeartbeats 160000` remains. Remaining issues are minor.

---

## 1. Sorry's

**0 sorry's across 22 files.** Grep confirms no `sorry`, `admit`, `axiom`, or `native_decide` keywords in any `.lean` file (only occurrences are inside comments). `lean_verify` on both `VML.Theorem42` and `VML.CoulombConcreteTheorem42` returns zero axioms and zero warnings.

I found no issue.

---

## 2. Hidden Axioms

The formalization relies on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and Mathlib's foundations. No custom `axiom` declarations exist. No `native_decide` usage. No `admit`.

The real "hidden axioms" are the **22 axiom fields of `FlatTorus3`** (Defs.lean:308-400). These are proved for the concrete `Torus3` instance in TorusInstance.lean with 0 sorry's. However:

- **FlatTorus3 is an abstract interface**, not a concrete mathematical object. It encodes "a compact 3-manifold with flat metric, integration, IBP, etc." as uninterpreted axioms. The axioms could be inconsistent if poorly chosen, but the concrete Torus3 instance validates them.
- The `IsSpatiallyDiff` predicate is abstract. On Torus3 it means `ContDiff ℝ ⊤ ∘ periodicLift`. This means **the formalization assumes C^∞ spatial regularity** everywhere, which is stronger than needed (C² typically suffices).

I found no issue with hidden axioms beyond the FlatTorus3 abstraction, which is validated by a concrete instance.

---

## 3. Circularity

**Is VelocityDecayConditions satisfiable by a non-equilibrium distribution for the Coulomb kernel?**

NO — and this remains the single most important structural weakness. No non-equilibrium `VelocityDecayConditions` instance exists for Coulomb. The `CoulombConcreteTheorem42` proof constructs one inline, but the hypotheses (`hSchwartz`, `hExpDecay`, `hGradBound`) constrain f to be "Schwartz-like." **Is the conjunction (hf_pos ∧ hSchwartz ∧ hExpDecay ∧ hGradBound ∧ hVlasov) satisfiable by a non-Maxwellian f?**

Almost certainly yes (e.g., perturb a Maxwellian slightly), but this is NOT formally verified. **The formalization does not prove that its hypotheses are consistent with a non-trivial steady state.**

This is a genuine weakness but NOT a fatal one: the theorem is of the form "IF these hypotheses hold THEN equilibrium," and the hypotheses are standard in kinetic theory literature.

---

## 4. Hypothesis Audit

### CoulombConcreteTheorem42 (13 explicit hypotheses)

| # | Name | Necessary? | Could weaken? |
|---|------|-----------|--------------|
| 1 | `hν : 0 < ν` | Yes | No |
| 2 | `hρ_ion : 0 < ρ_ion` | Yes | No |
| 3 | `hf_pos : ∀ x v, 0 < f x v` | Yes (log f) | Could use a.e. positivity, but complicates everything |
| 4 | `hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x)` | Overkill | C² or C³ suffices for all calculus used |
| 5 | `hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift ...)` | Overkill | C² suffices (only need grad, div, IBP) |
| 6 | `hB_smooth : ∀ i, ContDiff ℝ ⊤ (periodicLift ...)` | Overkill | C¹ suffices (curl needs one derivative) |
| 7 | `hSchwartz : UniformSchwartzDecay f` | Yes | Could weaken to specific polynomial decay rates |
| 8 | `hExpDecay` | Likely derivable from 7+9 | See non-minimality note in docstring |
| 9 | `hGradBound` | Likely derivable from 7+8 | See non-minimality note in docstring |
| 10 | `hVlasov` | Yes (the PDE) | No |
| 11 | `hAmpere` | Yes | No |
| 12 | `hGauss` | Yes | No |
| 13 | `hDivB` | Yes | No |

### FlatTorus3 typeclass (implicit)

22 axiom fields + 3 instance fields + 3 operator fields + 1 predicate = 29 total fields. All validated by the Torus3 instance. The typeclass design is adequate but the abstraction level is questionable — `IsSpatiallyDiff` is an opaque predicate rather than leveraging Mathlib's `ContDiff` infrastructure directly.

### VelocityDecayConditions (19 fields)

All 19 fields are proved inline in CoulombConcreteTheorem42. The structure bundles integrability, Fubini, IBP, differentiability, and continuity conditions. This is an honest engineering choice (keeps Theorem42 statement readable) but makes the theorem's actual strength hard to assess without expanding the bundle.

---

## 5. Mathematical Correctness

I found no divergence from the standard mathematical proof. The proof follows the blueprint faithfully through all 7 steps (H-theorem → transport → affine → polynomial matching → Killing → maximum principle → Maxwell). Since there are 0 sorry's and the kernel verifies it, this is formally settled.

---

## 6. Code Quality

### 6a. Files over 600 lines (7 files)

| File | Lines | Issue |
|------|-------|-------|
| TorusInstance.lean | 1162 | Far too large. Could split into TorusOperators + TorusAnalysis + TorusGeometry |
| Defs.lean | 761 | Borderline. Contains FlatTorus3 + all definitions + VMLInput/VMLSteadyState |
| CoulombPSD.lean | 715 | Acceptable (complex proofs) |
| CoulombSpatialTransport.lean | 662 | Borderline |
| Section3Helpers.lean | 637 | Borderline |
| CoulombFluxDiff.lean | 627 | Borderline |
| CoulombFlux.lean | 615 | Borderline |

### 6b. maxHeartbeats overrides (0 maxHeartbeats + 1 synthInstance = 1 total)

**ALL `maxHeartbeats` overrides eliminated** (cycles 55-58). Every proof compiles at default (400000).

| Value | Status |
|-------|--------|
| ~~800000 (12)~~ | **ALL ELIMINATED** (cycles 55-56) |
| ~~1600000 (11)~~ | **ALL ELIMINATED** (cycle 57) |
| ~~3200000 (6)~~ | **ALL ELIMINATED** (cycle 58) |
| synthInstance 160000 (1) | Remains in CoulombSpatialTransport.lean |

1 override remaining across all files (down from 30 at cycle 54).

### 6c. Primed definitions (11 duplicates across 3 files) — PARTIALLY ADDRESSED (cycle 54)

Bridging lemmas were added in cycle 54:
- **CoulombFlux.lean**: 6 bridging lemmas (`normSq'_eq`, `eucNorm'_eq`, `innerLandauMatrix'_eq`, `coulombKernel'_eq`, `landauMatrix'_eq`, `vGrad'_eq`)
- **CoulombPSD.lean**: 1 bridging lemma (`PSDIntegrand'_eq`)
- **LandauMatrixDerivBound.lean**: 3 new bridging lemmas + 1 existing (`normSq'_eq_VML`, `eucNorm'_eq_VML`, `innerLandauMatrix'_eq_VML`, `landauMatrix'_eq_VML`)

**Problem: 9 of 11 bridging lemmas are NEVER USED.** Only `landauMatrix'_eq_VML` (LandauMatrixDerivBound.lean:367, used at lines 405 and 414) is referenced in any proof. The other 10 are dead code. The bridging "works" implicitly via Lean's definitional equality — proofs using `normSq'` already typecheck against `normSq` without explicit rewrites.

The bridging lemmas document the intended relationship but do not enforce it at compile time. The primed definitions themselves still exist and could silently diverge from the VML versions if someone edits one but not the other. The correct fix would be to **eliminate the primed definitions entirely** and rewrite the Aristotle-generated proofs to use VML namespace definitions directly. The bridging lemmas are a half-measure.

### 6d. Linter suppressions

3 files suppress `linter.unusedSimpArgs`: Defs.lean, Section3Helpers.lean, Section7.lean. Minor.

---

## 7. Documentation Lies

### progress.md — ACCURATE (verified cycle 54)

Claims 22 files, ~8,300 lines, 0 sorry's. Actual: 22 files, 8,317 lines, 0 sorry's. No issues.

### MEMORY.md — ACCURATE (verified cycle 55)

Line counts updated in cycle 55. No issues.

### Docstrings

CoulombConcreteTheorem42 docstring is accurate (13 hypotheses, non-minimality note, scope note). No issues found.

---

## 8. Generalization Opportunities

### 8a. Weaken smoothness: C^∞ → finite regularity (FEASIBLE)

The proof uses at most second derivatives in spatial variables and finite-order velocity derivatives. Replacing `ContDiff ℝ ⊤` with `ContDiff ℝ k` for specific `k` (likely k = 2 or 3) throughout would make the theorem stronger. **Effort: Medium.**

### 8b. Remove hGradBound: prove it from hSchwartz + hExpDecay (UNCERTAIN)

The docstring claims hGradBound is "likely derivable." The argument: Schwartz decay gives `|∂f/∂v_i| ≤ C_N(1+‖v‖)^{-N}` for all N, while the lower bound gives `f ≥ exp(-C(1+‖v‖)^K)`. Then `|∂f|/f ≤ C_N(1+‖v‖)^{-N} · exp(C(1+‖v‖)^K)`. For any fixed K, choosing N > K gives `|∂f|/f → 0`, but not necessarily a polynomial bound. **The derivability claim needs careful mathematical analysis.** **Effort: High.**

### 8c. Generalize beyond Coulomb: soft potentials Ψ(r) = r^γ (HARD)

Only Coulomb (γ = -3) is handled. The abstract Theorem42 works for any Ψ > 0, but VelocityDecayConditions must be verified for each kernel. **Effort: Very High.**

### 8d. Strengthen conclusion: uniqueness of T_eq (EASY)

The conclusion asserts ∃ T_eq > 0 but not uniqueness. Since the Gaussian integral is injective in T, uniqueness follows immediately. **Effort: Low.**

### 8e. Eliminate primed definitions entirely (MEDIUM)

Rather than bridging lemmas, rewrite the 3 Aristotle-generated proof files to use VML namespace definitions directly. This eliminates 11 duplicate definitions and 11 dead bridging lemmas. **Effort: Medium** (mechanical rewriting, but Aristotle proofs are opaque and may break if `unfold` targets change).

---

## 9. Mathlib Upstreamability

### 9a. `inverse_poly_integrable` (SchwartzDecayDefs.lean:38)

Shows `C/(1+‖v‖)^4` is integrable on ℝ³. **Not worth upstreaming** — too specialized.

### 9b. Torus IBP and harmonic function lemmas (TorusInstance.lean)

`torus_hIBP_spatial`, `torus_hHarmonic_const`, `torus_hCurlIntZero`. **Medium priority** — needs refactoring to use Mathlib's `AddCircle` API.

### 9c. `integrable_of_schwartz_bound` (SchwartzDecayDefs.lean)

Domination lemma: if `‖v‖^k|φ(v)|` integrable for all k and `‖g(v)‖ ≤ C(1+‖v‖)^K|φ(v)|`, then g integrable. **Medium priority** — could fit in `MeasureTheory.Function.L1Space`.

### 9d. `lorentz_component_bound` (VelocityDecayInstance.lean:17)

Elementary linear algebra bound. **Not worth upstreaming.**

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | ~~VelocityDecayHelpers.lean: ~700 lines dead code~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 2 | 11 primed definitions + 9 unused bridging lemmas (20 lines dead code) | Minor | Partially addressed (cycle 54) |
| 3 | ~~progress.md severely stale~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 4 | ~~MEMORY.md stale~~ | ~~Minor~~ | **RESOLVED** (cycle 53) |
| 5 | ~~29 maxHeartbeats overrides~~ (1 synthInstance remains) | ~~Minor~~ | **RESOLVED** (cycles 55-58) |
| 6 | 7 files over 600 lines (TorusInstance at 1162) | Minor | Open |
| 7 | hGradBound "likely derivable" claim may be incorrect | Epistemic | Open |
| 8 | No non-equilibrium VDC instance for Coulomb kernel | Epistemic | Open |
| 9 | C^∞ smoothness overkill (C² likely suffices) | Minor | Open |
| 10 | Uniqueness of T_eq not proved | Minor | Open |
| 11 | ~~MEMORY.md line counts drifted~~ | ~~Trivial~~ | **RESOLVED** (cycle 55) |

### Remaining work (all recommended, none required)

1. Eliminate primed definitions entirely (replace with VML namespace defs in proofs)
2. Investigate and correct hGradBound "likely derivable" claim
3. Split TorusInstance.lean (1162 lines)
