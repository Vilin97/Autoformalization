# Adversarial Critique — 2026-03-10 UTC (Cycle 53)

## Verdict: ACCEPT WITH MINOR REVISIONS

All required conditions from cycle 52 are resolved. Remaining issues are minor/recommended.

---

## 1. Sorry's

**0 sorry's across 23 files.** Grep confirms no `sorry`, `admit`, `axiom`, or `native_decide` keywords in any `.lean` file. I found no issue.

---

## 2. Hidden Axioms

The formalization relies on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and Mathlib's foundations. No custom `axiom` declarations exist. No `native_decide` usage. No `admit`.

The real "hidden axioms" are the **22 axiom fields of `FlatTorus3`** (Defs.lean:308-400). These are proved for the concrete `Torus3` instance in TorusInstance.lean with 0 sorry's. However:

- **FlatTorus3 is an abstract interface**, not a concrete mathematical object. It encodes "a compact 3-manifold with flat metric, integration, IBP, etc." as uninterpreted axioms. The axioms could be inconsistent if poorly chosen, but the concrete Torus3 instance validates them.
- The `IsSpatiallyDiff` predicate is abstract. On Torus3 it means `ContDiff ℝ ⊤ ∘ periodicLift`. This means **the formalization assumes C^∞ spatial regularity** everywhere, which is stronger than needed (C² typically suffices).

**I found no issue** with hidden axioms beyond the FlatTorus3 abstraction, which is validated by a concrete instance.

---

## 3. Circularity

**Is VelocityDecayConditions satisfiable by a non-equilibrium distribution for the Coulomb kernel?**

NO — and this is the single most important structural weakness. The dead `schwartzDecayConditions` (removed this cycle) proved satisfiability only for **bounded smooth kernels** (Ψ bounded, C¹). The Coulomb kernel Ψ(r) = r⁻³ is unbounded and not C¹ at r = 0. **No non-equilibrium VelocityDecayConditions instance exists for Coulomb.**

The `CoulombConcreteTheorem42` proof constructs a VelocityDecayConditions instance inline for each hypothesis configuration, proving all 19 fields. But the hypotheses include `hSchwartz`, `hExpDecay`, `hGradBound` — these constrain f to be "Schwartz-like." **Is the conjunction (hf_pos ∧ hSchwartz ∧ hExpDecay ∧ hGradBound ∧ hVlasov) satisfiable by a non-Maxwellian f?**

The answer is almost certainly yes (e.g., perturb a Maxwellian slightly), but this is NOT formally verified. The closest evidence is the (now-deleted) smooth-kernel instance, which doesn't apply to Coulomb. **The formalization does not prove that its hypotheses are consistent with a non-trivial steady state.**

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

I found no divergence from the standard mathematical proof. The proof follows the blueprint (H-theorem-formal.pdf, Sections 1-10) faithfully:
1. Entropy dissipation D(f) ≤ 0 (H-theorem)
2. Transport entropy equation → ∫D(f) = 0 → D(f) = 0 pointwise
3. D = 0 → log f is affine in v → f = exp(a + b·v + c|v|²)
4. Polynomial matching from Vlasov → c constant, b constant
5. Killing field + flatness → b = 0
6. Maximum principle → ρ constant → E = 0
7. Maxwell → B constant

The only question is whether the Lean formalization of steps 3-4 (polynomial identity matching) is complete and correct. Since there are 0 sorry's and the kernel verifies it, this is formally settled.

---

## 6. Code Quality

### 6a. Files over 600 lines (7 files)

| File | Lines | Issue |
|------|-------|-------|
| TorusInstance.lean | 1164 | Far too large. Could split into TorusOperators + TorusAnalysis + TorusGeometry |
| Defs.lean | 761 | Borderline. Contains FlatTorus3 + all definitions + VMLInput/VMLSteadyState |
| CoulombPSD.lean | 713 | Acceptable (complex proofs) |
| CoulombSpatialTransport.lean | 662 | Borderline |
| Section3Helpers.lean | 637 | Borderline |
| CoulombFluxDiff.lean | 627 | Borderline |
| CoulombFlux.lean | 608 | Borderline |

### 6b. maxHeartbeats overrides (29 total)

| Value | Count | Files |
|-------|-------|-------|
| 800000 | 15 | CoulombFlux, CoulombSpatialTransport, LandauMatrixDerivBound, Section3, Section3Helpers, TorusInstance |
| 1600000 | 10 | CoulombFluxDiff, CoulombPSD, CoulombSpatialTransport, LandauMatrixDerivBound, NewtonianPotential |
| 3200000 | 4 | CoulombFlux, CoulombPSD, NewtonianPotential |

29 heartbeat overrides across 9 files. The 3200000 values (8x default) indicate proofs that could break with Mathlib updates.

### 6c. Primed definitions (11 duplicates across 3 files, 14 total with TorusInstance helpers)

Inline copies of VML namespace definitions used by Aristotle-generated proofs:

- **CoulombFlux.lean:11-18**: `normSq'`, `eucNorm'`, `innerLandauMatrix'`, `coulombKernel'`, `landauMatrix'`, `vGrad'`
- **LandauMatrixDerivBound.lean:36-43**: `normSq'`, `eucNorm'`, `innerLandauMatrix'`, `landauMatrix'`
- **CoulombPSD.lean:8**: `PSDIntegrand'`

These are unmaintainable: any change to the VML-namespace definition must be manually propagated to every primed copy, with no compiler enforcement. Bridging lemmas (`normSq' = normSq` by `rfl`) would let Aristotle proofs reference the real definitions.

### 6d. Linter suppressions

3 files suppress `linter.unusedSimpArgs`: Defs.lean, Section3Helpers.lean, Section7.lean. Minor.

---

## 7. Documentation Lies

### progress.md — **RESOLVED** (cycle 53)

Rewritten from scratch. Now accurately reflects 22 files, 0 sorry's, correct architecture and axiom counts.

### MEMORY.md — **RESOLVED** (cycle 53)

Updated to 22 files, ~8,300 lines, 19 VelocityDecayConditions fields.

### Docstrings

CoulombConcreteTheorem42 docstring is accurate (13 hypotheses, non-minimality note, scope note). No issues found in theorem-level documentation.

---

## 8. Generalization Opportunities

### 8a. Weaken smoothness: C^∞ → finite regularity (FEASIBLE)

The proof uses at most second derivatives in spatial variables and finite-order velocity derivatives. Replacing `ContDiff ℝ ⊤` with `ContDiff ℝ k` for specific `k` (likely k = 2 or 3) throughout would:
- Make the theorem stronger (weaker hypotheses)
- Better match the physics literature (which assumes finite regularity)
- Require auditing every use of `hf_smooth` to determine the actual derivative order needed

**Effort: Medium.** The main obstacle is `IsSpatiallyDiff = ContDiff ℝ ⊤ ∘ periodicLift` in TorusInstance.lean. Changing to `ContDiff ℝ n` requires parameterizing the typeclass.

### 8b. Remove hGradBound: prove it from hSchwartz + hExpDecay (UNCERTAIN)

The docstring claims hGradBound is "likely derivable from hSchwartz + hExpDecay." The argument sketch: Schwartz decay gives `|∂f/∂v_i| ≤ C_N(1+‖v‖)^{-N}` for all N, while the lower bound gives `f ≥ exp(-C(1+‖v‖)^K)`. Then `|∂f|/f ≤ C_N(1+‖v‖)^{-N} · exp(C(1+‖v‖)^K)`.

For this to be polynomial, we need the exponential factor to be dominated by some polynomial — which it is NOT for large ‖v‖. However, the Schwartz numerator decays faster than ANY polynomial, so for any fixed K in the exponential lower bound, we can choose N large enough that C_N(1+‖v‖)^{-N+K} → 0. This gives `|∂f|/f → 0` but not necessarily a polynomial bound.

**The derivability claim needs careful mathematical analysis.** It may be true (via a more refined argument using the specific form of Schwartz decay), but it is not obvious. The docstring should be softened to "conjectured" rather than "likely."

**Effort: High** (requires mathematical analysis, not just formalization).

### 8c. Generalize beyond Coulomb: soft potentials Ψ(r) = r^γ (HARD)

The current formalization handles only Coulomb (γ = -3). The abstract Theorem42 works for any Ψ > 0, but VelocityDecayConditions must be verified for each kernel. For soft potentials (γ > -3), the singularity is milder. For very soft potentials (γ < -3), the singularity is worse.

**Effort: Very High.** Each kernel family needs its own concrete theorem file.

### 8d. Strengthen conclusion: uniqueness of T_eq (EASY)

The conclusion asserts ∃ T_eq > 0, but doesn't prove uniqueness. Since the Maxwellian is parametrized by (ρ_ion, T), and ρ_ion is fixed, T is uniquely determined. Adding `∀ T₁ T₂, (∀ x v, f x v = equilibriumMaxwellian ρ_ion T₁ v) → (∀ x v, f x v = equilibriumMaxwellian ρ_ion T₂ v) → T₁ = T₂` would strengthen the result.

**Effort: Low.** The Gaussian integral `∫ exp(-|v|²/(2T)) dv = (2πT)^{3/2}` is injective in T.

---

## 9. Mathlib Upstreamability

### 9a. `inverse_poly_integrable` (SchwartzDecayDefs.lean:38)

Shows `C/(1+‖v‖)^4` is integrable on ℝ³. Special case of existing Mathlib lemmas. **Not worth upstreaming** — too specialized.

### 9b. Torus IBP and harmonic function lemmas (TorusInstance.lean)

`torus_hIBP_spatial`, `torus_hHarmonic_const`, `torus_hCurlIntZero` are general facts about functions on `(ℝ/ℤ)³`. **Medium priority** — but would need significant refactoring to use Mathlib's `AddCircle` API idiomatically.

### 9c. `integrable_of_schwartz_bound` (VelocityDecayHelpers.lean:50)

If `‖v‖^k|φ(v)|` integrable for all k and `‖g(v)‖ ≤ C(1+‖v‖)^K|φ(v)|`, then g integrable. Useful domination lemma. **Medium priority** — could fit in `MeasureTheory.Function.L1Space`.

### 9d. `lorentz_component_bound` (VelocityDecayInstance.lean:17)

Elementary linear algebra bound. **Not worth upstreaming.**

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | ~~VelocityDecayHelpers.lean: ~700 lines dead code~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 2 | 11 primed duplicate definitions across 3 files | Minor | Open |
| 3 | ~~progress.md severely stale~~ | ~~Major~~ | **RESOLVED** (cycle 53) |
| 4 | ~~MEMORY.md stale~~ | ~~Minor~~ | **RESOLVED** (cycle 53) |
| 5 | 29 maxHeartbeats overrides (4 at 3200000) | Minor | Open |
| 6 | 7 files over 600 lines (TorusInstance at 1164) | Minor | Open |
| 7 | hGradBound "likely derivable" claim may be incorrect | Epistemic | Open |
| 8 | No non-equilibrium VDC instance for Coulomb kernel | Epistemic | Open |
| 9 | C^∞ smoothness overkill (C² likely suffices) | Minor | Open |
| 10 | Uniqueness of T_eq not proved | Minor | Open |

### Remaining work (all recommended, none required)

1. Add bridging lemmas for primed definitions OR inline-expand them
2. Investigate and correct hGradBound "likely derivable" claim
3. Split TorusInstance.lean (1164 lines)
4. Reduce maxHeartbeats in hot proofs
