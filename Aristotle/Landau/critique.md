# Adversarial Critique: Coulomb Concrete Theorem 42

**Reviewer posture:** Hostile. Default verdict is REJECT. The formalization must earn approval through evidence.

**Reviewed file:** `Aristotle/Landau/main/CoulombConcreteTheorem42.lean` (271 lines)
**Full codebase:** 21 .lean files, ~10,500 total lines in `Aristotle/Landau/main/`

**Claim:** Any sufficiently smooth, positive, Schwartz-class steady-state solution of the Vlasov-Maxwell-Landau system with Coulomb collisions on T^3 is a global Maxwellian equilibrium with E = 0 and B = const.

---

## 1. Sorry's

There are **3 sorry's** in `CoulombConcreteTheorem42.lean`, down from 5 in the prior critique.

| # | File:Line | Field | Statement |
|---|-----------|-------|-----------|
| 1 | CoulombConcreteTheorem42.lean:166 | `hFubini_double` | Joint integrability of PSD integrand on (ℝ³)² |
| 2 | CoulombConcreteTheorem42.lean:196 | `hLandauFluxDiff` | `∀ x i, Differentiable ℝ (fun v => flux_component i v)` |
| 3 | CoulombConcreteTheorem42.lean:197 | `hLandauIBP_df_g` | Integrability of `∂_i(flux_i)(v) * log(f(v))` |

**Progress since last critique:** `hPSD_inner_int` and `hPSD_outer_int` (sorry's #1-2 in the previous critique) have been fully proved via `psd_inner_integrable_coulomb` and `psd_outer_integrable_coulomb` in CoulombPSD.lean. This is genuine progress — the PSD integrability was the hardest analytical component.

### Assessment of each sorry

**Sorry 1 (hFubini_double).** Joint integrability on (ℝ³)² of the score-flux dot product. Needed for Fubini symmetrization in the H-theorem. The integrand involves `‖v-w‖⁻¹` from the Coulomb kernel multiplied by Schwartz decay in both variables, with O(|v-w|) cancellation near the diagonal from the score difference. Standard: locally integrable + rapid decay → integrable on product space. **Mathematically true.**

**Worst case if false:** The entropy dissipation identity D(f) = -(1/2) ∫∫ PSD breaks. The entire proof collapses.

**Sorry 2 (hLandauFluxDiff).** Differentiability of each flux component `v ↦ ∫_w A(v-w)[f(w)∇f(v) - f(v)∇f(w)]_i`. This is differentiation under the integral sign with a singular kernel. The smooth-kernel proof uses `landau_flux_component_diff_with_bound` which requires `Continuous Ψ` — excluding Coulomb. A Coulomb-specific argument needs: (1) `‖∂_v A(v-w)‖ ≤ C‖v-w‖⁻²` (locally integrable in ℝ³), (2) Schwartz decay of f, (3) dominated convergence (Folland, Theorem 2.27). **Mathematically true.**

**Worst case if false:** Velocity-space IBP cannot be applied to the Landau operator. The symmetrized weak form is not established.

**Sorry 3 (hLandauIBP_df_g).** Integrability of `∂_i(flux_i)(v) * log(f(v))`. Given sorry 2, the flux derivative decays Schwartz-fast (inherited from f), and `log(f)` grows at most polynomially (proved: `schwartz_log_bound`). Product of Schwartz decay × polynomial growth = integrable. **Blocked on sorry 2; mathematically true.**

**Worst case if false:** IBP for the Landau operator breaks.

**Overall sorry verdict:** All 3 sorry statements are mathematically true and represent genuine technical lemmas about singular-kernel regularity. None sneaks the conclusion into the hypotheses. They represent the gap between "smooth kernel" and "Coulomb kernel" — specifically, differentiation under the integral and Fubini for ‖z‖⁻¹ singularity. The physically important case is 82% complete (15 of 18 VelocityDecayConditions fields proved).

---

## 2. Hidden Axioms

No `axiom` declarations found. No `admit`. No `native_decide`. No unsafe `Decidable.decide`.

All imports are from Mathlib and the project's own files. `lean_verify` on the abstract theorem shows only `propext`, `Classical.choice`, and `Quot.sound` — standard Lean 4 foundational axioms.

`set_option linter.all false` appears in all 21 files. This prevents automated detection of problems but is not an axiom. See Section 6.

I found no issue with hidden axioms.

---

## 3. Circularity

### Dependency chain

```
CoulombConcreteTheorem42
  imports: CoulombSpatialTransport, CoulombFlux, CoulombPSD
    imports: NewtonianPotential
      imports: CoulombKernel
        imports: ConcreteTheorem42
          imports: Theorem42, TorusInstance, VelocityDecayInstance
            imports: VMLInputDerive
              imports: Defs, Section2-9
```

### Is any hypothesis equivalent to the conclusion?

No. The hypotheses are: positivity, smoothness, Schwartz decay, stretched-exponential lower bound, polynomial score bound, and four VML equations. The conclusion is f = Maxwellian, E = 0, B = const. No circular reasoning.

### Is VelocityDecayConditions satisfiable by a non-equilibrium distribution for Coulomb?

**The formalization now provides partial evidence.** Of 18 fields, 15 are fully proved for arbitrary Schwartz functions with Coulomb kernel. The remaining 3 sorry's are the only gap. The existing `schwartzDecayConditions` instance requires `Continuous Ψ` (excluding Coulomb), so no complete satisfiability witness exists for Coulomb. However, the 15 proved fields demonstrate substantial (82%) satisfiability, reducing the concern from the prior critique.

I found no circularity.

---

## 4. Hypothesis Audit

The main theorem has 13 explicit hypotheses (lines 59-81):

| # | Name | Type | Necessary? | Could weaken? |
|---|------|------|-----------|--------------|
| 1 | `hnu` | `0 < ν` | Yes | No |
| 2 | `hrho_ion` | `0 < ρ_ion` | Yes | No |
| 3 | `hf_pos` | `∀ x v, 0 < f x v` | Yes | To a.e., at enormous cost |
| 4 | `hf_smooth_v` | `∀ x, ContDiff ℝ ⊤ (f x)` | Yes | C² might suffice |
| 5 | `hf_smooth_x` | `∀ v, ContDiff ℝ ⊤ (periodicLift (x ↦ f x v))` | Yes | C² might suffice |
| 6 | `hB_smooth` | `∀ i, ContDiff ℝ ⊤ (periodicLift (x ↦ B x i))` | Yes | C¹ might suffice |
| 7 | `hSchwartz` | `UniformSchwartzDecay f` | Yes | Strongest assumption |
| 8 | `hExpDecay` | Stretched-exponential lower bound | Yes | Could weaken to polynomial |
| 9 | `hGradBound` | Polynomial score bound | **Partially redundant with 7+8** | Could derive instead |
| 10 | `hVlasov` | Steady-state Vlasov equation | Core physics | No |
| 11 | `hAmpere` | Ampère's law | Core physics | No |
| 12 | `hGauss` | Gauss's law | Core physics | No |
| 13 | `hDivB` | div B = 0 | Core physics | No |

### Redundancy of hypothesis 9

For Schwartz f with stretched-exponential lower bound: |∂f/∂v_i| decays faster than any polynomial (Schwartz), while 1/f grows at most sub-exponentially (exp decay lower bound). Thus |∂f/∂v_i|/f is polynomially bounded. The formalization takes this as a separate hypothesis rather than deriving it. This inflates the hypothesis count from 12 to 13 without adding mathematical content.

### No hypothesis secretly assumes the conclusion

All hypotheses concern regularity and decay, not the specific form of f.

---

## 5. Mathematical Correctness

### The overall proof strategy is correct

The proof follows the standard Desvillettes-Villani / Guo argument:
1. H-theorem: D(f) = 0 at steady state.
2. D(f) = 0 → f locally Maxwellian (PSD = 0 → score parallelism → affine score → quadratic log f).
3. Temperature constant (polynomial matching).
4. Drift constant (Killing equation on flat T³ → harmonic → constant).
5. Drift = 0 (Ampère + Stokes on T³).
6. Density constant (Poisson-Boltzmann maximum principle).
7. E = 0 (force balance), B = const (harmonic on T³).

This is standard and mathematically correct.

### The Coulomb kernel trick

`coulombKernel r = if r ≤ 0 then 1 else r^(-3:ℝ)`. The value at r ≤ 0 is irrelevant because `innerLandauMatrix 0 = 0` (the projection vanishes at z = 0). Setting coulombKernel = 1 at r ≤ 0 ensures `∀ r, 0 < Ψ r`. This is correct and honest — the singularity is encoded in the integrability sorry's, not hidden.

I found no substantive mathematical error.

---

## 6. Code Quality

### `set_option linter.all false` in every file

All 21 .lean files disable all linters. Linters catch real bugs: unused variables, unreachable tactics, deprecated API. Disabling them everywhere signals the code was written to compile, not to be audited.

### maxHeartbeats above 800000

27 instances across 10 files:

| Value | Count | Risk |
|-------|-------|------|
| 4000000 (20x default) | 1 | **Severe** — VelocityDecayInstance.lean:1002 |
| 3200000 (16x default) | 3 | High — NewtonianPotential, CoulombFlux, CoulombPSD |
| 1600000 (8x default) | 10 | Moderate |
| 800000 (4x default) | 13 | Acceptable |

The 4M heartbeat proof is fragile and will break under Lean/Mathlib version updates.

### Files over 600 lines

| File | Lines | Issue |
|------|-------|-------|
| VelocityDecayInstance.lean | 2019 | Should be split into 3+ files |
| Section3.lean | 1308 | Monolithic H-theorem chain |
| TorusInstance.lean | 1223 | 23 axiom proofs |
| Defs.lean | 782 | Acceptable |
| CoulombSpatialTransport.lean | 662 | Borderline |
| LandauMatrixDerivBound.lean | 648 | Mostly machine-generated |
| CoulombFlux.lean | 609 | Borderline |

### Aristotle-generated proofs are unmaintainable

Many proofs are single-line semicolon-chained tactic scripts. `LandauMatrixDerivBound.lean` starts with a 200-line custom tactic re-implementation from Harmonic's fork. This is technical debt.

### Duplicate definitions

CoulombFlux.lean and CoulombPSD.lean define primed versions of core definitions (`normSq'`, `eucNorm'`, `landauMatrix'`, etc.) that are definitionally equal to the originals. These exist for "standalone Aristotle proofs" and are namespace pollution.

---

## 7. Documentation Discrepancies

| Claim (MEMORY.md) | Reality | Status |
|---|---|---|
| "CoulombConcreteTheorem42.lean (201 lines)" | 271 lines | **STALE** |
| "main theorem, 6 sorry's" | 3 sorry's | **STALE** |
| "CoulombFlux.lean (441 lines)" | 609 lines | **STALE** |
| "CoulombPSD.lean (170 lines)" | 405 lines | **STALE** |
| Ampère hypothesis labeled "(10)" | Should be "(11)" | Numbering error |

---

## Verdict: REVISE (improving)

### This formalization does NOT yet merit acceptance, but is approaching it.

**Grounds:**

1. **3 sorry's remain in the main theorem.** These represent Fubini integrability, flux differentiability, and IBP integrability for the Coulomb singular kernel. Without these, the entropy dissipation formula is not fully established.

2. **No complete satisfiability witness for Coulomb.** 15 of 18 VelocityDecayConditions fields are proved (up from 13), but 3 remain sorry'd. The theorem could in principle have vacuously true hypotheses for Coulomb (unlikely, but unverified).

3. **Universal linter suppression.** `set_option linter.all false` in all 21 files.

4. **Stale documentation.** Line counts and sorry counts in MEMORY.md do not match reality.

### Conditions for acceptance

1. Discharge all 3 sorry's, OR provide detailed mathematical proofs (with precise references) for each sorry'd statement.

2. Correct all documentation discrepancies.

3. (Stretch) Re-enable linters in top-level files. Split VelocityDecayInstance.lean.

### Progress since last critique

- hPSD_inner_int: **PROVED** (was sorry)
- hPSD_outer_int: **PROVED** (was sorry)
- Total sorry's: 5 → 3 (40% reduction)
- VelocityDecayConditions completeness: 72% → 82%

The formalization is making steady progress on the hard analytical lemmas.
