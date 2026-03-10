# Adversarial Critique: Coulomb Concrete Theorem 42

**Reviewer posture:** Hostile. Default verdict is REJECT. The formalization must earn approval through evidence.

**Reviewed:** Full codebase at `Aristotle/Landau/main/` (21 .lean files, 11,423 total lines)
**Main theorem:** `CoulombConcreteTheorem42` in `CoulombConcreteTheorem42.lean` (280 lines)
**Date:** 2026-03-11 (fresh analysis, supersedes all prior reviews)

**Claim:** Any sufficiently smooth, positive, Schwartz-class steady-state solution of the Vlasov-Maxwell-Landau system with Coulomb collisions on T^3 is a global Maxwellian equilibrium with E = 0 and B = const.

---

## 1. Sorry Count: ZERO

**There are 0 sorry tokens in the codebase.** Every lemma has a complete proof body. The formalization is fully verified by the Lean 4 kernel (Mathlib v4.24.0).

### Correction from previous critique

The previous critique identified 2 sorry's: `coulomb_entry_conv_differentiable` and `coulomb_entry_conv_deriv_decay`. Both have been resolved:

1. **`coulomb_entry_conv_differentiable`** — PROVED. The proof was refactored into a core `coulomb_entry_conv_hasFDerivAt_aux` lemma (HasFDerivAt via `hasFDerivAt_integral_of_dominated_of_fderiv_le` with uniform bound ‖u‖⁻¹ * Cf as dominator) and a corollary extracting differentiability.

2. **`coulomb_entry_conv_deriv_decay`** — DISCOVERED FALSE, REPLACED, PROVED. The original statement claimed Schwartz decay of the convolution derivative. This is mathematically false: the Coulomb kernel A(z) is degree -1 homogeneous, so the convolution `A * g` decays like ‖v‖⁻¹ and its derivative like ‖v‖⁻², not Schwartz. The statement was replaced with `coulomb_entry_conv_deriv_bounded` (uniform bound ∃ C, ∀ v, ‖fderiv(conv)(v)‖ ≤ C), which IS true and was proved using the HasFDerivAt representation + `newtonian_schwartz_uniform_bound`. The proof of `coulomb_flux_deriv_schwartz_decay` was refactored to use (Schwartz coefficient × bounded convolution derivative) instead of (bounded coefficient × Schwartz convolution derivative).

---

## 2. VelocityDecayConditions: All 18 Fields Proved

All 18 fields of `VelocityDecayConditions` are fully instantiated in `CoulombConcreteTheorem42.lean:158-274` with complete proof bodies:

| Field | Status |
|-------|--------|
| `hPSD_inner_int` | PROVED |
| `hPSD_outer_int` | PROVED |
| `hFubini_double` | PROVED |
| `hFubini_inner` | PROVED |
| `hFubini_outer` | PROVED |
| `hSpatialTransport_int` | PROVED |
| `hForceTransport_int` | PROVED |
| `hLandauFluxDiff` | PROVED |
| `hLandauIBP_df_g` | PROVED |
| `hLandauIBP_f_dg` | PROVED |
| `hLandauIBP_fg` | PROVED |
| `hLandauFluxInt` | PROVED |
| `hForceIBP_f_dg` | PROVED |
| `hForceIBP_fg` | PROVED |
| `hSpatialTransport_joint` | PROVED |
| `hSpatTransComp` | PROVED |
| `hf_velocity_dominated` | PROVED |
| `hPSD_cont` | PROVED |
| `hD_cont` | PROVED |

**Completeness: 18/18 = 100%.**

---

## 3. FlatTorus3: All 29 Fields Proved

The `FlatTorus3` typeclass (Defs.lean:325-417) is fully instantiated for `Torus3 = Fin 3 → AddCircle 1` in `TorusInstance.lean` (1,223 lines) with 0 sorry's. All 29 fields (3 instances, 3 operators, 1 predicate, 22 property axioms) are proved from Mathlib primitives.

### Remaining concern: `hGradScalarMul` lacks `IsSpatiallyDiff` guard

The axiom `hGradScalarMul` states `gradX (c * f) = c * gradX f` without requiring `IsSpatiallyDiff f`. On the concrete torus this holds vacuously (fderiv of non-differentiable function = 0), but a different instantiation might not have this property. Minor design issue; does not affect soundness.

### Remaining concern: `IsSpatiallyDiff` overshoot

On the concrete torus, `IsSpatiallyDiff` is `ContDiff R top` (smooth). The abstract proof only needs C^2 regularity. This narrows the class of functions covered by the theorem. Not a soundness issue.

---

## 4. Circularity and Hypothesis Scrutiny

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
                 <- CoulombPSD.lean [0 sorry's]
                    <- CoulombConcreteTheorem42.lean (main theorem)
```

**No cycles.** The flow is strictly: definitions → abstract algebra → analysis → abstract theorem → concrete instance → Coulomb specialization.

### Is any hypothesis restating the conclusion?

The 13 hypotheses of `CoulombConcreteTheorem42` are:
1. `hnu : 0 < nu` — physical parameter
2. `hrho_ion : 0 < rho_ion` — physical parameter
3. `hf_pos : forall x v, 0 < f x v` — positivity
4-6. Smoothness of f and B
7. `hSchwartz : UniformSchwartzDecay f` — Schwartz decay in v, uniform in x
8. `hExpDecay` — stretched-exponential lower bound
9. `hGradBound` — polynomial score bound
10-13. Four VML equations (Vlasov, Ampere, Gauss, div B = 0)

**None restates the conclusion.** The polynomial score bound (hypothesis 9) is the most restrictive but is satisfied by any Maxwellian, stretched-Gaussian, or function with polynomial logarithmic gradient growth.

### `UniformSchwartzDecay` scrutiny

`UniformSchwartzDecay` has two fields:
- `hDecay`: all iterated velocity derivatives decay faster than any polynomial, uniformly in x
- `hGradDecay`: spatial gradient components of f also have Schwartz velocity decay

Both are genuine analytical regularity conditions. For a steady-state solution of Vlasov with smooth coefficients, they follow from standard regularity theory (bootstrap argument), but formalizing this is far beyond scope. Treating them as hypotheses is honest.

### `coulombKernel_pos` and kernel extension

The Coulomb kernel is defined as `if r ≤ 0 then 1 else r^(-3)`. The positivity `∀ r, 0 < coulombKernel r` is a convenience for the abstract PSD argument. The value at r ≤ 0 never affects the Landau operator (since `landauMatrix Psi 0 = 0`). Sound.

---

## 5. Satisfiability Witnesses

`VelocityDecayInstance.lean` (2,019 lines) provides two witnesses:
1. `schwartzDecayConditions`: uniform isotropic Maxwellian with E = 0, B = 0
2. `schwartzDecayConditionsEB`: uniform isotropic Maxwellian with nonzero constant E, B

Both have all 18 fields proved with 0 sorry's. These demonstrate the hypotheses are non-vacuous.

---

## 6. Physical Limitations

- **Dimension:** Hardcoded to 3D (physically necessary for Lorentz force cross product)
- **Kernel:** Coulomb (Ψ(r) = r⁻³) only. Moderately soft potentials (-3 < γ < 0) not covered.
- **Spatial domain:** T³ = (ℝ/ℤ)³ (periodic, eliminates boundary terms)
- **Steady state:** f, E, B time-independent. This is a characterization theorem, not stability.
- **Positivity:** Strict positivity `∀ x v, 0 < f x v` everywhere (not a.e.)
- **Smoothness overshoot:** C^∞ required when C^2 would suffice mathematically

---

## 7. Code Quality

### File sizes

| File | Lines | Assessment |
|------|-------|------------|
| VelocityDecayInstance.lean | ~1,970 | **Too large.** Copy-paste in `schwartzDecayConditionsEB` fixed (cycle 25). |
| CoulombPSD.lean | 1,325 | **Large.** Five logically distinct topics in one file. |
| Section3.lean | 1,308 | **Too large.** H-theorem + Gaussian integrals + gap lemmas. |
| TorusInstance.lean | 1,223 | Acceptable for a single typeclass instance. |
| Defs.lean | 782 | Acceptable for definitions. |
| CoulombSpatialTransport.lean | 662 | Borderline. |
| LandauMatrixDerivBound.lean | 648 | Contains 232 lines of custom `generalize_proofs'` tactic. |
| CoulombFlux.lean | 609 | Borderline. |

### Heartbeat overrides

~33 `maxHeartbeats` overrides across 11 files:

| Value | Count | Severity |
|-------|-------|----------|
| 4,000,000 (20x default) | 1 | **Fragile** |
| 3,200,000 (16x default) | 5 | High |
| 1,600,000 (8x default) | 11 | Moderate |
| 800,000 (4x default) | ~15 | Acceptable individually |

### ~~Universal linter suppression~~ FIXED

~~`set_option linter.all false` in all 21 files.~~ All linter suppressions removed in cycle 26. The project builds with 0 linter warnings.

### Duplicate primed definitions

`landauMatrix'` resolves to different definitions in different namespaces (VML vs. top-level). `normSq'`, `eucNorm'`, `innerLandauMatrix'` are duplicated across CoulombFlux.lean and LandauMatrixDerivBound.lean.

### Custom tactic code

232 lines of Aristotle's `generalize_proofs'` reimplementation in LandauMatrixDerivBound.lean. Not relevant to mathematical content but a maintenance burden.

### MEMORY.md discrepancies

| Claim in MEMORY.md | Reality | Status |
|----|---------|--------|
| "CoulombConcreteTheorem42.lean (201 lines) — main theorem, 6 sorry's" | 280 lines, 0 sorry's | **STALE** |
| "CoulombFlux.lean (441 lines)" | 609 lines | **STALE** |
| "CoulombPSD.lean (170 lines)" | 1,325 lines | **STALE** |

---

## 8. Sorry Count Trajectory

| Version | Sorry tokens | VDC completeness |
|---------|-------------|-----------------|
| Initial | Many | ~50% |
| Cycle 20 | 4 | 16/18 = 89% |
| Cycle 22 | 3 | 16/18 = 89% |
| Cycle 23 | 2 | 16/18 = 89% |
| **Cycle 24** | **0** | **18/18 = 100%** |

---

## 9. Overall Assessment

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
| CoulombPSD | 1 | 1,325 | 0 | Fully verified |
| CoulombConcreteTheorem42 | 1 | 280 | 0 | Fully verified |
| **TOTAL** | **21** | **11,423** | **0** | **Fully verified** |

### What is proved

1. **The entire abstract proof chain is complete** (Sections 2-9 + Theorem42).
2. **The FlatTorus3 typeclass has a complete concrete instance** (all 29 fields).
3. **All 18 VelocityDecayConditions fields are proved for Coulomb.**
4. **The smooth-kernel theorem is fully complete.**
5. **The Coulomb Concrete Theorem 42 is fully proved** — 0 sorry's in the entire dependency chain.

### Structural concerns (non-blocking)

1. **~33 heartbeat overrides**, including one at 20x default
2. ~~Universal linter suppression across all 21 files~~ **FIXED** (cycle 26: all linters re-enabled, 0 warnings)
3. **Duplicate primed definitions** with namespace collision
4. **232 lines of custom tactic code** (Aristotle's `generalize_proofs'`)
5. **3 files exceed 1100 lines** (should be split)
6. ~~87 lines of copy-paste in `schwartzDecayConditionsEB`~~ **FIXED** (cycle 25: `let base` refactoring)
7. **Stale MEMORY.md** (wrong line counts and sorry counts)
8. **C^∞ overshoot** in IsSpatiallyDiff when C^2 would suffice
9. **`import Mathlib`** in 2 files instead of granular imports

### Verdict: ACCEPT

The formalization is **complete**. Every lemma in the 11,423-line codebase has a machine-checked proof. The 13 hypotheses of the main theorem are genuine analytical conditions that do not encode the conclusion. Two satisfiability witnesses confirm non-vacuity.

The structural concerns above are code quality issues, not soundness issues. They do not affect the validity of the proof.

**Remaining work (optional):**
1. Update MEMORY.md with correct line counts and sorry counts
2. ~~Re-enable linters in top-level theorem files~~ **DONE** (all 21 files)
3. Split VelocityDecayInstance.lean, Section3.lean, CoulombPSD.lean
4. ~~Replace copy-paste in `schwartzDecayConditionsEB` with `let`-binding~~ **DONE**
5. Reduce the 4M-heartbeat proof
6. Consolidate primed definitions
