# Experiment: Weaken UniformSchwartzDecay (Issue 8g)

## Status: IMPLEMENTED (cycle 89) — hDecay now requires k ≤ 2 only

## Current condition

```lean
structure UniformSchwartzDecay (f : Torus3 → (Fin 3 → ℝ) → ℝ) : Prop where
  hDecay : ∀ (N k : ℕ), ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    ‖iteratedFDeriv ℝ k (f x) v‖ * (1 + ‖v‖) ^ N ≤ C
  hGradDecay : ∀ (N : ℕ) (i : Fin 3), ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    |torusGradX (fun y => f y v) x i| * (1 + ‖v‖) ^ N ≤ C
```

This says: ALL velocity derivatives of f decay faster than ANY polynomial. This is the
Schwartz class condition.

## What the proof actually uses

### hDecay usage (grep of `hSchwartz.hDecay` and `hf_schwartz`):

| Call site | File | N | k | Purpose |
|-----------|------|---|---|---------|
| `hDecay 0 0` | CoulombKernel:42 | 0 | 0 | Upper bound on f |
| `hDecay 4 0` | CoulombConcreteTheorem42:231 | 4 | 0 | Velocity domination |
| `hDecay (k+4) 0` | CoulombKernel:96 | variable | 0 | Moment integrability |
| `hDecay (M+4) 0` | SchwartzDecayDefs:78 | variable | 0 | Polynomial weight integrability |
| `hDecay N 0` | CoulombFlux:205 | variable | 0 | Newtonian potential input |
| `hDecay (K_log+4) 0` | CoulombFlux:228 | variable | 0 | Flux component bound |
| `hDecay N 1` | CoulombFlux:112 | variable | 1 | Partial derivative decay |
| `hDecay (K_log+4) 1` | CoulombFlux:229 | variable | 1 | Flux derivative bound |
| `hDecay (K_log+6) 1` | CoulombSpatialTransport:140 | variable | 1 | Spatial transport |
| `hf_schwartz N 0` | CoulombPSD, CoulombFluxDiff | variable | 0 | Per-x specialization |
| `hf_schwartz N 1` | CoulombFlux:49, CoulombPSD:326 | variable | 1 | Per-x derivative decay |
| `hf_schwartz N (k+1)` | CoulombFluxDiff:31 | variable | k+1 | schwartz_fderiv_component_schwartz |

### Maximum k values reached

- `schwartz_fderiv_component_schwartz` (CoulombFluxDiff:31): accesses `hf_schwartz N (k+1)`
  - Called with outer k=0 → accesses k=1
  - Called with outer k=1 (CoulombFluxDiff:478) → accesses **k=2**
  - Never called with outer k ≥ 2

**Maximum k used: 2** (second velocity derivatives).

### hGradDecay usage

Used in `CoulombSpatialTransport.lean` for spatial transport integrability. The N values
are variable but k is always implicit (it's a spatial derivative, not velocity).

## Proposed weaker condition

```lean
/-- Weaker than UniformSchwartzDecay: only requires f, ∇f, ∇²f to have
    super-polynomial decay in velocity. Higher derivatives may grow polynomially. -/
structure UniformC2Decay (f : Torus3 → (Fin 3 → ℝ) → ℝ) : Prop where
  hDecay : ∀ (N : ℕ) (k : Fin 3),  -- k ∈ {0, 1, 2}
    ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    ‖iteratedFDeriv ℝ k (f x) v‖ * (1 + ‖v‖) ^ N ≤ C
  hGradDecay : ∀ (N : ℕ) (i : Fin 3), ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    |torusGradX (fun y => f y v) x i| * (1 + ‖v‖) ^ N ≤ C
```

Or equivalently using `k ≤ 2` instead of `Fin 3`:

```lean
structure UniformC2Decay (f : Torus3 → (Fin 3 → ℝ) → ℝ) : Prop where
  hDecay : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 →
    ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    ‖iteratedFDeriv ℝ k (f x) v‖ * (1 + ‖v‖) ^ N ≤ C
  hGradDecay : ∀ (N : ℕ) (i : Fin 3), ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    |torusGradX (fun y => f y v) x i| * (1 + ‖v‖) ^ N ≤ C
```

## Impact assessment

### What changes
- `UniformSchwartzDecay` → `UniformC2Decay` in the concrete theorem statement
- All call sites that pass `hDecay N k` need to additionally prove `k ≤ 2`
- The concrete theorem would apply to distributions that are C² in velocity with
  rapid decay, even if higher derivatives grow (e.g., solutions of Boltzmann equation
  that are C² but not C^∞)

### What stays the same
- hGradDecay is unchanged
- All helper lemmas (integrable, integrable_poly_mul, etc.) only use k=0
- The abstract Theorem42 doesn't reference decay directly (it uses VelocityDecayConditions)

### Refactoring effort
- ~10 files need the type signature updated
- Most changes are mechanical: add `(by norm_num : k ≤ 2)` to hDecay calls
- `schwartz_fderiv_component_schwartz` needs its signature updated
- The main theorem's `ContDiff ℝ ⊤` could also be weakened to `ContDiff ℝ 2`

### Physical significance
Schwartz class is standard in kinetic theory (Desvillettes-Villani, Guo). However,
the proof doesn't use the full Schwartz machinery — it only needs controlled
behavior up to second derivatives. A C² function with rapid decay (not necessarily
Schwartz) is a strictly larger class. For example:
- Piecewise-smooth distributions with exponential tails
- Solutions of truncated moment systems
- Distributions with mild regularity loss at high energies

## Decision

**Recommended: DEFER to a dedicated cycle.** The change is mechanical (~10 files, ~30 edits)
but needs careful verification. It's a genuine mathematical improvement (strictly weaker
hypothesis) with clear physical motivation. The risk is low (mostly type signature changes)
but the blast radius is high (touches many files).

Priority: Medium. Should be done before weakening regularity C^∞ → C^2 (issue 8b)
since both changes affect the same files and should be coordinated.
