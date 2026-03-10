# Smoothness Audit: C^∞ → C^k

## Question
What is the minimum regularity needed for the main theorem? Currently all smoothness
hypotheses use `ContDiff ℝ ⊤` (C^∞). Can we weaken to `ContDiff ℝ n` for finite n?

## Analysis

### Critical path: D=0 → Maxwellian (Section3Helpers.lean)

The bottleneck is `parallel_curl_free_affine` (line 396), which proves:
if g : ℝ³ → ℝ³ is smooth and g(v)-g(w) ∥ v-w for all v ≠ w, then g is affine.

This lemma uses:
1. **First derivatives** (C¹): `fderiv ℝ g v` exists, `g` is differentiable
2. **Second derivative symmetry** (C²): `ContDiffAt.isSymmSndFDerivAt` at line 441
   requires `ContDiff ℝ n` with `2 ≤ n` (actually uses `n = ⊤` currently)
3. **Differentiability of fderiv components** (C²): `ContDiff.fderiv` to get
   `ContDiff ℝ (n-1)` on fderiv, then `fun_prop` for component extraction
4. **Constancy from zero derivative** (C¹ on c): `is_const_of_fderiv_eq_zero`
   needs `Differentiable ℝ c`, derived from smoothness of fderiv components

**Conclusion for g**: C² suffices for `parallel_curl_free_affine`.

### Chain back to f

The argument calls `parallel_curl_free_affine` on g = vGrad(log ∘ f):
- vGrad takes one derivative: g C² ← log∘f C³
- log preserves regularity for f > 0: log∘f C³ ← f C³

**Conclusion for f (velocity)**: C³ suffices.

### Spatial regularity

The spatial hypotheses (`hf_smooth_x`, `hB_smooth`) are used for:
- `IsSpatiallyDiff` closure properties (grad, div, curl)
- Gauss/Ampère/divB equation manipulations
- Maximum principle arguments (Section7)

These use at most first spatial derivatives. **C¹ suffices for spatial smoothness.**
But `IsSpatiallyDiff` in TorusInstance is defined as `ContDiff ℝ ⊤ (periodicLift f)`,
so weakening spatial regularity also requires changing the typeclass.

### Other uses

- `CoulombFlux.lean`: uses `ContDiff ℝ ⊤ f` for `Differentiable` and `Continuous`.
  C¹ suffices.
- `CoulombFluxDiff.lean`: uses smoothness for `hasFDerivAt_integral_of_dominated_of_fderiv_le`.
  Needs C¹ on the integrand w.r.t. parameters. C¹ suffices.
- `CoulombPSD.lean`: uses smoothness for continuity of PSD integrand. C¹ suffices for
  the inner terms, but `psd_integrand_continuous` chains through vGrad and log.
  Needs log∘f C¹, so f C¹.
- `SchwartzDecayDefs.lean`: uses `ContDiff ℝ ⊤` just for `Differentiable` extraction.
  C¹ suffices.

## Summary

| Hypothesis | Current | Minimum needed |
|-----------|---------|---------------|
| `hf_smooth_v : ∀ x, ContDiff ℝ ⊤ (f x)` | C^∞ | **C³** |
| `hf_smooth_x : ∀ v, ContDiff ℝ ⊤ (periodicLift ...)` | C^∞ | **C¹** |
| `hB_smooth : ∀ i, ContDiff ℝ ⊤ (periodicLift ...)` | C^∞ | **C¹** |

## Implementation difficulty

- **~80 occurrences** of `ContDiff ℝ ⊤` across 15 files
- Internal lemmas in Section3Helpers need regularity threading (C^k in → C^(k-1) out)
- `analysis_vGrad_smooth` currently returns C^∞; must return C^(n-1) instead
- `IsSpatiallyDiff` in `FlatTorus3` typeclass must be parameterized by smoothness level
- `TorusInstance.lean` proofs need updating for finite smoothness
- **Effort: High (multi-cycle, ~3-5 cycles)**

## Recommendation

This is feasible but large. Start with the velocity regularity (C^∞ → C³) since it
affects only the abstract chain, not the typeclass. Leave spatial regularity for later.

The cleanest approach: introduce a universe-polymorphic smoothness parameter in the
abstract theorem, specialize to ⊤ for the concrete theorem (preserving backwards
compatibility), then gradually lower it.
