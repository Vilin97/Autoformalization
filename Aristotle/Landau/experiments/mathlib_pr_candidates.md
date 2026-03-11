# Mathlib PR Candidates

## 1. `iteratedFDeriv_clm_zero`

**Statement**: The iterated derivative of a continuous linear map vanishes at order >= 2.

```lean
lemma iteratedFDeriv_clm_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) (n : ℕ) (hn : 2 ≤ n) (x : E) :
    iteratedFDeriv 𝕜 n f x = 0
```

**Proof**: Uses `iteratedFDeriv_succ_eq_comp_right` + `fderiv` of a CLM is constant + `iteratedFDeriv_const_of_ne`.

**Mathlib location**: `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas` or `Mathlib.Analysis.Calculus.ContDiff.Basic`

**Related Mathlib lemmas**:
- `ContinuousLinearMap.iteratedFDeriv_eq` (exists but for different formulation)
- `iteratedFDeriv_const_of_ne` (used in proof)

## 2. `norm_iteratedFDeriv_one_clm`

**Statement**: The norm of the first iterated derivative of a CLM equals the operator norm.

```lean
lemma norm_iteratedFDeriv_one_clm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E →L[𝕜] F) (x : E) :
    ‖iteratedFDeriv 𝕜 1 f x‖ = ‖f‖
```

**Proof**: Unfold `iteratedFDeriv 1` via `iteratedFDeriv_succ_eq_comp_right`, simplify fderiv of CLM to constant, apply `LinearIsometryEquiv.norm_map`.

**Mathlib location**: Same file as above.

## Status

Both lemmas are:
- Fully generalized (arbitrary `NontriviallyNormedField`, arbitrary normed spaces)
- Self-contained (only depend on Mathlib, no project-specific definitions)
- Currently in `Aristotle/Landau/main/IteratedDerivHelpers.lean` (lines 22-40)
- Used in `norm_iteratedFDeriv_quad_bound` for Gaussian decay bounds

## Loogle search results (cycle 91)

- `iteratedFDeriv_clm_zero`: **Not in Mathlib.** Genuinely new. Good PR candidate.
- `norm_iteratedFDeriv_one_clm`: **Partially exists.** `norm_iteratedFDeriv_one` gives `‖iteratedFDeriv 𝕜 1 f x‖ = ‖fderiv 𝕜 f x‖`. For a CLM `f`, `fderiv 𝕜 ↑f x = f` by `ContinuousLinearMap.hasFDerivAt.fderiv`, so our lemma is a one-liner corollary. Still useful but lower priority for PR.

**Recommendation**: PR `iteratedFDeriv_clm_zero` to `Mathlib.Analysis.Calculus.ContDiff.Basic` or similar. The `norm_iteratedFDeriv_one_clm` version is a convenience lemma that could go in the same PR.
