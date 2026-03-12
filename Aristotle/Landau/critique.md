# Adversarial Critique: VML Steady State Formalization

**Timestamp**: 2026-03-12 (Cycle Babysit)

## 0. CI status
- **Result**: REVISE (P1 issue).
- The `Build and Deploy Documentation` CI workflow is **failing** on the `landau` branch.
- Moreover, `curl -Is https://vilin97.github.io/aristotle/blueprint/` returns HTTP 404. The docs are definitively broken. This must be fixed immediately.
- `lake build` locally passes with 0 errors but a significant number of linter warnings (e.g. `ring_nf` instead of `ring`, unused variables, unused simp arguments, lines over 100 characters). This code is not perfectly clean.

## 1. Sorry's
- **Result**: I found no issue. 
- A full search of the repository reveals **0 sorry's** remaining in the source code.

## 2. Hidden axioms
- **Result**: I found no issue.
- `lean_verify` and axiom printing on `VML.CoulombConcreteTheorem42` and `VML.CoulombConcreteTheorem42_classify_T` reveal only standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`). No hidden `sorryAx` or `native_decide` cheating is present in the final assembly.

## 3. Circularity
- **Result**: I found no issue.
- Tracing the dependency chain reveals no circularities. The conclusion (that `f` is a Maxwellian parameterized by $T$ and $B_0$) is not assumed anywhere in the typeclasses, and the `VelocityDecayConditions` do not secretly assume equilibrium. The `CoulombNonvacuous` proves that an equilibrium state *satisfies* the hypotheses, which correctly establishes non-vacuousness rather than circularity.

## 4. Hypothesis audit
- **Result**: REVISE.
- The `CoulombConcreteTheorem42` demands explicit `hGradBound` (bound on `fderiv f`) and `hLogGrowth` (two-sided polynomial bound on $\log f$). While independence is argued in the file, requiring *both* is physically overly-restrictive for general steady states. Bounding $\log f$ from below means $f$ cannot decay faster than an exponential, which is fine for Maxwellians but mathematically heavy-handed as an input hypothesis. Could we weaken this to just a bound on $|\nabla_v \log f(v)| \le C(1+\|v\|)^k$?

## 5. Mathematical correctness
- **Result**: I found no issue.
- The definitions and proof steps align with the standard mathematical treatment of the VML system. The singularity of the Coulomb kernel is handled appropriately by showing that the score difference $\nabla \log f(v) - \nabla \log f(w) = O(|v-w|)$ cancels the $1/|v-w|$ blowup, leading to proper PSD integrability.

## 6. Code quality
- **Result**: REVISE.
- `Section3Helpers.lean` is over 600 lines (621 lines), violating the strict file size limits. It needs to be split.
- The build produces dozens of linter warnings:
  - `ring` tactic failures recommending `ring_nf` in `GaussianHelpers.lean` and `Section3Helpers.lean`.
  - Unused variables and `simp` arguments in `Section3.lean` and `SchwartzDecayDefs.lean`.
  - Rampant long lines (>100 characters) across almost all files.
  - Abusive use of `show` to change the goal instead of `change` (e.g. in `Theorem42.lean`, `TorusInstance.lean`).

## 7. Documentation lies
- **Result**: I found no issue.
- The documentation claims 0 sorry's and correctly lists the axioms. The README accurately reflects the final state of the `main/` proofs.

## 8. Generalization opportunities
- **Result**: REVISE. 
This proof is too tightly coupled to its specific assumptions. Three concrete paths:
1. **Weaken Score Bounds:** Drop the explicit lower bound on $\log f$ (`hLogGrowth`) in favor of an integrated Fisher information bound or a pointwise score bound $|\nabla \log f|$.
2. **Beyond the Torus:** The flat torus $T^3$ avoids boundary conditions entirely. Generalizing to domains with boundary (e.g. bounded domain in $\mathbb{R}^3$ with specular reflection) would be significantly more physically relevant.
3. **General Soft Potentials:** The entire proof chain is specialized to $\Psi(r) = r^{-3}$ (Coulomb). The abstract theorem handles bounded kernels, but the intermediate case (moderately soft potentials $\Psi(r) = r^{-\gamma}$ for $\gamma < 3$) should be achievable with exactly the same methods.

## 9. Mathlib upstreamability
- **Result**: REVISE.
- Almost none of this is PR'd to Mathlib.
- `FlatTorus3` definitions and properties (integration on quotient spaces, periodic functions) are mathematically general and should be contributed to Mathlib's geometry/topology library.
- `GaussianHelpers.lean` contains completely generic estimates for multivariate Gaussians and iterated derivatives of $e^{-\|v\|^2}$ that have no physical dependencies.

## Verdict
**REVISE**

The mathematics is solid, but the project is failing CI due to broken documentation (HTTP 404), has bloated files (`Section3Helpers.lean`), is riddled with linter warnings, and leaves obvious generalizations on the table.

Conditions for acceptance:
1. Fix the `Build and Deploy Documentation` CI and ensure `blueprint/` returns HTTP 200.
2. Clean up code quality warnings (fix `ring` -> `ring_nf`, remove unused `simp` arguments, change `show` to `change` where appropriate).
3. Split `Section3Helpers.lean` to be strictly under 600 lines.
4. Extricate `GaussianHelpers.lean` and `TorusDefs.lean` so they are fully independent of physics contexts for future Mathlib PRs.