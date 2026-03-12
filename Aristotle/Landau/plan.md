# Plan -- Cycle 121 (Adversarial Focus)

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 10,221 lines
- **Build**: Local build passing (with linter warnings)
- **Critique verdict**: REVISE
- **Open issues**:
  - **P0**: `Build and Deploy Documentation` CI is failing, `blueprint/` returns HTTP 404.
  - **P1**: Code quality: `Section3Helpers.lean` exceeds 600 lines (621 lines).
  - **P2**: Code quality: Dozens of linter warnings (e.g. `ring_nf` instead of `ring`, unused variables, unused simp args, long lines).
  - **P2**: Epistemic: `hLogGrowth` in `CoulombConcreteTheorem42` demands explicit lower bounds on $\log f$, which is overly restrictive.
  - **P3**: Mathlib upstreamability: `GaussianHelpers.lean` and `TorusDefs.lean` are generic and should be prepped for Mathlib.

## Active multi-cycle strategies

### Purge `VelocityDecayConditions` of analytical consequences
- This requires structurally breaking down `Theorem42` to accept base integrability bounds and prove the Fubini/continuity theorems internally, likely requiring thousands of lines of new analysis. Will require careful staging across multiple cycles.

### Generalize beyond Torus and Coulomb Kernel
- Generalize to domains with boundaries (e.g. bounded domain with specular reflection) and moderately soft potentials ($\gamma < 3$).

## This cycle's work items

### 1. Fix Documentation CI (`/simplify` / `/cleanup`)
- **What**: The blueprint deployment CI is failing and returning 404.
- **Files**: `.github/workflows/deploy.yml` or docgen configurations.
- **Approach**: Investigate the exact failure in the GH Actions logs for the doc build, and fix the pathing or python environment issues causing it.
- **START IMMEDIATELY.**

### 2. Clean up Linter Warnings (`/simplify`)
- **What**: Resolve build warnings to improve code cleanliness.
- **Files**: `GaussianHelpers.lean`, `Section3Helpers.lean`, `Section3.lean`, `SchwartzDecayDefs.lean`, `Theorem42.lean`, `TorusInstance.lean`
- **Approach**: Replace `ring` with `ring_nf`, drop unused `simp` arguments, replace `show` with `change` where the goal state changes.

### 3. Split `Section3Helpers.lean` (`/simplify`)
- **What**: File is 621 lines, which violates the <600 lines limit.
- **Files**: `Section3Helpers.lean`
- **Approach**: Move independent algebraic or analytic lemmas into a new file `Section3Helpers2.lean` or into `GaussianHelpers.lean` if appropriate.

### 4. Investigate `hLogGrowth` Weakening (`/strengthen`)
- **What**: The hypothesis restricts the steady state solutions excessively.
- **Files**: `CoulombConcreteTheorem42.lean`, `Theorem42.lean`
- **Approach**: See if `hLogGrowth` can be replaced with a gradient bound $|\nabla_v \log f(v)| \le C(1+\|v\|)^k$.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| Mathlib upstreaming | P3 | Extricate `GaussianHelpers.lean` and `TorusDefs.lean`. |
| Document Non-Relativistic Limit | P4 | Document superluminal velocities in the VML formulation. |
