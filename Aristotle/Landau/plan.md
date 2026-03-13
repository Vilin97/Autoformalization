# Plan -- Cycle 122 (Adversarial Focus)

## Status summary

- **Sorry count**: 0
- **Files**: 32 files
- **Build**: Local build passing (with style linter warnings)
- **Critique verdict**: REVISE
- **Open issues**:
  - **P1**: Code quality: `NewtonianPotential.lean` uses `set_option maxHeartbeats 800000`.
  - **P1**: Code quality: `Section3Helpers.lean` exceeds 600 lines (621 lines).
  - **P2**: Code quality: Dozens of style linter warnings (`linter.style.longLine`).
  - **P2**: Epistemic/Documentation: `hGradBound` forces a lower bound on decay, making it overly restrictive compared to what the docs claim for Schwartz class.
  - **P3**: Mathlib upstreamability: `GaussianHelpers.lean`, `TorusDefs.lean`, and `inv_norm_local_integrable`.

## Active multi-cycle strategies

### Purge `VelocityDecayConditions` of analytical consequences
- This requires structurally breaking down `Theorem42` to accept base integrability bounds and prove the Fubini/continuity theorems internally, likely requiring thousands of lines of new analysis. Will require careful staging across multiple cycles.

### Generalize beyond Torus and Coulomb Kernel
- Generalize to domains with boundaries (e.g. bounded domain with specular reflection) and moderately soft potentials ($\gamma < 3$).

## This cycle's work items

### 1. Fix `maxHeartbeats` in `NewtonianPotential.lean` (`/simplify`)
- **What**: Reduce the 800,000 heartbeats required for `inv_norm_local_integrable`.
- **Files**: `NewtonianPotential.lean`
- **Approach**: Break the proof of `inv_norm_local_integrable` into smaller sub-lemmas.
- **START IMMEDIATELY.**

### 2. Split `Section3Helpers.lean` (`/simplify`)
- **What**: File is 621 lines, which violates the <600 lines limit.
- **Files**: `Section3Helpers.lean`
- **Approach**: Move independent algebraic or analytic lemmas into a new file `Section3Helpers2.lean` or into `GaussianHelpers.lean` if appropriate.

### 3. Clean up Linter Warnings (`/simplify`)
- **What**: Resolve build warnings to improve code cleanliness (especially `linter.style.longLine`).
- **Files**: `FlatTorus3Lemmas.lean`, `Section4.lean`, `Section5.lean`, `Section7.lean`, `Section8.lean`, `VMLInputDerive.lean`, `Theorem42.lean`, `TorusIntegration.lean`, `TorusInstance.lean`, `CoulombSpatialTransport.lean`, `CoulombFlux.lean`, `CoulombFluxBound.lean`, `CoulombPSDHelpers.lean`, `CoulombPSD.lean`, `CoulombFluxConv.lean`, `CoulombFluxDiff.lean`, `LogBoundHelpers.lean`, `CoulombConcreteTheorem42.lean`.
- **Approach**: Break long lines, fix missing spaces, adjust command starts.

### 4. Correct Documentation for `hGradBound` (`/strengthen`)
- **What**: The docs claim Schwartz class or sub-Gaussian tails are sufficient, but `hGradBound` forces a lower bound that contradicts this.
- **Files**: `CoulombConcreteTheorem42.lean`
- **Approach**: Update the docstring to accurately reflect the restrictiveness of the polynomial lower bound assumption, or explicitly mention that this excludes standard Schwartz functions with faster-than-exponential decay.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| Mathlib upstreaming | P3 | Extricate `GaussianHelpers.lean` and `TorusDefs.lean`. |
| Document Non-Relativistic Limit | P4 | Document superluminal velocities in the VML formulation. |
