# Plan -- Cycle 120 (Adversarial Focus)

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 10,203 lines
- **Build**: Local build passing
- **Critique verdict**: REVISE (Cycle 120 Hostile Review)
- **Open issues**: 
  - **P0**: Purge `VelocityDecayConditions` of tautological analytical consequences (e.g., Fubini swaps, continuity).
  - **P1**: Epistemic falsehood: Correct the "uniqueness" claims to "classification of steady states".
  - **P2**: Fake abstraction: `FlatTorus3` hides Hodge theory inside typeclass parameters.
  - **P3**: `UniformSchwartzDecay` is an overkill brute-force assumption.
  - **P3**: Non-relativistic framework lacks physical documentation.

## This cycle's work items

### 1. Correct "uniqueness" claims (`/strengthen`)
- **What**: Critique issue 2. The theorem classifies a family of steady states parameterized by $T_0$ and $B_0$, it does not uniquely determine the state without energy constraints.
- **Files**: `Theorem42.lean`, `CoulombConcreteTheorem42.lean`, `README.md`, `home_page/index.md`
- **Approach**: Replace the word "unique" with "classification" or "global Maxwellian". Rename `CoulombConcreteTheorem42_unique_T` if it is misleading, or document exactly what it means. Add documentation acknowledging the free parameters $T_0, B_0$.
- **START IMMEDIATELY.**

### 2. Document Non-Relativistic Limit (`/strengthen`)
- **What**: Critique issue 4. Document that the non-relativistic assumption with $v \in \mathbb{R}^3$ admits superluminal velocities.
- **Files**: `Theorem42.lean`, `CoulombConcreteTheorem42.lean`, `README.md`
- **Approach**: Add clear docstring disclaimers to the main theorem files explaining the physical inconsistency of the non-relativistic Vlasov-Maxwell formulation.

### 3. Simplify / Clean up Linter Warnings (`/simplify`)
- **What**: Carryover from previous cycle. Fix linter warnings in `Section3Helpers.lean` and `GaussianHelpers.lean`.
- **Files**: `Section3Helpers.lean`, `GaussianHelpers.lean`
- **Approach**: Remove unused `simp` arguments, prefix unused variables with `_`.

## Active multi-cycle strategies

### Purge `VelocityDecayConditions` of analytical consequences (P0)
- This requires structurally breaking down `Theorem42` to accept base integrability bounds and prove the Fubini/continuity theorems internally, likely requiring thousands of lines of new analysis. Will require careful staging across multiple cycles.

### Dissolve or justify `FlatTorus3` (P2)
- Re-evaluating the Riemannian geometry/Hodge theory axioms. Options: explicitly specialize the abstract theorem to $T^3$ or properly formalize Hodge theory on manifolds. 

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| Weaken `UniformSchwartzDecay` | Strengthen | Define `VelocityMomentBound k` instead of infinite decay. |
| 2 maxHeartbeats overrides | Code quality |  |
| Files over 500 lines | Code quality | |
