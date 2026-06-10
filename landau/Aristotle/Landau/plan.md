# Plan -- Cycle 123

## Status summary

- **Sorry count**: 0
- **Files**: 34 files in `main/`
- **Build**: Passing, 0 errors, 47 linter warnings
- **Critique verdict**: CONDITIONAL ACCEPT
- **Key wins since last cycle**: `maxHeartbeats 800000` in NewtonianPotential.lean fixed; Section3Helpers.lean split (now 493 lines, under 600 limit); hGradBound docstring updated with restrictiveness warning.

## Open issues from critique

| Priority | Issue | Source |
|----------|-------|--------|
| P1 | MEMORY.md has false claims (Section9.lean, VelocityDecayInstance instances, nonvacuous sorry count) | critique §7 |
| P1 | `hLogGrowth` ghost reference in CoulombConcreteTheorem42.lean docstring line 84 | critique §7 |
| P2 | Hypothesis numbering gap (missing #8) in CoulombConcreteTheorem42.lean docstring | critique §7 |
| P2 | 5-linter suppressions in GaussianHelpers.lean and Section3Helpers.lean | critique §6 |
| P2 | `maxHeartbeats 400000` in TorusIntegration.lean:89 | critique §6 |
| P2 | `Section3Helpers2.lean` has 3 multiGoal warnings at lines 72-74 | critique §6 |
| P3 | 17 files suppress `linter.style.longLine` globally | critique §6 |
| P3 | Rename `UniformSchwartzDecay` to reflect actual k≤2 scope | critique §4 |
| P3 | Add bounded-kernel instance (Ψ = const) to show hGradBound is Coulomb-specific | critique §8 |

## Active multi-cycle strategies

### Documentation accuracy
- MEMORY.md is severely outdated. Must be reconciled with actual codebase. This is a P1 blocking issue.

### Code quality hygiene
- Systematically remove linter suppressions by fixing underlying issues. 17 files suppress longLine; 2 files suppress 5 linters each.

## This cycle's work items

### 1. Fix documentation lies (`/simplify`)
- **What**: Fix the `hLogGrowth` ghost reference (line 84-85) and hypothesis numbering gap in `CoulombConcreteTheorem42.lean` docstring.
- **Files**: `CoulombConcreteTheorem42.lean`
- **Approach**: Remove `hLogGrowth` reference, renumber hypotheses to be contiguous (1-12 or keep 1-13 with clear note).
- **START IMMEDIATELY.**

### 2. Fix MEMORY.md (`/simplify`)
- **What**: Remove false claims about Section9.lean, VelocityDecayInstance.lean (3 instances), CoulombNonvacuous sorry count.
- **Files**: `MEMORY.md` (in `.claude/projects/`)
- **Approach**: Update to reflect current file contents.

### 3. Fix multiGoal warnings in Section3Helpers2.lean (`/simplify`)
- **What**: 3 multiGoal warnings at lines 72-74.
- **Files**: `Section3Helpers2.lean`
- **Approach**: Add `<;>` or restructure tactics to avoid multi-goal state.

### 4. Remove linter suppressions from GaussianHelpers.lean (`/simplify`)
- **What**: File suppresses 5 linters globally. Fix the underlying issues.
- **Files**: `GaussianHelpers.lean`
- **Approach**: Add explicit `_` for unused variables, remove `show` where not needed, focus `simp` args, fix multi-goal patterns.

### 5. Remove linter suppressions from Section3Helpers.lean (`/simplify`)
- **What**: File suppresses 5 linters globally. Fix the underlying issues.
- **Files**: `Section3Helpers.lean`
- **Approach**: Same as item 4.

### 6. Fix long lines in files WITHOUT linter suppression (`/simplify`)
- **What**: Files that DON'T suppress longLine but still have warnings: `FlatTorus3Lemmas.lean:143`, `Section4.lean:207`, `Section5.lean:140-149`, `Section7.lean:165`, `Section8.lean:45,48`, `VMLInputDerive.lean:126`, `Theorem42.lean:197`, `TorusIntegration.lean:386-392`, `TorusInstance.lean:435,472`, `CoulombSpatialTransport.lean:173,212,351`, `LogBoundHelpers.lean:119-120`.
- **Files**: Multiple (listed above)
- **Approach**: Break lines at operators or introduce intermediate `have` bindings.

## Backlog

| Issue | Priority | Notes |
|-------|----------|-------|
| Reduce `maxHeartbeats 400000` in TorusIntegration.lean | P2 | May require decomposing the proof |
| Remove `linter.unusedVariables false` from CoulombNonvacuous.lean | P2 | Fix unused variable warnings |
| Rename `UniformSchwartzDecay` to `UniformC2Decay` | P3 | Misleading name |
| Add bounded-kernel instance (Ψ = const) | P3 | Would demonstrate Theorem42 generality |
| Weaken C³ to C² in velocity | P3 | Needs careful Clairaut rework |
| Mathlib upstreaming candidates | P3 | `integrable_one_add_norm_pow_mul`, IBP on AddCircle, `landauMatrix_mulVec_self` |
| Generalize beyond T³ | P4 | Major architectural change |
