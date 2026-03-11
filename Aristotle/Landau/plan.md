# Plan — Cycle 112

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,589 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: CONDITIONAL ACCEPT (one medium-severity documentation issue)
- **Aristotle jobs**: 0 pending (5 done, 1 failed/proved manually, many completed)
- **maxHeartbeats overrides**: 2 (TorusIntegration 400000, NewtonianPotential 800000)
- **`simp +decide`**: 0 (fully eliminated in prior cycles)
- **Lines over 100 chars**: 0
- **Files over 600 lines**: 1 (Section3Helpers.lean at 613)
- **Working tree**: clean (only critique.md modified, state.md untracked)

## This cycle's work items

### 1. Document hLogGrowth independence from hSchwartz (`/strengthen`)
- **What**: The sole medium-severity issue from critique.md (issue 5). The main theorem docstring explains why hGradBound is independent of hSchwartz+hLogGrowth, but does NOT explain why hLogGrowth is independent of hSchwartz. A reader seeing both "Schwartz decay" and "polynomial log growth" will naturally wonder if the latter follows from the former.
- **File**: `Aristotle/Landau/main/CoulombConcreteTheorem42.lean`, lines 30-53 (docstring)
- **Approach**: Add a paragraph after the existing "Independence note" block explaining: Schwartz decay gives an upper bound |f(x,v)| <= C_N/(1+||v||)^N but does NOT give a lower bound on f. Therefore it does not bound -log f(x,v), which can grow arbitrarily fast. hLogGrowth (polynomial |log f| growth) implicitly encodes a stretched-exponential lower bound f(x,v) >= exp(-C(1+||v||)^K), which is genuinely independent of the Schwartz upper bound.
- **Resolves**: Critique issue 5 (medium), promoting verdict from CONDITIONAL ACCEPT to ACCEPT.
- **Can start immediately**: yes, pure documentation edit.

### 2. Remove unused `Fin.sum_univ_three` from `simp` calls in Defs.lean (`/simplify`)
- **What**: Critique issue 7d. Three `simp` calls at lines 98, 103, 108 include `Fin.sum_univ_three` which the linter flags as unused.
- **File**: `Aristotle/Landau/main/Defs.lean`, lines 98, 103, 108
- **Approach**: Remove `Fin.sum_univ_three` from each `simp` list. Verify with `lake env lean` that the proofs still close. (Note: lines 219, 223, 227, 306 also use `Fin.sum_univ_three` but in `simp only` calls where it may be needed -- check those too.)
- **Resolves**: Critique issues 7d and 7e (low).

### 3. Reduce `maxHeartbeats 800000` in NewtonianPotential.lean (`/simplify`)
- **What**: The remaining maxHeartbeats 800000 override is at the project ceiling. Try to bring it down to 400000 or eliminate it.
- **File**: `Aristotle/Landau/main/NewtonianPotential.lean`, line 85
- **Approach**: Profile the proof with `lean_profile_proof` to identify the slow tactic. Try `simp only` narrowing, term-mode rewrites, or proof restructuring to reduce heartbeats.
- **Risk**: Medium -- may require non-trivial proof restructuring. Skip if no easy wins.

### 4. Refresh MEMORY.md file inventory and line counts
- **What**: Critique issues 8a and 8b. MEMORY.md lists 7 Coulomb files but there are 10 (missing CoulombFluxBound, CoulombFluxConv, CoulombForceTransport, CoulombPSDHelpers, CoulombNonvacuous). Line counts are 3-4x stale.
- **File**: `/home/vilin/.claude/projects/-home-vilin-aristotle/memory/MEMORY.md`
- **Approach**: Update the "Coulomb files" section with all 10 files and current `wc -l` counts. Update total file/line counts.

### 5. Update critique.md to reflect cycle 112 changes
- **What**: After completing items 1-4, re-run `/critique` to verify the medium-severity issue is resolved and update the summary table.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| Section3Helpers.lean 613 lines | Code quality | Just over 600-line limit; contents are tightly coupled, splitting would be artificial. Leave as-is. |
| 3 proofs over 150 lines | Code quality | All under 200 lines. Diminishing returns on decomposition. |
| TorusIntegration maxHeartbeats 400000 | Performance | Lower priority since well under 800000 ceiling. |
| Generalize beyond T^3 | Feature | Hard; requires parameterizing all Coulomb files over abstract FlatTorus3. |
| Dimension generalization (Fin n) | Feature | Hard; 3D is hard-coded everywhere. |
| Multi-species | Feature | Hard; requires coupling multiple distribution functions. |
| Mathlib PRs for helper lemmas | Upstream | 5 candidates: iteratedFDeriv_clm_zero, inverse_poly_integrable, schwartz_pointwise_decay, poisson_boltzmann_max_principle, second_deriv_nonpos_at_local_max'. |
| IsMaxwellian API strengthening | Mathematical | Add IsMaxwellian.unique (parameter agreement from function equality) or IsMaxwellian.integrable (Gaussian integral convergence). |
