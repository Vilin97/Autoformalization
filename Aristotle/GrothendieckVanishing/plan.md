# Work Plan — Grothendieck Vanishing

**Updated**: 2026-03-30T19:30Z

## Status Summary
- **Sorry count**: 2 (both in IrreducibleStep.lean, both Mathlib gaps)
- **Files**: 14 files, ~4162 lines
- **CI**: Unknown (no `gh` access). Uncommitted perf changes untested.
- **Docs**: Broken (404 on all GitHub Pages URLs)
- **Peak heartbeats**: 400K maxHeartbeats, 400K synthInstance (SetupCore, UNTESTED reduction from 1.6M)
- **Aristotle**: Both sorry's attempted (4 total), all failed. No pending jobs.

## Active multi-cycle strategies

1. **Sorry #1 — `subsheaf_contains_zeroOutsideInt`**: Aristotle failed twice. Requires stalk-level sheaf algebra not in Mathlib (toSheafify stalk iso for AddCommGrpCat, presheaf restriction to open subsets). Must decompose into sub-lemmas and prove manually. Target sub-lemmas: (a) stalks of subsheaves of Z_V are cyclic subgroups d·ℤ, (b) the multiplicity function d_x is locally constant on the support, (c) take V' where d_x is constant and minimal.

2. **Sorry #2 — `cohomology_vanishing_of_finitelyGenerated_vanishing`**: Aristotle failed. This is Hartshorne 2.9: K = colim K_α ⟹ H^m(K) = colim H^m(K_α). Requires LES for derived functors + filtered colimit commutativity. Mathlib gap is real. Consider alternative proof strategy: can we bypass filtered colimits entirely by working directly with the finitely generated subsheaf lattice?

3. **Heartbeat reduction**: 23 proofs still at 400K (2x default). SetupCore.lean synthInstance reduced to 400K via `letI` caching but UNTESTED. Systematic `letI` caching across all files could reduce further.

## This cycle's work items

1. **Fix stale docstrings** (P4, `/simplify`): Fix GrothendieckVanishing.lean:8 ("Setup.lean" → "IrreducibleStep.lean"), IrreducibleStep.lean:8 (clarify 2 sorry's), main.lean:14 (fix file reference). Immediate, no risk.

2. **Remove redundant wrapper theorems** (P3, `/cleanup`): `grothendieck_reduction` (IrreducibleStep.lean:714) and `grothendieck_vanishing_irreducible_pos` (line 727) are trivial wrappers around `IrreduciblePosVanishing`. Inline them. Check callers first.

3. **Submit sorry's to Aristotle** (P1, `/submit-aristotle`): Re-submit both sorry's with improved decomposition hints. Even though prior attempts failed, the decomposition into sub-lemmas may help.

4. **Attempt `subsheaf_contains_zeroOutsideInt` decomposition** (P1, `/prove`): Decompose into:
   - `zeroOutsideInt_stalk_cyclic`: stalks of subsheaves of Z_V are cyclic (d·ℤ ⊆ ℤ)
   - `subsheaf_multiplicity_locally_constant`: the multiplicity d_x is locally constant
   - `subsheaf_contains_on_constant_locus`: on V' where d is constant, Z_{V'} ↪ R
   Prove what we can, leave the hardest piece as a more targeted sorry.

5. **Commit and push** (P0, `/commit`): Push the uncommitted SetupCore.lean + CI workflow changes to get CI feedback. This is the only way to test the synthInstance.maxHeartbeats 400K reduction.

## Backlog
- Split IrreducibleStep.lean (738 lines) and ZeroOutside.lean (734 lines) into smaller files (P3)
- Investigate docs deployment failure — may need to re-trigger deploy.yml (P0 but blocked on `gh`)
- Apply `letI` HasDerivedCategory caching to other files with high synthInstance heartbeats (P3)
- Re-enable some disabled Mathlib linters (unusedTactic, unreachableTactic) and fix findings (P3)
- Extract FlasqueVanishing for Mathlib PR (P3)
