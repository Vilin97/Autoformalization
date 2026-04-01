# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-01T05:50Z

## Status Summary
- **Sorry count**: 2 (both in IrreducibleStep.lean, both Mathlib gaps)
- **Files**: 14 files under `main/`
- **CI**: RED — last 3 commits all fail on SetupCore.lean heartbeat timeout
- **Docs**: Broken (404 on GitHub Pages)
- **Peak heartbeats**: 800K maxHeartbeats (SetupCore), 4M synthInstance (FlasqueVanishing), 1.6M synthInstance (SetupCore ×5)
- **Aristotle**: No pending jobs. Both sorry's attempted previously, all failed.

## Active multi-cycle strategies

1. **Fix CI (P0)**: SetupCore.lean `epi_g_app_top_of_H1_vanishing` times out at 800K heartbeats. Root cause is `HasSmallLocalizedHom` synthesis in Ext/derived category operations. Strategy: refactor the proof to cache expensive typeclass instances with `letI` and extract sub-lemmas to reduce per-proof heartbeat pressure. This is the #1 priority — nothing else matters until CI is green.

2. **Sorry #1 — `exists_good_section`**: Decompose into sub-lemmas about stalk structure of subsheaves of Z_V. Prior Aristotle attempts failed. Must prove manually.

3. **Sorry #2 — `cohomology_vanishing_of_finitelyGenerated_vanishing`**: Hartshorne 2.9, filtered colimit commutativity. Genuine Mathlib gap. Consider alternative: can we avoid filtered colimits by using Noetherian ascending chain condition on subsheaves directly?

4. **Heartbeat reduction**: Systematic `letI` caching of `HasDerivedCategory`, `HasSmallLocalizedHom`, and related instances to bring all proofs under 400K, ideally under 200K.

## This cycle's work items

### 1. Fix CI — refactor `epi_g_app_top_of_H1_vanishing` (P0, `/prove`)
The proof at SetupCore.lean:194 times out because each `rw`/`exact` step triggers re-synthesis of derived category instances. Approach:
- Add `letI` bindings at the top for `HasDerivedCategory`, `HasSmallLocalizedHom`, and related instances
- Extract the `hψ` sub-proof (lines 214–221) into a separate lemma to reduce the proof term size
- If still over budget, split the proof into 2–3 lemmas with explicit type annotations to guide synthesis
- Target: maxHeartbeats ≤ 400K, synthInstance ≤ 400K

### 2. Reduce synthInstance.maxHeartbeats 4M in FlasqueVanishing.lean (P1, `/simplify`)
Line 53 has `synthInstance.maxHeartbeats 4000000` — 125x the Lean default. Apply `letI` caching for `HasDerivedCategory` and related instances. Target: ≤ 200K.

### 3. Reduce remaining 1.6M synthInstance overrides in SetupCore.lean (P2, `/simplify`)
Lines 233, 258, 312, 361 all have `synthInstance.maxHeartbeats 1600000`. Same `letI` caching strategy. Target: ≤ 400K.

### 4. Submit sorry's to Aristotle (P1, `/submit-aristotle`)
Re-submit both sorry's with fresh attempts. Even though prior attempts failed, it costs nothing.

### 5. Attempt sorry decomposition (P1, `/prove`)
If time permits after fixing CI, decompose `exists_good_section` into sub-lemmas.

## Backlog
- Split IrreducibleStep.lean (920 lines) into smaller files
- Split ZeroOutside.lean (734 lines) into smaller files
- Fix docs deployment (investigate GitHub Pages 404)
- Remove redundant wrapper theorems (`grothendieck_reduction`, `grothendieck_vanishing_irreducible_pos`)
- Fix stale docstrings
- Re-enable disabled Mathlib linters and fix findings
- Extract FlasqueVanishing for Mathlib PR
