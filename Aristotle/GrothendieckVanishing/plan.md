# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-02T01:00Z

## Status Summary
- **CI**: PR #5 pending merge (`wip/grothendieck-vanishing` → `grothendieck-vanishing`)
- **Heartbeat overrides**: 0
- **Sorry count**: 2 in IrreducibleStep.lean
- **Files**: 15 files under `main/`, ~6000 lines

## Remaining Sorry's (2)

### 1. Divisibility sub-goal in `exists_section_generating_stalks` (line ~934)
**Goal**: For any `a ∈ stalk(R, x)` with `x ∈ W`, show `∃ k, a = k • germ(s_W, x)`.

Equivalently: if `i_x(a) = n • gen` and `i_x(germ(s_W, x)) = d • gen` (known), show `d | n`.

**Status**: 90% of `exists_section_generating_stalks` is proved. All steps except this divisibility.

**Fix needed**: The proof currently picks x₀ arbitrarily via `exists_nonzero_stalk_in_V`. It should instead pick x₀ to **minimize** the generator `d`. With minimality:
- `d_x | d` (proved: from `hcoeff_const`, `d ∈ image(i_x)`)
- `d ≤ d_x` (from minimality)
- Combined: `d_x = d`, so `d | n` (since `d_x | n`)

**Implementation**: Restructure proof to use `Nat.find` or well-founded induction on d to choose x₀ with minimal generator. This requires changes to Steps 1-2 of the proof.

### 2. `cohomology_vanishing_of_finitelyGenerated_vanishing` (line ~1111)
**Hartshorne 2.9**: If H^m = 0 for all finitely generated subsheaves, then H^m(K) = 0.

**Strategy**: K = colim K_α, H^m(K) = colim H^m(K_α) = 0. Requires Ext commuting with filtered colimits (AB5 / Grothendieck abelian).

## What's Been Proved (this cycle)

Closed 21+ sorry's total:
- All stalk lemmas (Tier 1-2): 8 proofs
- ClosedImmersionSES pattern: 4 proofs (cokernel_openHom_vanishing, etc.)
- Finset infrastructure: 5 proofs
- Germ algebra: 2 proofs
- exists_good_section: proved using exists_section_generating_stalks
- zsmul_generator_injective, sHom_stalk_bijective_at: new helper lemmas
- 90% of exists_section_generating_stalks (Steps 1-5 of Noetherian shrinking)

## Backlog
- Update plan sorry counts after fixes
- Docs deployment: Fix 404 on blueprint pages
