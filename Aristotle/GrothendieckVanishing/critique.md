# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-02T22:20Z
**Reviewer verdict**: CONDITIONAL PASS

## 0. CI Status

All CI runs **green**. Local `lake build` succeeds with 0 errors.

## 1. Sorry's (1)

One `sorry` at `FiniteGeneratorReduction.lean:~94` inside `ext_comm_filtered_colimit_mono`.

**Precise goal**: `Subsingleton (Ext Z ip.shortComplex.X₃ n)` — vanishing of Ext^n on the
cokernel Q = I/c.pt of an injective embedding.

**What's proved**: The dimension shift via the covariant Ext LES reduces Ext^{n+1}(Z, c.pt)
to Ext^n(Z, Q). The injective vanishing Ext^{n+1}(Z, I) = 0 is proved. The n=0 case of
the full theorem is PROVED. The n≥1 case's sorry is isolated to exactly this one subgoal.

**Why it remains**: Q = colim Q_j (by AB5 + mono transitions) with Ext^n(Z, Q_j) = 0 for
each j (per-j LES). But showing Ext^n preserves this colimit requires infrastructure not
in Mathlib v4.28.0 (universal δ-functors / Čech / derived category colimits). The quotient
diagram has epi transitions, blocking recursive application.

**Assessment**: Genuine Mathlib API gap. The statement is mathematically true
(Hartshorne III Lemma 2.9). No risk of falsity.

## 2. Hidden Axioms

None. No `admit`, `axiom`, `native_decide`, or linter/heartbeat overrides.

## 3. File Sizes

- `IrreducibleStep.lean`: 1263 lines (26% over 1000-line guideline, acceptable)
- `FiniteGeneratorReduction.lean`: ~370 lines
- All other files ≤ 733 lines

## 4. Code Quality

- `sheafH_vanishing_succ` and `sheafH_vanishing_cascade` are public with docstrings
- No heartbeat overrides
- No dead code
- The sorry is well-decomposed: dimension shift is explicit, injective vanishing proved,
  only the core colimit-transfer subgoal remains

## 5. Documentation

All headers consistent with 1 sorry in FiniteGeneratorReduction.lean

## 6. Open Issues

| # | Priority | Issue |
|---|----------|-------|
| 1 | P0 | 1 sorry: Ext^n colimit transfer (Mathlib gap, see plan.md for paths) |
| 2 | P1 | Docs/blueprint return 404 |
