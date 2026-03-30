# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-03-30T18:00Z
**Reviewer verdict**: REVISE

## 0. CI Status

Two CI runs in progress (`23759487699`, `23759375440`). Previous run cancelled. No green CI since perf decomposition.

Blueprint and dep graph return HTTP 200.

**P0 risk — CI unconfirmed.**

## 1. Sorry's (2)

1. **`subsheaf_contains_zeroOutsideInt`** (IrreducibleStep.lean:383): Subsheaf structure of Z_V. Mathematically true. Two Aristotle attempts failed. Requires stalk-level sheaf algebra not in Mathlib API.

2. **`cohomology_vanishing_of_finitelyGenerated_vanishing`** (IrreducibleStep.lean:540): Hartshorne 2.9 — cohomology commutes with filtered colimits. Confirmed Mathlib gap (missing LES for derived functors + colimit commutativity).

Both are genuine Mathlib gaps, not proof bugs.

## 2. Hidden Axioms

No `admit`, `axiom`, `native_decide`, or disabled linters. I found no issue.

## 3. Circularity

Well-founded induction on `topologicalKrullDim`. IH is strictly weaker. I found no issue.

## 4. Hypothesis Audit

`GrothendieckVanishing (X : TopCat.{u}) (F : Sheaf AddCommGrpCat.{u} X) [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X)` — all hypotheses necessary and standard. I found no issue.

## 5. Mathematical Correctness

Follows Hartshorne III.2.7 faithfully. Sorry's correspond to Steps 3A and 4. I found no issue.

## 6. Code Quality

**P3 — 11 proofs with maxHeartbeats > 800K** (CLAUDE.md limit is 200K):
- 7 at 3,200,000: binaryGlue_exists, closedIncl_pushforward_shortExact, PushforwardHVanishing_one, PushforwardHVanishing_succ, epi_unit_of_closedImmersion, closedIncl_unit_stalk_isIso, stalk_zero_of_ses_g_iso, ReducibleVanishing'
- 2 at 1,600,000: sectionsAt_preservesLeftHomologyOf, sections_exact_of_shortExact, cokernel_stalk_zero_V

**P3 — 3 files over 600 lines**: SetupCore.lean (1061), IrreducibleStep.lean (738), ZeroOutside.lean (734)

**P3 — synthInstance.maxHeartbeats 1,600,000** (3 instances in SetupCore for Ext types)

## 7. Documentation Lies

- CLAUDE.md: "sole gap is IrreduciblePosVanishing in Setup.lean" — sorry's are in IrreducibleStep.lean, 2 of them
- main.lean:14: "IrreduciblePosVanishing (1 sorry)" — hides the 2 concrete sorry's
- MEMORY.md: "1 sorry" — technically correct (1 wrapper), but misleading

## 8. Generalization Opportunities

1. **Generalize from AddCommGrpCat to Grothendieck abelian** (LOW feasibility)
2. **Extract FlasqueVanishing as Mathlib PR** (HIGH feasibility)
3. **Extract closedIncl_unit_stalk_isIso** (MEDIUM feasibility)
4. **Extract sheaf_isZero_of_zero_stalks** (HIGH feasibility)

## 9. Mathlib Upstreamability

1. `epi_app_of_shortExact_flasque` + `isFlasque_X₃_of_shortExact` — flasque theory (overlaps Nugent #35790)
2. `sheaf_isZero_of_zero_stalks` — basic missing lemma
3. `closedIncl_unit_stalk_isIso` — stalk computation for closed immersions
4. `IsPartialLift` decomposition — reusable Zorn argument pieces

## Open Issues

| # | Priority | Issue |
|---|----------|-------|
| 1 | P0 | CI unconfirmed after perf decomposition |
| 2 | P1 | 2 sorry's (Mathlib gaps) |
| 3 | P3 | 11 proofs with maxHeartbeats > 800K |
| 4 | P3 | 3 files over 600 lines |
| 5 | P4 | CLAUDE.md stale (sorry location) |
| 6 | P4 | main.lean docstring inaccurate |
