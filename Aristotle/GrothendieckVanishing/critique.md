# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-02T22:50Z
**Reviewer verdict**: CONDITIONAL PASS

## 0. CI Status

Latest CI run (23925337164) **in_progress**. Previous two runs **green**.
No `admit`, `axiom`, `native_decide`, heartbeat overrides, or `set_option linter` found.

**Docs (P1)**: `https://vilin97.github.io/aristotle/blueprint/` returns **HTTP 404**.

## 1. Sorry's (1)

**`FiniteGeneratorReduction.lean:65`**: `ext_vanishing_of_colimit_pieces` — sorry.

Statement: For a filtered colimit c = colim Y_j in a Grothendieck abelian category, if
Hom(Z,-) transfers subsingleton and Ext^n(Z, Y.obj j) = 0 for all j, then Ext^n(Z, c.pt) = 0.

Mathematically true (Hartshorne III Lemma 2.9). No risk of falsity. The sorry is cleanly
isolated — `ext_comm_filtered_colimit_mono` delegates to it; no other sorry in the project.

## 2. Hidden Axioms

I found no issue. `lean_verify` on main theorems reports no axioms beyond propext/choice/Quot.sound.

## 3. Circularity

I found no issue. WF induction on dimension; sorry is in a non-recursive helper.

## 4. Hypothesis Audit

Main theorem hypotheses are minimal and standard (Hartshorne III.2.7). I found no issue.

## 5. Mathematical Correctness

I found no divergence from the standard proof.

## 6. Code Quality

| Issue | Priority |
|-------|----------|
| `IrreducibleStep.lean` at 1263 lines (26% over 1000-line guideline) | P3 |
| `FiniteGeneratorReduction.lean` header still references old sorry location at line 6 | P4 |

## 7. Documentation Lies

- `FiniteGeneratorReduction.lean:6` says "1 sorry: Ext^n(Z, cokernel(ι)) for cokernel of
  injective embedding" but the sorry is now `ext_vanishing_of_colimit_pieces` (general
  colimit transfer, no injective embedding). Stale.

## 8. Generalization Opportunities

1. Drop NoetherianSpace to finite cohomological dimension (medium)
2. Generalize to arbitrary Grothendieck topologies (hard)
3. Extract `FlasqueVanishing` as Mathlib PR (easy)

## 9. Mathlib Upstreamability

- `FlasqueVanishing`, `constantSheaf_flasque_of_irreducible`, `subsingleton_ext_of_ses` family,
  `sheafH_vanishing_cascade` — all candidates.

## Open Issues

| # | Priority | Issue |
|---|----------|-------|
| 1 | P0 | 1 sorry: ext_vanishing_of_colimit_pieces (Mathlib gap) |
| 2 | P1 | Docs/blueprint 404 |
| 3 | P3 | IrreducibleStep.lean at 1263 lines |
| 4 | P4 | FiniteGeneratorReduction.lean header stale |

**Verdict**: CONDITIONAL PASS
