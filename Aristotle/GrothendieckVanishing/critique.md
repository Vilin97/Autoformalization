# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-03-28T10:10Z
**Reviewer verdict**: CONDITIONAL ACCEPT

---

## 0. CI Status

Two CI runs in progress (heartbeat reduction + linter fix commits). Previous builds passed. `lake build` locally passes with 0 errors. Blueprint and dep graph deployed (HTTP 200).

No P0 issues.

---

## 1. Sorry's

**1 sorry** in Setup.lean:56 (`FlasqueVanishing`).

| Sorry | File:Line | Statement true? | Risk |
|---|---|---|---|
| `FlasqueVanishing` | Setup.lean:56 | Yes (Grothendieck III.2.7) | **Blocked** — requires j_! (extension by zero), Prop 2.9 (direct limits), or derived adjunction for pushforward. None in Mathlib v4.28. |

This sorry IS the main theorem itself. All downstream files are proved modulo this single sorry. The dim 0 case is proved independently via projectivity of the constant sheaf.

**CRITICAL finding**: Aristotle (99a8a5d6) proved that **flasque → injective is FALSE** (ℤ on point is flasque but not injective). The counterexample is formalized in Auxiliary.lean (`not_injective_int`). The current proof structure does NOT depend on this false claim.

---

## 2. Hidden Axioms

`lean_verify GrothendieckVanishing` would return `sorryAx` (from FlasqueVanishing).

No `admit` or `axiom` keywords anywhere. All gaps are visible as `sorry`.

---

## 3. Circularity

No circularity. `FlasqueVanishing` (sorry) is called by `ReducibleVanishing` and `IrreduciblePosVanishing` (both proved from it). The main induction in `GrothendieckVanishing.lean` uses well-founded induction on `WithBot ℕ∞`.

The dim 0 case (`grothendieck_vanishing_dim_zero`) is proved independently of FlasqueVanishing via projectivity of the constant sheaf.

---

## 4. Hypothesis Audit

Main theorem:
```
GrothendieckVanishing (X : TopCat.{u}) (F : Sheaf AddCommGrpCat X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

All hypotheses necessary. `AddCommGrpCat` could generalize to `ModuleCat R` (hard).

---

## 5. Mathematical Correctness

Proof structure faithfully follows Hartshorne III.2.7. Key insight: the dim 0 case bypasses flasque sheaf theory entirely using projectivity of the constant sheaf (via `constantSheafΓAdj.map_projective`).

---

## 6. Code Quality

| Issue | Status |
|---|---|
| All `maxHeartbeats` ≤ 400000 (2× default) | **Fixed** |
| All heartbeat overrides have comments | **Fixed** |
| No bare `simp` (only `simp only` or `simp [...]`) | **OK** (one bare `simp` in ConstantSheafFlasque.lean:97 is acceptable) |
| No files over 300 lines | **OK** (max: Auxiliary.lean at 277) |
| No `admit` or `axiom` | **OK** |
| 9 files, 1033 lines total | **Good** |

---

## 7. Documentation

All docstrings accurate. main.lean correctly lists file structure and sorry status.

---

## 8. Independently Proved Results (sorry-free, upstreamable)

| Result | Location | Upstreamability |
|---|---|---|
| `cohomologyPresheafTopEquiv` (H'(⊤,F) ≅ H(F)) | CohomologyIso.lean | **High** — resolves Mathlib TODO |
| `subsingleton_ext_of_ses` | IrreducibleStep.lean | **High** — generic Ext LES vanishing |
| `not_injective_int` (ℤ not injective in Ab) | Auxiliary.lean | **High** — standalone result |
| `addMonoidHom_rat_int_eq_zero` | Auxiliary.lean | **High** — standalone result |
| `constantSheaf_flasque_of_irreducible` | ConstantSheafFlasque.lean | **Medium** — specific to constant sheaf |
| `ulift_int_projective` | Auxiliary.lean | **Medium** — via ModuleCat equivalence |
| `grothendieck_vanishing_dim_zero` | DimZeroVanishing.lean | **Medium** — dim 0 via projectivity |
| `topologicalKrullDim_lt_of_isIrreducible_of_isClosed` | Auxiliary.lean | **Medium** |

---

## 9. Generalization Opportunities

1. **(Hard)** Build j_! (extension by zero) to close the remaining sorry.
2. **(Medium)** Generalize from `AddCommGrpCat` to `ModuleCat R`.
3. **(Feasible)** PR `cohomologyPresheafTopEquiv` and `subsingleton_ext_of_ses` to Mathlib.
4. **(Feasible)** PR `not_injective_int` and `addMonoidHom_rat_int_eq_zero` to Mathlib.

---

## Verdict: CONDITIONAL ACCEPT

### Condition for ACCEPT:
- Close the single remaining sorry (`FlasqueVanishing`). This requires j_! infrastructure not in Mathlib v4.28, so acceptance is conditional on either:
  1. Building j_! (~500 lines of new infrastructure), OR
  2. Finding an alternative proof path (e.g., Čech cohomology, direct limit approach), OR
  3. Waiting for Mathlib to add j_! (planned but no timeline)

### What IS proved (sorry-free):
- Full induction structure for Grothendieck vanishing
- Dim 0 case via constant sheaf projectivity
- Empty space case
- Constant sheaf is flasque on irreducible spaces
- H'(⊤) ≅ H (cohomology isomorphism)
- Abstract LES vanishing
- Counterexample: flasque ≠ injective
- Dimension inequalities for closed subsets
