# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-03-29T16:20Z
**Reviewer verdict**: REVISE

---

## 0. CI Status

- Latest CI run (push 2c4c81e) is **in progress**.
- Previous CI run (push 331d1d5) **FAILED**. Unable to retrieve failure logs due to sandbox. This is a **P0** issue — the last completed push that passed CI was b8a1821 (ReducibleVanishing), meaning the PushforwardHVanishing degree-1 commit may have broken the build.
- Blueprint and dep_graph both return HTTP 200 — docs are deployed.

**Issue (P0):** CI failure on commit 331d1d5. Until CI passes on HEAD, claimed progress is unverified.

## 1. Sorry's

**Exactly 1 sorry in `main/`:**

| File | Line | Statement |
|------|------|-----------|
| `Setup.lean` | 95 | `IrreduciblePosVanishing` kernel term |

The statement is mathematically correct (Grothendieck vanishing is a theorem). The proof requires 4 pieces of new infrastructure (direct-limit reduction, single-generator quotient, Step 4 local structure, Step 5 SES). None exist yet.

## 2. Hidden Axioms

No `admit`, `axiom`, or `native_decide` found beyond standard Mathlib usage. Standard classical logic only.

I found no issue.

## 3. Circularity

No circularity. WF induction on `WithBot ℕ∞` is sound. `ReducibleVanishing'` uses `ih_irred` only on irreducible spaces of ≤ dimension. `IrreduciblePosVanishing` uses `ih` on strictly smaller dimension.

I found no issue.

## 4. Hypothesis Audit

All hypotheses of `IrreduciblePosVanishing` are necessary and standard.

**Minor issue:** The IH does not require `[IrreducibleSpace Y]` but downstream `ClosedOpenDecomposition` uses `ih_irred` which does. Harmless asymmetry but confusing.

## 5. Mathematical Correctness

The docstring now correctly documents that the support-based argument fails on irreducible spaces. The sorry is honestly marked. The proved portions (ClosedImmissionSES setup, pushforward vanishing, LES reduction) are correct.

I found no mathematical incorrectness in proved portions.

## 6. Code Quality

**Issue (P1): `maxHeartbeats 12800000` at SetupCore.lean:214.** 64x default. Fragile, likely to break with Mathlib updates.

**Issue (P1): `maxHeartbeats 6400000` at ClosedImmersion.lean:338.** 32x default.

**Issue (P2): `maxHeartbeats 3200000` at 6 locations** (SetupCore, ReducibleVanishing). 16x default.

**Issue (P2): SetupCore.lean is 1027 lines.** Above 600-line guideline. Should be split.

**Issue (P3): Dead code in SetupCore.lean.** Old `ReducibleVanishing` comments referencing sorry's at lines 211, 751 are stale.

## 7. Documentation Lies

**Issue:** `main.lean:13` says "Setup.lean: category instances + 3 sorry'd theorems". Stale — Setup.lean now has 1 sorry.

**Issue:** `ClosedOpenDecomposition.lean:7` says "Reducible X: sorry". Stale — reducible case is proved.

**Issue:** `IrreducibleStep.lean:8` says "uses IrreduciblePosVanishing (sorry)". Correct but should cite Setup.lean:95.

## 8. Generalization Opportunities

1. **Universe polymorphism:** Locked to `universe u`. Should work for any universe. Feasibility: medium.
2. **General abelian category:** Uses `AddCommGrpCat` throughout. Should hold for any Grothendieck abelian category. Feasibility: hard.
3. **Weakening NoetherianSpace:** `constantSheaf_flasque_of_irreducible` only needs `IrreducibleSpace`. Feasibility: easy.

## 9. Mathlib Upstreamability

1. **`constantSheaf_flasque_of_irreducible`** — High value. Standard result missing from Mathlib.
2. **`FlasqueVanishing`** — Very high value. Related to Brian Nugent's PR #35790.
3. **`closedIncl_unit_stalk_isIso`** — Medium value. Standard closed-immersion result.
4. **`topologicalKrullDim_lt_of_isIrreducible_of_isClosed`** — Medium value.

All need: heartbeat reductions, universe polymorphism, generalization from `AddCommGrpCat`.

---

## Open Issues (ranked by priority)

1. **(P0)** CI must pass on HEAD.
2. **(P1)** `maxHeartbeats 12800000` at SetupCore.lean:214 must be profiled/refactored.
3. **(P1)** Stale docstrings in main.lean, ClosedOpenDecomposition.lean.
4. **(P2)** SetupCore.lean >1000 lines; dead code removal needed.
5. **(Critical)** `IrreduciblePosVanishing` sorry. Step 5 (vanishing for Z_U) is the most concrete achievable sub-goal.

## Verdict: REVISE
