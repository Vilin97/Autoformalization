# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-03-29T17:00Z
**Reviewer verdict**: REVISE

---

## 0. CI Status

**CI fix pushed (029fae5).** The Setup.lean→SetupCore.lean split was committed. CI run 23713895270 is in-progress.

- Previous 3 runs FAILED because SetupCore.lean was never committed.
- Fix: commit 029fae5 adds SetupCore.lean, thin Setup.lean, updated ReducibleVanishing.lean import.
- **Status: PENDING** — must verify CI passes before downgrading this from P0.

**Docs**: Blueprint (HTTP 200) and dep_graph (HTTP 200) are deployed.

## 1. Sorry's

**1 sorry in `main/`:**

| File | Line | Statement |
|------|------|-----------|
| `Setup.lean` | 95 | `IrreduciblePosVanishing` — kernel term in SES argument |

The statement is mathematically correct (it's Grothendieck vanishing restricted to irreducible positive-dim spaces). The proof requires 4 pieces of infrastructure that don't exist yet: direct-limit reduction, single-generator quotient, Step 4 local structure, Step 5 SES for `Z_U`. None of these are even partially formalized.

Aristotle cannot prove the negation (the theorem is true). However, the sorry could mask a **type error** in the surrounding proof: if `S.X₁` (the kernel of ClosedImmissionSES) has the wrong type or the SES isn't actually exact in the right category, the sorry would hide it. The proof at lines 96-107 uses `hKer` to close the LES argument, so the sorry is load-bearing.

## 2. Hidden Axioms

`lean_verify` on `GrothendieckVanishing` reports: `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`. The `sorryAx` traces to `IrreduciblePosVanishing`. No `admit`, `axiom`, or `native_decide` found.

I found no hidden axiom issue beyond the known sorry.

## 3. Circularity

The WF induction on `WithBot ℕ∞` is sound. `grothendieck_vanishing_aux` uses `ih` only at strictly smaller dimensions. `ReducibleVanishing'` uses `ih_irred` only on irreducible spaces of ≤ dimension. `IrreduciblePosVanishing` uses `ih` on strictly smaller dimension.

However, there is a **dependency tangle** between Setup.lean and ReducibleVanishing.lean:
- Committed ReducibleVanishing.lean imports Setup.lean
- Local ReducibleVanishing.lean imports SetupCore.lean
- Local Setup.lean imports ReducibleVanishing.lean

The committed state has `ReducibleVanishing.lean → Setup.lean` (single direction, fine). The local state has `Setup.lean → ReducibleVanishing.lean → SetupCore.lean` (also fine, but ONLY if SetupCore.lean exists). Since SetupCore.lean is untracked, this dependency chain is broken in the repository.

I found no logical circularity.

## 4. Hypothesis Audit

`GrothendieckVanishing` hypotheses:
- `X : TopCat.{u}` — necessary
- `F : TopCat.Sheaf AddCommGrpCat.{u} X` — necessary
- `[NoetherianSpace X]` — necessary (standard hypothesis)
- `(n : ℕ) (h : n > topologicalKrullDim X)` — necessary

**Issue**: Universe is locked to `u`. The theorem should hold universe-polymorphically.

**Issue**: `AddCommGrpCat` is hardcoded. The theorem holds for any Grothendieck abelian category (or at minimum any abelian category with enough injectives). This is a significant generality gap.

**Issue**: `NoetherianSpace X` could potentially be weakened to finite Krull dimension + DCC on closed subsets, though in practice these are equivalent for most applications.

## 5. Mathematical Correctness

The proved portions are mathematically sound:
- DimZeroVanishing: correct argument (only opens are ⊥ and ⊤ on irreducible dim-0 space)
- FlasqueVanishing: correct (flasque sheaves are acyclic)
- PushforwardHVanishing: correct (pushforward along closed immersion preserves flasqueness)
- ReducibleVanishing: correct (induction on irreducible components via ClosedImmersonSES)
- ClosedOpenDecomposition: correct (case split on empty/irreducible/reducible)
- GrothendieckVanishing: correct WF induction structure

The sorry in IrreduciblePosVanishing is correctly identified as the Hartshorne Steps 3-5 gap. The docstring now correctly documents that the naive support argument fails.

I found no mathematical incorrectness in proved portions.

## 6. Code Quality

**FIXED: Uncommitted critical files.** SetupCore.lean committed in 029fae5. CI pending.

**Issue (P1): `maxHeartbeats 12800000` at SetupCore.lean:214.** 64x default. This is `epi_app_of_shortExact_flasque` (the Zorn argument). A Mathlib reviewer would reject this immediately.

**Issue (P1): `maxHeartbeats 6400000` at ClosedImmersion.lean:338.** 32x default.

**Issue (P2): `maxHeartbeats 3200000` at 5 locations** (SetupCore.lean:173,675,752,939; ReducibleVanishing.lean:51,97). 16x default.

**Issue (P2): `maxHeartbeats 1600000` at 2 locations** (SetupCore.lean:81,117). 8x default.

**Issue (P2): SetupCore.lean is 1027 lines.** Above the 600-line guideline. The monolithic file structure makes maintenance difficult.

**Issue (P3): Stale comments in SetupCore.lean.**
- Line 211: "Two sorry's remain: (1) chain upper bound via sheaf gluing, (2) binary gluing" — STALE, both are proved.
- Line 751: "Requires: i_* is exact for closed immersions (sorry'd sub-lemma)" — STALE, PushforwardHVanishing is proved.

## 7. Documentation Lies

**Issue (P1):** `main.lean:7-8` says "Sorry's (1 remaining): IrreduciblePosVanishing (Setup.lean:95)". This is correct for the LOCAL state but **unverifiable** since the refactored Setup.lean was never committed. CI builds the old 1197-line Setup.lean which has different sorry locations.

**Issue (P1):** `main.lean:13` says "SetupCore.lean: category instances, FlasqueVanishing (PROVED)". SetupCore.lean doesn't exist in the repository. This documentation describes a file that CI has never seen.

**Issue:** `GrothendieckVanishing.lean:8` says "all proved, modulo FlasqueVanishing in Setup.lean". Stale — FlasqueVanishing is now in SetupCore.lean locally, and was proved (not sorry'd) in the committed Setup.lean either. Confusing wording.

**Issue:** LOG.md says "Sorry count: 1 (IrreduciblePosVanishing at Setup.lean:95)". The line number is correct locally but not in the committed version.

## 8. Generalization Opportunities

1. **Universe polymorphism** (feasibility: medium). Locked to `universe u`. Should work for any universe pair. Requires threading universe variables through all definitions.

2. **General abelian category** (feasibility: hard). Uses `AddCommGrpCat` throughout. The theorem holds for any Grothendieck abelian category with enough injectives. Requires abstracting over the category.

3. **Weakening NoetherianSpace on constantSheaf_flasque_of_irreducible** (feasibility: easy). This result only needs `IrreducibleSpace`, not `NoetherianSpace`. Currently requires NoetherianSpace through the import chain.

4. **Strengthening to functorial vanishing** (feasibility: hard). The current formulation gives `Subsingleton (Sheaf.H F n)`. A stronger statement would show the derived functor sheaf `R^n Γ` is zero, giving functorial vanishing, not just pointwise.

5. **Cohomological dimension bound** (feasibility: medium). The theorem implies `cd(X) ≤ dim(X)` for Noetherian spaces. This is a useful corollary that could be stated as a standalone theorem.

## 9. Mathlib Upstreamability

1. **`constantSheaf_flasque_of_irreducible`** — High value. Standard result missing from Mathlib. Needs: drop NoetherianSpace hypothesis, universe polymorphism, heartbeat reduction.

2. **`FlasqueVanishing`** — Very high value. Related to Brian Nugent's PR #35790. Needs: heartbeat reduction (12.8M → 800K for the Zorn argument), code cleanup, universe polymorphism.

3. **`epi_app_of_shortExact_flasque`** (the Zorn argument) — High value but currently at 64x heartbeats. Needs major refactoring before any Mathlib reviewer would accept it.

4. **`topologicalKrullDim_lt_of_isIrreducible_of_isClosed`** — Medium value. Standard dimension inequality. Likely needs minor cleanup.

5. **`closedIncl_unit_stalk_isIso`** — Medium value. Standard closed-immersion stalk result.

All need: heartbeat reductions to ≤ 800K, universe polymorphism, generalization from `AddCommGrpCat`, Mathlib style compliance.

---

## Open Issues (ranked by priority)

1. ~~**(P0)** SetupCore.lean committed in 029fae5.~~
2. **(P0)** CI must pass on 029fae5. Run 23713895270 is in-progress.
3. **(P1)** `maxHeartbeats 12800000` at SetupCore.lean:214 must be profiled and refactored below 800000.
4. **(P1)** `maxHeartbeats 6400000` at ClosedImmersion.lean:338 must be profiled and refactored.
5. **(P2)** Stale comments at SetupCore.lean:211,751 must be updated.
6. **(P2)** SetupCore.lean >1000 lines; should be split.
7. **(Critical)** `IrreduciblePosVanishing` sorry. No infrastructure for Steps 3-5 exists yet.

## Verdict: REVISE

CI fix committed (029fae5), awaiting pass. 1 sorry remains. Extreme heartbeat overrides (up to 64x default) make the code un-upstreamable. Must verify CI passes and reduce heartbeats before acceptance.
