# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-03-30T19:30Z
**Reviewer verdict**: REVISE

## 0. CI Status

Unable to run `gh` on this machine. No local Lean toolchain available to run `lake build`.

**Docs deployment is broken**: `https://vilin97.github.io/aristotle/` returns HTTP 404. `https://vilin97.github.io/aristotle/docs/` also 404. `https://vilin97.github.io/aristotle/blueprint/` also 404. The entire GitHub Pages site is down. The `deploy.yml` workflow exists but it is unclear when it last succeeded.

**Uncommitted changes**: SetupCore.lean has been modified (synthInstance.maxHeartbeats reduced from 1.6M to 400K with `letI` caching, CI workflow modified to remove doc-gen). These changes are UNTESTED — no local build or CI run has verified them. If the `letI` caching is insufficient and `HasDerivedCategory` synthesis still exceeds 400K heartbeats per attempt, these changes will break the build.

**P0 — Docs deployment broken. P0 — Uncommitted changes untested.**

## 1. Sorry's (2)

1. **`subsheaf_contains_zeroOutsideInt`** (IrreducibleStep.lean:383): Given a non-zero subsheaf `R` of `Z_V`, find an open `V' ⊆ V` with `Z_{V'} ↪ R` bijective on stalks. Mathematically true (stalks of subsheaves of `ℤ` are `dℤ` for some `d`, take `V'` where `d` is constant). Two Aristotle attempts failed. Requires stalk-level sheaf algebra (toSheafify stalk iso for AddCommGrpCat, presheaf restriction, etc.) that is not in Mathlib API.

2. **`cohomology_vanishing_of_finitelyGenerated_vanishing`** (IrreducibleStep.lean:540): Hartshorne 2.9 core — cohomology commutes with filtered colimits. Confirmed Mathlib gap: requires LES for derived functors + colimit commutativity for sheaf cohomology. No existing Mathlib API covers this.

Both sorry's are load-bearing — they appear in the dependency chain of `IrreduciblePosVanishing`, which is required by the main theorem. The formalization is INCOMPLETE without them. Calling this "modulo Mathlib gaps" does not change the fact that the main theorem depends on unproved propositions.

## 2. Hidden Axioms

No `admit`, `axiom`, `native_decide`, or disabled linters in source files. The lakefile disables 5 Mathlib linters (`mathlibStandardSet`, `unusedSimpArgs`, `unnecessarySimpa`, `unusedTactic`, `unreachableTactic`). These suppressions could hide dead code and redundant tactics. I found no issue beyond the linter suppressions.

## 3. Circularity

Well-founded induction on `topologicalKrullDim` (type `WithBot ℕ∞`). The induction hypothesis is strictly weaker (requires `d' < d`). The `IrreduciblePosVanishing` proof obtains `Z` with `dim Z < dim X` and applies `ih` correctly. I found no issue.

## 4. Hypothesis Audit

`GrothendieckVanishing (X : TopCat.{u}) (F : Sheaf AddCommGrpCat.{u} X) [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X)`:

- `TopCat.{u}` — standard, necessary for universe consistency
- `Sheaf AddCommGrpCat.{u} X` — could theoretically generalize to Grothendieck abelian categories, but AddCommGrpCat is standard for this theorem
- `[NoetherianSpace X]` — necessary, standard
- `n : ℕ` — standard encoding of cohomological degree
- `h : n > topologicalKrullDim X` — necessary, standard. Uses `WithBot ℕ∞` which handles the case `dim X = ⊤` correctly (vacuously true since no `n : ℕ` exceeds `⊤`)

All hypotheses are necessary and standard. I found no issue.

## 5. Mathematical Correctness

Follows Hartshorne III.2.7 faithfully:
- Reduction to irreducible: correct (closed-open decomposition, Finset induction on components)
- Dim 0 base case: correct (constant sheaf is flasque on irreducible space)
- Irreducible positive dim: correct strategy (closed immersion SES, pushforward vanishing, kernel vanishing via Hartshorne Steps 3-5)
- FlasqueVanishing: correct (dimension shifting via injective presentations)

The 2 sorry's correspond exactly to Steps 3A (filtered colimit) and 4 (subsheaf classification). These are mathematically correct statements. I found no issue with the proof strategy.

## 6. Code Quality

**P2 — 23 proofs with maxHeartbeats 400000** (CLAUDE.md limit is 200000):
- FlasqueVanishing.lean: 6 overrides
- SetupCore.lean: 7 overrides (including 3 with synthInstance.maxHeartbeats 400000)
- IrreducibleStep.lean: 4 overrides
- ReducibleVanishing.lean: 2 overrides
- ConstantSheafFlasque.lean: 2 overrides
- Auxiliary.lean: 1 override
- ClosedImmersion.lean: 1 override

**P2 — synthInstance.maxHeartbeats overrides**: 3 at 400000 (SetupCore, down from 1.6M but UNTESTED), 2 at 200000 (IrreducibleStep, ZeroOutside), 5 at 160000 (SetupCore, ReducibleVanishing, ClosedImmersion), 10 at 80000 (various). The 400K synthInstance overrides are 12.5x the Lean default of 32000.

**P3 — 3 files over 600 lines**: IrreducibleStep.lean (738), ZeroOutside.lean (734), FlasqueVanishing.lean (608). SetupCore.lean was reduced from 1061 to 478, but the debt moved to FlasqueVanishing.lean.

**P3 — 5 Mathlib linters disabled** in lakefile.toml. `unusedTactic` and `unreachableTactic` could hide dead proof steps.

**P3 — Redundant wrapper theorems**: `grothendieck_reduction` (IrreducibleStep.lean:714) is just `IrreduciblePosVanishing`. `grothendieck_vanishing_irreducible_pos` (line 727) is just `grothendieck_reduction`. These are dead indirections.

## 7. Documentation Lies

- **CLAUDE.md line 63**: "Never increase maxHeartbeats above 200000" — 23 proofs violate this. The codebase itself contradicts its own discipline.
- **GrothendieckVanishing.lean line 8**: "all proved, modulo IrreduciblePosVanishing sorry in Setup.lean" — sorry's are in IrreducibleStep.lean, not Setup.lean.
- **IrreducibleStep.lean line 8**: "uses IrreduciblePosVanishing (sorry)" — there are 2 sorry's, not 1. Calling the wrapper "1 sorry" hides 2 distinct proof obligations.
- **main.lean line 14**: "IrreduciblePosVanishing (2 sorry's inside)" — correct count but wrong location claim ("Setup.lean" in structure section vs actual IrreducibleStep.lean).
- **GitHub Pages docs**: completely broken (404). Any claim about docs being deployed is false.
- **LOG.md line 13**: "Peak maxHeartbeats: 12,800,000 → 3,200,000 (75% reduction)" — this is stale; current peak is 400,000 (after subsequent commits). But the uncommitted changes to SetupCore.lean synthInstance are untested.

## 8. Generalization Opportunities

1. **Generalize from AddCommGrpCat to Grothendieck abelian categories** (LOW feasibility). The theorem should hold for any Grothendieck abelian category `A` with enough injectives. Current proof uses concrete `AddMonoidHom`, `ULift ℤ`, `zsmul` operations that don't generalize. Would require rewriting FlasqueVanishing, PushforwardHVanishing, and all stalk arguments.

2. **Extract FlasqueVanishing as standalone Mathlib PR** (HIGH feasibility). `FlasqueVanishing` + `isFlasque_of_injective` + `epi_app_of_shortExact_flasque` form a self-contained package. Overlaps with Nugent PR #35790 but could be complementary.

3. **Extract `sheaf_isZero_of_zero_stalks`** (HIGH feasibility). Basic missing lemma: a sheaf whose stalks are all zero is zero. Currently proved inline; should be a standalone Mathlib lemma.

4. **Weaken NoetherianSpace to locally Noetherian** (MEDIUM feasibility). Grothendieck vanishing holds for locally Noetherian spaces via sheafification on a cover. Would require significant refactoring of the induction structure.

5. **Strengthen to give explicit isomorphism `H^n(X,F) ≅ 0`** (LOW feasibility). Current statement is `Subsingleton (Sheaf.H F n)` which is weaker than `IsZero`. Could strengthen but `Subsingleton` suffices for applications.

## 9. Mathlib Upstreamability

1. **`epi_app_of_shortExact_flasque` + `isFlasque_X₃_of_shortExact`** — Flasque sheaf theory. Core result: in a SES of sheaves, if F₁ and F₂ are flasque, so is F₃. Overlaps Nugent #35790 but well-decomposed.

2. **`sheaf_isZero_of_isEmpty`** — A sheaf on an empty space is zero. Basic missing lemma. Straightforward PR.

3. **`closedIncl_unit_stalk_isIso`** — Stalk of the adjunction unit for closed immersion is an isomorphism. Useful infrastructure for closed immersion theory.

4. **`IsPartialLift` decomposition** — Reusable Zorn argument pattern for lifting sections of sheaves. Clean abstraction.

5. **`pushforward_stalk_zero_closedIncl`** — Stalk of pushforward along closed immersion vanishes outside the closed set. Basic infrastructure.

## Open Issues

| # | Priority | Issue |
|---|----------|-------|
| 1 | P0 | Docs deployment broken (404 on all pages) |
| 2 | P0 | Uncommitted SetupCore.lean changes untested |
| 3 | P1 | 2 sorry's (Mathlib gaps, load-bearing) |
| 4 | P2 | 23 proofs exceed maxHeartbeats 200K limit |
| 5 | P2 | 3 synthInstance.maxHeartbeats at 400K (12.5x default) |
| 6 | P3 | 3 files over 600 lines |
| 7 | P3 | 5 Mathlib linters disabled in lakefile |
| 8 | P3 | Redundant wrapper theorems (grothendieck_reduction) |
| 9 | P4 | Stale docstrings (sorry locations, heartbeat claims) |
| 10 | P4 | GrothendieckVanishing.lean line 8 wrong file reference |
