# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-01T05:45Z
**Reviewer verdict**: REVISE

## 0. CI Status

**P0 — CI is RED.** All 3 most recent CI runs on `grothendieck-vanishing` are failing:

```
completed  failure  fix: restore original heartbeat budgets...  23827254792  21m52s  2026-04-01
completed  failure  fix: increase maxHeartbeats to 800K...     23826964530   8m57s  2026-04-01
completed  failure  fix: add maxHeartbeats 400K...             23826711040   9m3s   2026-04-01
```

Root cause: `SetupCore.lean` line ~221 fails with `(deterministic) timeout at 'isDefEq', maximum number of heartbeats (800000) has been reached` during `HasSmallLocalizedHom` synthesis for derived category Ext operations. Cascading failure takes out `epi_g_app_top_of_H1_vanishing` and everything downstream.

The last 3 commits were all failed attempts to fix this by bumping heartbeats (400K → 800K). The code is in a broken state. **Nothing compiles.**

**P1 — Docs deployment broken.** Both `https://vilin97.github.io/aristotle/blueprint/` and `https://vilin97.github.io/aristotle/blueprint/dep_graph_document.html` return HTTP 404. The entire documentation site is down.

## 1. Sorry's (2)

Both in `IrreducibleStep.lean`, both load-bearing for the main theorem:

1. **`exists_good_section`** (line 554): Given a non-zero subsheaf R of Z_V, find V' ⊆ V with a section s ∈ R(V') inducing stalkwise bijections. Mathematically true but requires stalk-level sheaf algebra not in Mathlib (toSheafify stalk iso for AddCommGrpCat, presheaf restriction, locally constant germ analysis). Two Aristotle submissions have failed.

2. **`cohomology_vanishing_of_finitelyGenerated_vanishing`** (line 736): Hartshorne 2.9 — cohomology commutes with filtered colimits on Noetherian spaces. Confirmed Mathlib gap: requires LES for derived functors + colimit commutativity for sheaf cohomology. No existing Mathlib API covers this.

Both sorry's are in the dependency chain of `IrreduciblePosVanishing` → `grothendieck_vanishing_aux` → `GrothendieckVanishing`. The main theorem is **not proved** — it depends on unproved propositions. Calling this "modulo Mathlib gaps" is marketing, not mathematics.

## 2. Hidden Axioms

No `admit`, `axiom`, or `native_decide` found. The lakefile disables 5 Mathlib linters (`mathlibStandardSet`, `unusedSimpArgs`, `unnecessarySimpa`, `unusedTactic`, `unreachableTactic`). These suppressions hide dead tactics and redundant simp arguments — potential maintenance debt that becomes real cost on Mathlib bumps.

## 3. Circularity

Well-founded induction on `topologicalKrullDim` (type `WithBot ℕ∞`). The induction hypothesis requires strict `d' < d`. `IrreduciblePosVanishing` obtains `Z` with `dim Z < dim X` via closed subspace dimension drop. No circularity found.

## 4. Hypothesis Audit

Main theorem signature:
```lean
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

- `TopCat.{u}`, `NoetherianSpace`, `n : ℕ`, `h : n > topologicalKrullDim X` — all necessary and standard.
- `Sheaf AddCommGrpCat.{u} X` — standard for Hartshorne's formulation. Could generalize to Grothendieck abelian categories but that's a different theorem.
- The `Subsingleton` conclusion is weaker than `IsZero` but adequate. `topologicalKrullDim` using `WithBot ℕ∞` correctly handles dim = ⊤ (vacuously true).

No unnecessary hypotheses found.

## 5. Mathematical Correctness

Follows Hartshorne III.2.7 faithfully:
- Reduction to irreducible: Finset induction on irreducible components, correct.
- Dim 0 base case: constant sheaf is flasque on irreducible space, correct.
- Irreducible dim ≥ 1: closed immersion SES, pushforward vanishing, kernel vanishing via Steps 3–5, correct strategy.
- FlasqueVanishing: dimension shifting via injective presentations, correct.

The 2 sorry's correspond to Steps 3A (filtered colimit) and 4 (subsheaf classification). Both are mathematically correct statements. No divergence from the standard proof found.

## 6. Code Quality

**P0 — CI broken.** SetupCore.lean fails to compile even at 800K heartbeats. The code is non-functional.

**P1 — Extreme heartbeat overrides:**
- `FlasqueVanishing.lean:53`: `synthInstance.maxHeartbeats 4000000` — **125x the Lean default of 32000**. This is absurd.
- `SetupCore.lean` lines 193, 233, 258, 312, 361: `synthInstance.maxHeartbeats 1600000` — 50x the default.
- `SetupCore.lean:192`: `maxHeartbeats 800000` — 4x the CLAUDE.md limit of 200K.
- 7 additional proofs at `maxHeartbeats 400000`.

Total: **~30 heartbeat overrides** across the codebase. CLAUDE.md says "Never increase maxHeartbeats above 200000" — the codebase openly violates its own discipline.

**P2 — 5 files over 300 lines, 3 over 600:**
| File | Lines |
|------|-------|
| IrreducibleStep.lean | 920 |
| ZeroOutside.lean | 734 |
| FlasqueVanishing.lean | 624 |
| SetupCore.lean | 475 |
| ClosedImmersion.lean | 404 |

IrreducibleStep.lean at 920 lines is nearly unnavigable.

**P3 — Redundant wrapper theorems**: `grothendieck_reduction` and `grothendieck_vanishing_irreducible_pos` in IrreducibleStep.lean are trivial wrappers around `IrreduciblePosVanishing`. Dead indirections.

## 7. Documentation Lies

- **CLAUDE.md line 63**: "Never increase maxHeartbeats above 200000" — ~30 proofs violate this, including one at 4,000,000. The stated discipline is fiction.
- **GrothendieckVanishing.lean line 8**: References "2 sorry's in IrreducibleStep.lean" — accurate count and location. (Fixed from previous critique.)
- **GitHub Pages docs**: completely broken (404). Any claim about documentation deployment is false.
- **CLAUDE.md "Remaining Work" section**: Says "2 sorry's remain" — accurate. Says both are "confirmed Mathlib API gaps" — accurate but potentially misleading; they are still unproved propositions the main theorem depends on.

## 8. Generalization Opportunities

1. **Generalize from AddCommGrpCat to Grothendieck abelian categories** (LOW feasibility). The theorem holds for any Grothendieck abelian category with enough injectives. Current proof uses concrete `AddMonoidHom`, `ULift ℤ`, `zsmul` — rewriting would touch FlasqueVanishing, PushforwardHVanishing, and all stalk arguments. Major refactor.

2. **Strengthen `Subsingleton (Sheaf.H F n)` to `IsZero (Sheaf.H F n)`** (MEDIUM feasibility). `IsZero` is strictly stronger and more useful for downstream consumers. Would require checking that `Sheaf.H` lives in an additive category where `Subsingleton ↔ IsZero`.

3. **Extract FlasqueVanishing as a standalone Mathlib PR** (HIGH feasibility). `FlasqueVanishing`, `isFlasque_of_injective`, `epi_app_of_shortExact_flasque` form a self-contained package. Overlaps with Nugent PR #35790 but could be complementary. Would need heartbeat reduction to Mathlib standards first.

4. **Weaken NoetherianSpace to locally Noetherian** (LOW feasibility). Grothendieck vanishing generalizes to locally Noetherian schemes. Would require significant refactoring of the topological induction.

5. **Extract `sheaf_isZero_of_zero_stalks`** (HIGH feasibility). Basic missing lemma: a sheaf whose stalks are all zero is itself zero. Currently proved inline. Clean Mathlib PR candidate.

## 9. Mathlib Upstreamability

1. **Flasque sheaf package** — `epi_app_of_shortExact_flasque`, `isFlasque_X₃_of_shortExact`, `FlasqueVanishing`. Self-contained, useful. Must reduce heartbeats to default first.

2. **`sheaf_isZero_of_isEmpty`** — sheaf on empty space is zero. Trivial PR.

3. **`closedIncl_unit_stalk_isIso`** — stalk of adjunction unit for closed immersion is iso. Useful for closed immersion theory in Mathlib.

4. **`pushforward_stalk_zero_closedIncl`** — stalk of pushforward along closed immersion vanishes outside the closed set. Basic infrastructure.

All upstream candidates would need heartbeat budgets reduced to Lean defaults and the disabled linters re-enabled to pass Mathlib CI.

## Open Issues

| # | Priority | Issue | Status |
|---|----------|-------|--------|
| 1 | P0 | CI broken — SetupCore.lean timeout at 800K heartbeats | OPEN |
| 2 | P1 | Docs deployment broken (404 on blueprint) | OPEN |
| 3 | P1 | 2 sorry's (load-bearing, Mathlib API gaps) | OPEN |
| 4 | P1 | synthInstance.maxHeartbeats 4,000,000 in FlasqueVanishing.lean | OPEN |
| 5 | P2 | ~30 heartbeat overrides across codebase (limit is 200K) | OPEN |
| 6 | P2 | IrreducibleStep.lean at 920 lines | OPEN |
| 7 | P3 | 5 Mathlib linters disabled in lakefile | OPEN |
| 8 | P3 | Redundant wrapper theorems | OPEN |
| 9 | P4 | GitHub Pages docs 404 | OPEN |

## Verdict: REVISE

The formalization is **non-functional** — CI is red, nothing compiles. The immediate priority is fixing the SetupCore.lean heartbeat timeout that has broken the last 3 commits. Until CI is green, all other issues are moot.

Conditions for CONDITIONAL ACCEPT:
1. CI must be green (all files compile)
2. Both sorry's must be clearly documented as blocking on specific Mathlib PRs
3. No `maxHeartbeats` above 400K (current 4M and 1.6M overrides are unacceptable)
4. No `synthInstance.maxHeartbeats` above 200K

Conditions for ACCEPT:
- All of the above, plus both sorry's resolved
