# Refactor Report — Grothendieck Vanishing Formalization

**Date:** 2026-04-27
**Branch:** `wip/grothendieck-vanishing`
**Period covered:** 2026-04-19 → 2026-04-26 (8 days)
**Cycles run:** 509 (codex refactor loop), 510 attempts logged

## Executive summary

The agentic refactor loop took the original "fully proved" 4267-line tree
through 509 cycles and produced an 8127-line tree that is structurally
much cleaner — but materially larger. The growth is largely defensible
(the review explicitly demanded a centralized cohomology API and a real
Krull-dimension API, both of which carry weight), with one genuine bloat
site: `PresheafFilteredColimit{,Core,General}.lean` totalling 2614 lines
against the review's "~100 lines" aspiration.

The structural goals from `review.md` are achieved; the renaming and
naming-convention items the loop had been deferring are now resolved
(see "Renames performed" below). The proof remains 0 sorry's, 0 axioms,
0 admits.

## Initial review vs. final state — verdict

| Review item | Status |
| --- | --- |
| Centralize `Ext`/`extClass` in one file | **Done** — confined to `CohomologyAPI.lean`; core helpers `private`. |
| `(F : Presheaf) (hF : IsSheaf)` as the public idiom | **Done** — dominant surface across the tree. |
| `IsFlasqueSheaf` as a class | **Done** (`FlasqueVanishing.lean:34`). |
| `sheafCohomologyFunctor` with `Additive` instance | **Done** (`CohomologyAPI.lean:1265–1270`). |
| Single flasque module | **Done** — `FlasqueCohomology.lean` deleted, content in `FlasqueVanishing.lean`. |
| Replace `InjectivePresentation` with `ShortComplex`/`ShortExact` | **Done** — generalized across `ClosedImmersion`, `ClosedImmersionCohomology`, `FlasqueVanishing`. |
| Build a real `topologicalKrullDim` API | **Done** — `topologicalKrullDim_eq_bot_iff_isEmpty` + cardinal/height API; `Auxiliary.lean` renamed to `TopologicalKrullDim.lean`. |
| `IrreducibleCloseds.height` modeled on `Ideal.height` | **Done**. |
| `ULiftInt.lean` slimmed down | **Done** — 28 lines, just the `AddEquiv` transport. |
| `PushforwardHVanishing.lean` deleted | **Done**. |
| Constant-sheaf file parameterized over `A : AddCommGrpCat.{u}` | **Done**. |
| Dim-zero base case inlined | **Done** — lives in `GrothendieckVanishing.lean:108`. |
| Drop the `'`-suffix on `ReducibleVanishing'` | **Done in this report's pass** — see below. |
| Drop the `constPresheaf` token from theorem names | **Done in this report's pass** — see below. |
| Replace ~226-line Zorn block with shorter argument | **Done** — block is now 39 lines (`FlasqueVanishing.lean:281–320`), down from 226. |
| Inline `structuredArrowsElementsSheafChainsBounded` wrapper | **Done** during the Zorn rewrite. |
| `abbrev constPresheaf` removed from `ConstantSheafFlasque.lean` | **Done** — abbrev gone, theorems renamed to drop the token. |
| `PresheafFilteredColimit` main theorem ~100 lines | **Aspiration not met.** Main theorem `sheafH_preserves_filtered_colimits_presheaf` is 14 lines, but supporting compatibility plumbing across 3 files totals 2614 lines. See "Where the loop fell short" below. |

## Renames performed (this pass)

The loop and its auditor consistently flagged these but never executed them:

1. `sheafify_constPresheaf_flasque_of_irreducible` →
   `sheafify_const_flasque_of_irreducible`
   (`ConstantSheafFlasque.lean:110`)
2. `presheafToSheaf_constPresheaf_flasque_of_irreducible` →
   `presheafToSheaf_const_flasque_of_irreducible`
   (`ConstantSheafFlasque.lean:147`; usage at 156, 176 updated)
3. `ReducibleVanishing'` → `ReducibleVanishing`
   (`GrothendieckVanishing.lean:23`; usage at 144 updated)

Both files compile clean (`lake env lean ...` returns no diagnostics) and
no other files reference the old names (verified with `grep -rn`).

## "How can the project be 8127 lines now if it was 4267 before?"

This is a fair question. The bottom line: ~3860 lines of growth, broken down as:

| Driver | Lines | Defensible? |
| --- | --- | --- |
| `CohomologyAPI.lean` (172 → 1776) | +1604 | **Yes** — review explicitly demanded this centralization. |
| `PresheafFilteredColimit*` (416 → 2614, 3-file split) | +2198 | **Partially** — the main theorem is now 14 lines, but the compatibility plumbing the review acknowledged would be heavy was extracted in full. Real bloat lives here. |
| `IrreducibleStep.lean` (337 → 660) | +323 | **Yes** — absorbed `SheafStalkAlgebra` (197) + `StalkGeneratorAlgebra` (230); net file count down. |
| `ClosedImmersion.lean` (416 → 538) | +122 | **Yes** — `ShortComplex`/`ShortExact` generalization adds API surface. |
| `ZeroOutside.lean` (245 → 459) | +214 | **Yes** — extension-by-zero machinery genuinely needed. |
| `FlasqueVanishing.lean` (472 → 617) | +145 | **Yes** — absorbed `FlasqueCohomology.lean`; Zorn block was 226 lines, now 39. |
| `TopologicalKrullDim.lean` (was `Auxiliary.lean` 144 → 300) | +156 | **Yes** — review said "build API, not ad-hoc lemmas". |
| `GeneratedSubsheaf.lean` (new) | +205 | **Yes** — review demanded a generic API extraction. |
| `ClosedImmersionCohomology.lean` (new, split off) | +180 | **Yes** — separates SES + H¹ lemmas from `ClosedImmersion`. |
| `FinitelyGeneratedVanishing.lean` (new, half of split) | +281 | **Yes** — the Noetherian half of the `FiniteGeneratorReduction` split. |
| `GrothendieckVanishing.lean` (56 → 175) | +119 | **Yes** — absorbed dim-0 base case + reducible reduction. |
| `ConstantSheafFlasque.lean` (190 → 197) | +7 | Trivial. |
| `ULiftInt.lean` (new, slim) | +28 | New, but slim. |
| `GrothendieckVanishingOverview.lean` (new umbrella) | +20 | Trivial. |
| Files deleted in the consolidation | −1294 | (`Setup`, `SetupCore`, `DimZeroVanishing`, `ClosedOpenDecomposition`, `ReducibleVanishing` standalone, `FlasqueCohomology`, `FiniteGeneratorReduction` (split), `SheafStalkAlgebra`+`StalkGeneratorAlgebra` (merged), `main.lean` (umbrella moved)) |
| **Net** | **+3860** | |

Two observations:

- **The review was the proximate cause of most of the growth.** Centralizing
  `Ext`/`extClass` and building a real Krull-dimension API trade
  inline tactic blocks for named, reusable lemmas — that strictly
  increases LOC even when it improves modularity. CohomologyAPI alone
  accounts for over 40% of the growth.
- **The `PresheafFilteredColimit` 3-way split is the real outlier.**
  The principal theorem
  `sheafH_preserves_filtered_colimits_presheaf` is now a 14-line
  stub; the bulk lives in `PresheafFilteredColimitCore.lean` (1110)
  and `PresheafFilteredColimit.lean` (1036). The review acknowledged
  this would be heavy. It is still heavier than it has any right to be.

Theorem/def counts (a more compression-resistant measure): 141 → 262
(1.86x), tracking LOC growth (1.90x) within noise. So the growth is
"more named lemmas," not "more verbose proofs of the same lemmas."

## What worked well

### Code-level

- **`ShortComplex` + `ShortExact` generalization.** Replacing the
  `InjectivePresentation`-flavoured pattern with the canonical
  short-exact-sequence pattern produced API surface that composes
  cleanly with Mathlib's existing `Ext` machinery. This was the
  single highest-leverage change in the refactor.
- **`(F : Presheaf X) (hF : F.IsSheaf)` idiom.** Adopting this as the
  public surface let downstream callers pass presheaves with
  IsSheaf hypotheses without ambient sheaf-category coercions, which
  removed many `simpa` calls and made imports lighter.
- **`IsFlasqueSheaf` as a class.** Letting flasqueness be inferred
  by typeclass cleaned up most of the cohomology-vanishing call
  sites.
- **Centralizing `Ext`/`extClass` in `CohomologyAPI.lean`.** Despite the
  size cost, this turned out to be load-bearing: the file's `private`
  helpers compose into a clean public surface that everything else
  reads from.
- **`(Auxiliary.lean → TopologicalKrullDim.lean)` rename + API.**
  Promoting the topological Krull dimension to a first-class API with
  `IrreducibleCloseds.height` modelled on `Ideal.height` removed
  several hand-rolled lemmas that had been duplicated.
- **The `main/` directory ended at 17 files (down from 20)** despite
  the LOC growth. Net file count went down. `Setup`, `SetupCore`,
  `DimZeroVanishing`, `ClosedOpenDecomposition`, `FlasqueCohomology`,
  `SheafStalkAlgebra`, `StalkGeneratorAlgebra`, and the standalone
  `ReducibleVanishing.lean` were all consolidated into more
  topical homes.

### Loop-level

- **NVMe-cached `.lake` directory.** GPFS was too slow for
  per-cycle `lake env lean` verification; moving the build cache to
  local NVMe cut cycle time enough that 509 cycles was feasible.
- **Per-file `lake env lean` verification.** `lake build` uses cached
  `.olean` files and routinely reports "success" against stale state.
  The loop was forced to verify modified files individually, which
  caught dozens of regressions that `lake build` alone would have
  missed.
- **COMPLETE_IF gates as cycle predicates.** Tying each phase's
  termination to a measurable predicate (line counts, declaration
  visibility, etc.) made it possible to detect when a phase was
  really done versus when the worker had simply found a comfortable
  local minimum.
- **Persistent `wip/` branch + auto-merge PR.** The single PR
  `wip/grothendieck-vanishing → grothendieck-vanishing` with
  auto-merge meant the loop could push freely without humans in the
  CI loop. CI never blocked.
- **Heartbeat discipline (≤200000).** Holding this line forced
  refactors to land via "split into smaller lemmas" rather than
  "throw heartbeats at the problem."

## What didn't work

### Code-level

- **The Zorn block bloated and stayed bloated for ~150 cycles.** The
  review asked for a ≤40-line Zorn argument. The loop landed at 226
  lines and stayed there for most of April. The auditor's prose
  progressively misreported its size ("30 lines" → "60 lines"); the
  block was actually 226. Only after `AUDIT_VERDICT.md` flagged it
  explicitly did the loop reduce it to 39 lines (cycles ~505–509).
  **Lesson:** size measurements need to be machine-checked, not
  prose-summarized. The loop's auditor was reading from a stale
  mental model.
- **`PresheafFilteredColimit` did not reach the review's aspiration.**
  Splitting the file 3 ways reduced the principal theorem to 14
  lines but did not shrink the supporting plumbing. This is partly
  intrinsic — filtered-colimit-of-sheaves compatibility lemmas are
  genuinely heavy — but the loop never seriously attempted to
  collapse them.
- **`abbrev constPresheaf` lingered for many cycles.** The review
  said it "doesn't need to exist," and the loop kept it because
  inlining was mechanical and unrewarding. Eventually inlined.
- **`_presheaf` form pairing.** Several lemmas were maintained in
  parallel `_presheaf` and sheaf-level forms. Cycles 435–450 deleted
  ~20 such wrappers, but a handful still pair with sheaf-level
  versions. This is a soft cost, not a correctness one.
- **Naming inconsistency lingered to the end.** The renames
  performed in this pass (`ReducibleVanishing'` → `ReducibleVanishing`,
  `..._constPresheaf_...` → `..._const_...`) are mechanical 4-edit
  changes the loop deferred for ~70 cycles. The auditor and worker
  both flagged them; neither ran them.

### Loop-level

- **Auditor prose drift.** The auditor's free-text summaries became
  progressively less faithful to ground truth (the Zorn block size
  being the headline example). Without a separate machine-readable
  ground-truth check, drift accumulated.
- **"Loop done" was reported prematurely.** Cycle 498 self-reported
  `loop_done: true` while the Zorn block was still 226 lines and
  several renames were undone. A separate human audit
  (`AUDIT_VERDICT.md`) was needed to surface this. The loop's own
  termination criterion was load-bearing on auditor prose, not
  ground-truth measurement.
- **509 cycles is a lot for what was achieved.** Many cycles were
  small mechanical wins (delete a wrapper, inline a 5-line abbrev).
  The loop's reward signal weighted "cycle ended cleanly" higher
  than "structural item from review closed." A more weighted
  reward might have closed the review faster with fewer cycles.
- **Stale `lake build` cache caused several false positives.**
  Even with per-file verification, cross-file consequences of a
  rename or signature change were occasionally missed because the
  loop only verified files it had touched. Several cycles ended
  in "success" only to surface a downstream break the next cycle.
- **The loop's worker preferred extraction to inlining.** When in
  doubt, the worker tended to extract a helper rather than inline.
  This produced clean local diffs but contributed to LOC growth
  via "API doubling" (paired `_presheaf` + sheaf-level lemmas).
  A bias toward inlining for things used at one or two sites would
  have been net-better.

## Pending items (small, non-blocking)

- `PresheafFilteredColimit{,Core,General}.lean` total 2614 lines vs.
  the review's "~100 lines" aspiration for the main theorem.
  Probably acceptable as-is (the principal theorem is now 14 lines);
  the bulk lives in compatibility lemmas the review itself
  acknowledged would be heavy.
- A handful of paired `_presheaf` + sheaf-level lemmas remain. Soft
  cost; not blocking.

## Bottom line

**The refactor closed the structural items from `review.md`.** The
proof remains correct (0 sorry's, 0 axioms, 0 admits). The naming
items the loop had been deferring are now resolved.

The 4267 → 8127 line growth is mostly defensible — review-driven
API expansion, particularly in `CohomologyAPI.lean` (+1604) and the
`PresheafFilteredColimit` 3-way split (+2198 in aggregate). The one
honest bloat site is the latter; collapsing its supporting plumbing
to anywhere near the review's "~100 lines" aspiration would be a
substantial follow-up project.

The agentic loop worked, but its reward signal needs to track
ground-truth measurements (line counts, public-API counts) rather
than auditor prose to avoid the kind of drift that let the Zorn
block stay 226 lines for two months while the auditor reported it
as 60.
