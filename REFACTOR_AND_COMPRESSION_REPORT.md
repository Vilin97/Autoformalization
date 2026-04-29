# Agentic Refactor and Compression of a Lean 4 Formalization of Grothendieck Vanishing

**Date:** 2026-04-29
**Branch:** `grothendieck-vanishing`
**Period covered:** 2026-04-16 → 2026-04-29 (13 days, 459 commits)
**Loops run:** 1 refactor loop (509 cycles), 1 compression loop (86 cycles), 1 manual audit pass
**Theorem:** Grothendieck vanishing for sheaves of abelian groups on Noetherian topological spaces

## Abstract

We report on the second supervision cycle of an AI-driven Lean 4 formalization. Starting from a "fully proved" 4 200-line tree judged unidiomatic by a code review, we ran two automated loops back-to-back: a *refactor loop* (509 cycles, 8 days, gpt-5.5 worker + claude-opus-4-7 evaluator) that addressed the review's structural items at the cost of nearly doubling LOC (4 267 → 8 127), and a *compression loop* (86 cycles, 2 days, same models, with one new agent) that pulled the tree back to 4 998 raw / 4 087 normalized LOC — below the original size, while preserving all the refactor's API improvements and 0 sorry's / 0 axioms. We document the loop architectures, the seven principles that drove compression, the structural opportunities that yielded the largest deltas, and a taxonomy of failure modes — *auditor prose drift*, *premature loop-done*, *helper extraction bias*, *API doubling* — that argue for machine-checked metrics over agent self-reports as the loop's primary control signal.

## 1. Introduction

The previous arxiv report [1] documented the *first* supervision cycle on this codebase: Gemini DeepThink + Claude Code + Aristotle, ten days to a 10K-line proof of the Vlasov-Maxwell-Landau equilibrium. That paper concluded with a brief acknowledgement that the resulting Lean was "compilable but unidiomatic" — written in a style that violated several Mathlib conventions and that an experienced reviewer would refuse to upstream.

This report covers what happened next. After the first paper we requested a code review of a different but representative formalization — Grothendieck vanishing for sheaves on Noetherian topological spaces (the "Clawristotle" line, hence the repo). The review (Section 5) asked for nine large structural changes: rename uninformative files, split files mixing different topics, centralize the cohomology API, replace `(F : Sheaf …)` with `(F : Presheaf) (hF : IsSheaf F)` as the public idiom, generalize `InjectivePresentation` arguments to `ShortComplex`/`ShortExact`, build a real Krull-dimension API, replace "if A=0 then B=0" with "A ≅ B", and so on. We executed these as a single agentic loop (Section 4.1), audited the result (Section 4.2), and discovered the loop had over-applied one of the review's recommendations and grown the tree from 4 200 to 8 127 lines — about half the growth was the review's fault and half the loop's. We then ran a *compression loop* (Section 4.3) with a different metric (normalized LOC, with a per-cycle ratchet gate) and a fifth specialized agent (gate-repair) that pulled the tree back to 4 998 lines while keeping every structural item the refactor had achieved. Total wall-clock from review delivery to second commit was 13 days.

The contribution is twofold. First, a worked example of *adversarial reviewer-driven refactoring*: an LLM-orchestrated loop following a human code review can address structural items at scale (we closed 17 of 19 review items) but tends to *expand* the codebase as it adds named API surface; a follow-up minimization loop is a clean way to reclaim the bloat without losing the structure. Second, an architecture pattern — the five-agent loop with mechanical metric gates and a specialized gate-repair agent — that we believe is more robust than the four-agent design from the first paper, particularly the introduction of a per-cycle *ratchet* on a metric (normalized LOC) the worker cannot game.

## 2. The Theorem

The proof we worked on is *Grothendieck vanishing*: for any sheaf of abelian groups $F$ on a Noetherian topological space $X$,

$$H^n(X, F) = 0 \quad \text{for all } n > \dim X$$

where $\dim X$ is the topological Krull dimension. The proof is the standard one (Hartshorne Proposition III.2.7): induction on $\dim X$, reducing first to the irreducible case via a Mayer-Vietoris-type argument over closed subsets, then to the case where $F$ is a constant sheaf via a finitely-generated subsheaf colimit, then closing by showing constant sheaves on irreducible spaces are flasque. The induction calls into a stack of supporting facts: that flasque sheaves have vanishing higher cohomology; that filtered colimits commute with sheaf cohomology on Noetherian spaces; that closed-immersion pushforwards preserve cohomology; that the irreducible-step reduction lifts a section through the closed/open decomposition. None of these were in Mathlib at the start of the project.

The first-pass formalization (predating this report) introduced the proof at ~4 200 lines spread over 19 files. It was correct (`#print axioms` showed only `propext`, `Quot.sound`, `Classical.choice`) but unidiomatic; the review (Section 5) is its diagnosis.

## 3. Tools

Three tool layers, each contributing differently to the refactor and the compression. The first paper [1] established the layer-1 setup; layers 2 and 3 are new in this work.

**Layer 1 — Lean 4 + Mathlib + Lean LSP MCP.** The proof itself is in Lean 4 against Mathlib `v4.28`. We use the Lean LSP MCP server to expose `lean_goal`, `lean_diagnostic_messages`, `lean_loogle`, `lean_state_search`, `lean_hammer_premise`, and friends to the agents. Search-tool usage is rate-limited (3-10 calls / 30s) which forces the agents to plan their search budget rather than thrash.

**Layer 2 — Codex CLI as the loop driver.** We use OpenAI's `codex` CLI (gpt-5.5) as the worker and planner inside the loop. The CLI is invoked with a single prompt + repo access; it can call shell, Lean LSP, and Mathlib search tools, and writes its output to a file the loop driver picks up. This is the first paper's Claude Code role, but with a different model and a less interactive interface. The choice was driven by cost (gpt-5.5 is cheaper at this token volume) and by the fact that the loop is fully automated — there is no human-in-the-loop conversation for which Claude Code's UX advantage matters.

**Layer 3 — Claude Opus 4.7 (1M context) as the evaluator/auditor.** Where the worker writes code, the evaluator and auditor *read* it and produce structured JSON judgements (cycle pass/fail, score in [-2,+2], list of completed checklist items, `loop_done` boolean). We use Claude for these because the JSON discipline and verification workload is more failure-sensitive than the worker's, and Claude has been less prone to hallucinating file references (a problem the auditor in particular cannot afford). Cost difference is ~3× per-token but evaluator runs are ~4× shorter than worker runs, so net cost ratio is roughly 1:1.

The orchestration code (`scripts/codex_refactor_loop.py`, `scripts/codex_compress_loop.py`) is a single ~1 100-line Python driver in each phase, plus seven prompt files (`scripts/prompts/{codex,compress}_*.md`). The driver reads/writes a flat persistent state directory (`.refactor-state/`, then `.compress-state/`); the prompts are model-readable but version-controlled, so changes to the loop's behavior are reviewable diffs.

## 4. Process

### 4.1 Phase 1 — Refactor loop (cycles 1–509, 2026-04-16 → 2026-04-26)

The refactor loop was a four-agent pipeline:

| Agent | Role | Model | Timeout |
| --- | --- | --- | --- |
| Auditor | Refresh the work checklist when it goes empty | claude-opus-4-7 | 30 min |
| Planner | Pick one target from the checklist + audit | gpt-5.5 | 30 min |
| Worker | Modify code to address the target | gpt-5.5 | 3 hr |
| Evaluator | Score the change and mark items complete | claude-opus-4-7 | 30 min |

Per-cycle gates were strict (every modified `.lean` file must compile under `lake env lean`; `lake build` runs if any file is added/deleted/renamed; sorry count cannot increase) but there was *no LOC gate*. The loop's reward signal weighted "cycle ended cleanly" higher than "structural item from review closed", which turned out to be load-bearing for the bloat that followed.

The loop ran for 8 days and 509 cycles. Sixteen of the review's nineteen items closed during this period: the Auxiliary/Setup/SetupCore renaming, the FlasqueCohomology consolidation, the FiniteGeneratorReduction split, the centralization of `Ext`/`extClass` in `CohomologyAPI.lean`, the `(F : Presheaf) (hF : IsSheaf)` idiom adoption, the `InjectivePresentation → ShortComplex` generalization, the `topologicalKrullDim` API build-out, the `IrreducibleCloseds.height` analogue of `Ideal.height`, the `ULiftInt.lean` slim-down, and so on. Three items were left for a manual pass: the Zorn block in `FlasqueVanishing.lean` had bloated to 226 lines instead of contracting to ≤40 lines as the review asked; two cosmetic renames (`ReducibleVanishing'` → `ReducibleVanishing`, `..._constPresheaf_...` → `..._const_...`) were repeatedly flagged by the auditor and never run; and the `PresheafFilteredColimit` cluster did not shrink to the review's ~100-line aspiration.

The headline number is the LOC growth: 4 200 → 8 127 raw lines, +93%. The growth distribution was concentrated in two files. `CohomologyAPI.lean` went from non-existent to 1 776 lines (the review explicitly demanded this centralization, so growth is defensible). `PresheafFilteredColimit{,Core,General}.lean` totalled 2 614 lines for what the review said "should not need to be more than ~100 lines" for the main theorem alone. Growth elsewhere was modest and tracked review demands closely.

### 4.2 Phase 2 — Manual audit (2026-04-26)

Cycle 498 self-reported `loop_done: true` while the Zorn block in `FlasqueVanishing.lean` was still 226 lines — the auditor's prose summary, repeated unmodified across cycles, claimed the block was "30 lines" or "60 lines" depending on the cycle. We wrote a one-page hand audit (`AUDIT_VERDICT.md`) measuring the block directly:

| Range | Lemma | Lines |
| --- | --- | --- |
| 110–114 | `Under` abbrev | 5 |
| 115–235 | `under_exists_extension_containing` | **121** |
| 237–307 | `under_chain_upper_bound` | 71 |
| 308–314 | `structuredArrowsElementsSheafChainsBounded` (redundant wrapper) | 7 |
| 316–333 | `under_maximal_eq_top` | 18 |
| | **Total** | **222** |

The audit re-opened the loop with a `Phase 17` checklist item: replace lines 108–333 with the shorter Zorn argument from the user's PR. Cycles 499–509 closed it (final block: 39 lines). REFACTOR_REPORT.md was committed at the end of this pass.

The audit's diagnosis — that the loop had been miscounting the Zorn block for ~150 cycles because no agent measured it directly — became the single most important input to the compression loop's design: every claim the loop makes about size must be checkable mechanically.

### 4.3 Phase 3 — Compression loop (cycles 1–86, 2026-04-27 → 2026-04-29)

The compression loop was a five-agent pipeline. Four agents were the same as the refactor loop, with a fifth added:

| Agent | Role | Model | Timeout |
| --- | --- | --- | --- |
| Auditor | Refresh checklist; declare `loop_done` when audit reports nothing left | claude-opus-4-7 | 30 min |
| Planner | Pick one target from the *fresh* per-cycle audit | gpt-5.5 | 30 min |
| Worker | Modify code to compress | gpt-5.5 | 3 hr |
| **Gate-repair worker** | Salvage a cycle if mechanical gates fail | gpt-5.5 | 1 hr |
| Evaluator | Score the change and mark items complete | claude-opus-4-7 | 30 min |

The new agent is *gate-repair*. Where the refactor loop's response to a gate failure was to revert and record a regression, the compression loop's response is: hand the diff and the gate failure to a specialized worker that may patch around it (e.g., introduce a missing lemma the worker forgot, or re-establish a `simp` invariant that broke). If repair fails, only then do we revert. In our run, gate-repair was invoked exactly *once* — cycle 84 — and it succeeded; the design is cheap to keep available even if rarely used.

The loop runs the following per-cycle pipeline:

```
1. raw_loc_total() → < 5000? exit.
2. has_unchecked_or_wip_items() → no → run_auditor() → loop_done? exit.
3. run_audit(cycle)              # fresh audit, non-fatal if it crashes
4. run_planner(cycle, history)   # writes compress_strategy.md
5. promote_to_wip()               # flip planner's targets to "- [>]"
6. run_worker(cycle, strategy)
7. compute sorry_after, loc_after
8. check_gates(...)               # sorry, compile per-file, lake build, LOC ratchet
9. gate failed?
   ├── run_gate_repair()
   ├── check_gates() again
   └── still failed? → git checkout --. → record_gate_failure() → raise
10. run_evaluator(...)            # JSON: progress_score, completed_task_lines, etc.
11. mark_completed_tasks(...)
12. git add -A && git commit && git push
13. append_history(record)
```

The structurally-important addition over the refactor loop is step 8's *normalized-LOC ratchet*: every cycle's commit must strictly decrease normalized LOC, where "normalized" strips block and line comments, ignores blank lines, and *splits* tactic-stacked lines (`tac1; tac2` is two units, not one). The metric is in `scripts/normalized_loc.py` (132 lines) and is computable in <1s; the planner gets it in the audit, the evaluator independently re-runs it for verification, the gate uses it as the ratchet. Because the metric ignores comments and blank lines, the worker cannot pass the gate by deleting them. Because it splits stacked tactics, the worker cannot pass by golfing onto one line. Real compression — deletion, inlining, structural rewrite, proof shortening that actually shortens the proof — is the only way through.

The loop's behavior is governed by seven principles in `.compress-state/principles.md` (88 lines). They are durable across cycles; the planner, worker, evaluator, and gate-repair agent all read them.

| # | Principle | Where it bit |
| --- | --- | --- |
| 1 | Real compression, not metric gaming | Evaluator vetoed two cycles that lowered raw LOC only by deleting comment blocks. |
| 2 | **Sheaf, not Presheaf+IsSheaf** — revert the previous refactor's over-application | This is Phase 1 of the loop and the largest LOC delivery: cycles 1–10 reverted ~30 theorems and deleted the `_presheaf` bridge wrappers. Saved ~1 700 norm LOC. |
| 3 | Inline single-use helpers | Saved ~250 norm LOC across 18 cycles. The worker had a strong bias toward extraction; principle 3 + evaluator enforcement reverses it. |
| 4 | Delete unused declarations | A Lean metaprogram (`scripts/unused_decls.lean`) computes the set of public decls not transitively reachable from `grothendieck_vanishing`. Audit lists them; worker deletes; cascade. |
| 5 | Replace ad-hoc proofs with Mathlib lemmas | Used ~7 times. `lean_state_search` and `lean_loogle` are the access points. |
| 6 | Hard mechanical gates | The ratchet is here. |
| 7 | Structural opportunities backlog | When the mechanical phases run dry, the loop consults `.compress-state/structural_ideas.md` (six cross-file initiatives sized as single cycles). Four of six shipped. |

The audit step (`scripts/compress_audit.py`, 235 lines) emits four sections each cycle: per-file LOC, the unused-decl list (computed by running a Lean metaprogram, ~30s), the remaining `_presheaf` declarations (regex over the source), and Phase-5 structural-idea status (auto-detected predicates, e.g., "does `class IsFlasqueSheaf` still exist?"). The planner receives this fresh; it does not look at the previous cycle's audit. This was a deliberate design choice driven by Phase 2's diagnosis: stale audit data is the single largest source of agent miscalibration.

## 5. The Original Review

The review preceding the refactor loop is preserved verbatim in the project as `review.md`. We reproduce its top-level structure and the items the loop closed. (Per-file commentary on internal proofs is omitted here for brevity; see the file.)

**Cross-cutting items:**
1. *Centralize `Ext`/`extClass` in one file.* The review observed that `Ext` was leaking through `PresheafFilteredColimit.lean`, `ClosedImmersionCohomology.lean`, and `FlasqueVanishing.lean`. Asked for a `CohomologyAPI.sheafH_subsingleton_of_injective` wrapper and downstream rewrites.
2. *`(F : Presheaf) (hF : IsSheaf F)` should be the primary idiom.* The review flagged ~32 `*_presheaf` / sheaf-level lemma pairs in `CohomologyAPI.lean` and asked that the presheaf-with-hypothesis form be the primary, with sheaf wrappers being thin `simpa` shims.
3. *Generalize `InjectivePresentation` arguments to `ShortComplex`/`ShortExact`.* Many results that took an injective presentation only used `ip.shortComplex`; these should take `(S : ShortComplex (TopCat.Sheaf …))` and `(hS : S.shortExact)` directly, with `[S.X₂.Injective]` only added where actually needed.
4. *`PushforwardHVanishing` and `sheafH_preserves_filtered_colimits` prove "if A=0 then B=0" when they should prove "A ≅ B".* The more general result is significantly more useful; the proofs are essentially the same.

**File-structural items:** `Auxiliary.lean` is not descriptive; rename to `TopologicalKrullDim.lean` and build a real API there. `FlasqueVanishing.lean` and `FlasqueCohomology.lean` should be one file. `FiniteGeneratorReduction.lean` is a bad name and mixes general-colimits-of-sheaves work with the Noetherian case; split. `ReducibleVanishing.lean`, `ClosedOpenDecomposition.lean`, `DimZeroVanishing.lean` are short single-purpose files that should be inlined into `GrothendieckVanishing.lean`. `Setup.lean` is a single random lemma that should be folded.

**Per-file content items:** The Zorn argument in `FlasqueVanishing.lean` was hand-rolled and ~100 lines; the user's own PR has a ≤40-line version using Mathlib's `zorn_*` directly — the review asked the agent to copy it. `closedIncl_counit_isIso` should be derived from `pushforward fully faithful` rather than via a 150-line stalk calculation. Numerous specific lemmas were flagged as "doesn't need to be its own theorem" or "too specific; this should be an instance/inferred". The `class IsFlasqueSheaf` was correctly introduced but pervasively unused; the review asked that flasqueness be inferred via typeclass.

**The loop closed 17 of 19 items by 2026-04-26.** The two exceptions were the Zorn block (closed in cycles 505–509 after manual audit pressure) and the `PresheafFilteredColimit` ~100-line aspiration (not closed; the cluster's main theorem became 14 lines but supporting plumbing remained ~2 600 lines).

## 6. Statistics

### 6.1 Headline numbers — the full arc

| Snapshot | Raw LOC | Norm LOC | Files in `main/` | Sorry's | Date |
| --- | --- | --- | --- | --- | --- |
| Pre-refactor (`dcff8ee`) | 4 208 | — | 19 | 0 | 2026-04-16 |
| Post-refactor (`a5756f5`) | 8 127 | ~6 900 | 17 | 0 | 2026-04-27 |
| Post-compression (`85437ea`) | **4 998** | **4 087** | **15** | **0** | 2026-04-29 |
| Δ refactor | +3 919 (+93%) | — | −2 | 0 | |
| Δ compression | **−3 129 (−39%)** | — | −2 | 0 | |
| Net (both) | **+790 (+19%)** | — | −4 | 0 | |

Reading the rows: the two loops together added 790 lines net, in exchange for closing 17 review items, a centralized cohomology API, a topological-Krull-dimension API analogous to `Ideal.height`, four file consolidations, and the removal of two whole files (`ULiftInt.lean`, `ZeroOutsideFinset.lean`) that the review flagged as carrying their own weight in unrewarding boilerplate.

### 6.2 Per-file evolution

LOC by file across the three snapshots, sorted by current size:

| File | Pre-refactor | Post-refactor | Post-compression | Δ refactor | Δ compression |
| --- | ---: | ---: | ---: | ---: | ---: |
| `CohomologyAPI.lean` | (new) | 1 776 | 782 | +1 776 | **−994 (−56%)** |
| `PresheafFilteredColimitCore.lean` | (new) | 1 110 | 493 | +1 110 | **−617 (−56%)** |
| `IrreducibleStep.lean` | 337 | 660 | 482 | +323 | −178 (−27%) |
| `ClosedImmersion.lean` | 349 | 538 | 474 | +189 | −64 (−12%) |
| `PresheafFilteredColimit.lean` | 416 | 1 036 | 447 | +620 | **−589 (−57%)** |
| `ZeroOutside.lean` | 245 | 459 | 428 | +214 | −31 (−7%) |
| `FlasqueVanishing.lean` | 481 | 617 | 411 | +136 | −206 (−33%) |
| `PresheafFilteredColimitGeneral.lean` | (new) | 468 | 382 | +468 | −86 (−18%) |
| `TopologicalKrullDim.lean` (was `Auxiliary.lean`) | 173 | 300 | 278 | +127 | −22 (−7%) |
| `FinitelyGeneratedVanishing.lean` | (new, ½ of split) | 281 | 206 | +281 | −75 (−27%) |
| `ConstantSheafFlasque.lean` | 189 | 197 | 174 | +8 | −23 (−12%) |
| `GeneratedSubsheaf.lean` | (new) | 205 | 161 | +205 | −44 (−21%) |
| `GrothendieckVanishing.lean` | 56 | 175 | 137 | +119 | −38 (−22%) |
| `ClosedImmersionCohomology.lean` | (new, split off) | 180 | 124 | +180 | −56 (−31%) |
| `GrothendieckVanishingOverview.lean` | (new) | 20 | 19 | +20 | −1 (−5%) |
| Files deleted between snapshots | — | — | — | (8 deleted) | (2 deleted) |

The compression's top three contributors — `CohomologyAPI`, `PresheafFilteredColimitCore`, and `PresheafFilteredColimit` — are exactly the three files the refactor over-grew, and exactly the three the review identified as "the AI didn't recognize this is functor-category territory and over-built a special-cased API". The compression's −56%/−56%/−57% on these files vindicates the review's diagnosis: the over-build was undone, not the structural work itself.

### 6.3 Compression cycles — categories and yields

We classified each of the 86 compression cycles by the dominant action it took. Categories: SHEAF_REVERT (delete a `_presheaf` bridge wrapper or revert a `Presheaf+IsSheaf` argument pair to a bundled `Sheaf`), UNUSED_PRUNE (delete a public declaration not reachable from `grothendieck_vanishing`), HELPER_INLINE (inline a 0–1-call helper), GOLF (shorten a proof body without changing its statement), STRUCTURAL (file merger, class → def collapse, cross-file move).

| Category | Cycles | Norm LOC saved | Avg / cycle |
| --- | ---: | ---: | ---: |
| SHEAF_REVERT | 35 | −1 782 | −51 |
| GOLF | 19 | −564 | −30 |
| HELPER_INLINE | 18 | −245 | −14 |
| UNUSED_PRUNE | 10 | −156 | −16 |
| STRUCTURAL / OTHER | 4 | −155 | −39 |
| **Total** | **86** | **−2 902** | **−34** |

Sheaf reversion delivered 61% of total savings. This is the *one* item in the review the previous refactor over-applied — and it took an entire follow-up loop to undo. It is the largest single design lesson of the project (Section 7.1).

The five biggest individual cycles were:

| Cycle | File | LOC | Description |
| --- | --- | --- | --- |
| 2 | `CohomologyAPI.lean` | −501 | Sheaf-revert successor-map + H¹ cokernel iso + H¹ vanishing clusters; delete `_presheaf` wrappers and update cross-file callers. |
| 1 | `CohomologyAPI.lean` | −350 | Bundle the successor connecting iso cluster onto `ShortComplex (Sheaf …)`; delete two `_presheaf` wrappers. |
| 10 | `PresheafFilteredColimit{,Core}.lean` | −337 | Sheafify the filtered-colimit boundary layer; delete ~10 `_presheaf` shim declarations and rework degree-0/1/successor comparison-iso proofs. |
| 7 | `CohomologyAPI.lean` | −148 | Sheaf-revert the dimension-shift cluster. |
| 3 | `FlasqueVanishing.lean` | −103 | Sheaf-revert the flasque-vanishing cluster; delete the `sheafShortComplexOfPresheaf` bridge. |

The first 10 cycles delivered −1 738 LOC (60% of total) at an average of −174 LOC each. Cycles 11–31 delivered −800 LOC at an average of −38 each. Cycles 32–86 delivered −364 LOC at an average of −7 each — the natural diminishing-returns curve of any minimization process.

LOC distribution by cycle size:

- **Big wins** (≥50 LOC saved): 9 cycles, −1 765 LOC (61% of all savings).
- **Medium** (10–50 LOC): 58 cycles, −1 035 LOC (36%).
- **Small** (1–10 LOC): 18 cycles, −102 LOC (3%).
- **Zero-delta** (no LOC change but other gates passed): 1 cycle.

### 6.4 Human supervision

Unlike the first paper [1] — where 229 interactive Claude Code prompts drove the formalization day-to-day — this project was almost entirely loop-driven. The two automated loops together accounted for ~3 000 in-loop LLM invocations (5 agents × 595 cycles ≈ 2 975 calls if every cycle ran every agent; the actual count is somewhat lower because audit was non-fatal and gate-repair fired only once). The script `scripts/count_human_prompts.py` extracts human prompts from Claude Code session transcripts:

| Source | Human prompts | Period |
| --- | ---: | --- |
| Local Claude Code (workstation, 3 sessions) | 17 | 2026-04-27 → 2026-04-29 (post-refactor) |
| Hyak (klone-login:/gscratch/amath/vilin/Clawristotle) | TBD | (compression loop ran here; transcripts not yet pulled) |

The local count covers only the post-refactor *supervisory* work — reading the audit, kicking off the compression loop, drafting this report. The refactor loop ran on klone over Apr 16–26 and its prompt logs (if any survived in `~/.claude/projects/...` on that host) need to be counted there. To complete the table run `python3 scripts/count_human_prompts.py ~/.claude/projects/-gscratch-amath-vilin-Clawristotle` on klone-login.

The lesson is that *human prompt count is no longer a useful proxy for project effort* once the system is loop-driven. A better proxy would be the number of *durable artifacts* the human authored: the original review (~6 KB), `principles.md` (88 lines), `structural_ideas.md` (160 lines), `AUDIT_VERDICT.md` (78 lines), and the seven prompts in `scripts/prompts/compress_*.md` (~370 lines total). Total ≈ 700 lines of human-authored loop input — a small fraction of the 459 commits the loop produced.

### 6.5 Structural ideas (Phase 5)

Six cross-file structural opportunities were enumerated in `.compress-state/structural_ideas.md` at the start of compression:

| # | Idea | Yield estimate | Shipped |
| --- | --- | --- | --- |
| 1 | Sheafify the entire `PresheafFilteredColimit*` cluster | 400–700 | ✅ (largest single delivery; ~350 LOC over cycles 5, 10) |
| 2 | Collapse `class IsFlasqueSheaf` to `def` | 30–50 | ✅ |
| 3 | Inline / Mathlib-replace `ULiftInt.lean` | 20–28 | ✅ (file deleted) |
| 4 | Merge `ZeroOutsideFinset.lean` into `ZeroOutside.lean` | 10–20 | ✅ (file deleted) |
| 5 | Upstream `TopologicalKrullDim.lean` to Mathlib | 150–200 | ❌ (out-of-band) |
| 6 | Aristotle auto-prover golf on body/sig outliers | 200–500 | ❌ (deferred) |

Idea 5 is gated on a Mathlib PR review cycle and was correctly excluded from the loop. Idea 6 was deferred until Idea 1's rewrites stabilized; it is the most natural follow-up.

## 7. Lessons Learned

### 7.1 *API doubling* is the failure mode of "be generous with named lemmas"

The refactor's biggest single design flaw was producing 32 pairs of `_presheaf`-suffixed and sheaf-level lemmas in `CohomologyAPI.lean`. Every pair existed because the worker, having learned from the review that the `(F : Presheaf) (hF : IsSheaf F)` form was preferred for some lemmas, applied the form *everywhere* and then preserved the older sheaf-level lemma as a thin wrapper for callers it didn't want to update. Net effect: the review's "many lemmas should take Presheaf+IsSheaf" was read as "every lemma must offer both forms", which doubled `CohomologyAPI`'s surface area and accounted for ~60% of the compression loop's eventual workload.

The fix in compression was Principle 2 ("Sheaf, not Presheaf+IsSheaf") with explicit evaluator reward language: REWARD sheaf-reversion cycles. REJECT new lemmas that re-introduce the pair. The lesson is that workers driven by a review do not interpolate — they extrapolate. If the review says "X is sometimes better", the worker hears "X is always better", and you need an opposing signal for the cases it isn't.

### 7.2 *Auditor prose drift* is what kills self-reporting loops

The Zorn block in `FlasqueVanishing.lean` was 226 lines for ~150 cycles. The auditor's prose summary, generated each cycle and read by the planner, claimed the block was "30 lines" or "60 lines" depending on the cycle. The number was inherited from the previous summary and never re-measured — the auditor was summarizing its own previous output, not the source. The loop's `loop_done: true` decision at cycle 498 was directly downstream of this drift.

The fix was the per-cycle audit script (`scripts/compress_audit.py`): a fresh Python pass that recomputes raw LOC, normalized LOC, the unused-decl list (via a Lean metaprogram), the `_presheaf` decl list, and per-file body length each cycle. The planner reads the script's output, not the auditor's prose. The auditor's role is reduced to extending the checklist when it goes empty; everything else is mechanical. After this change, the loop never again miscounted any quantity it acted on.

The general principle: **agent self-reports decay; mechanical scans do not**. Any quantity the loop conditions on must be recomputed from source on demand, not maintained as text the agent edits.

### 7.3 *Premature loop-done* is the symmetric failure to 7.2

Cycle 498 of the refactor loop self-reported `loop_done: true` while three review items were demonstrably open. The trigger was a checklist item being marked `[x]` based on the worker's report ("I closed Phase 12") rather than a verification step ("does the property the phase asserts now hold?"). Once enough items were marked complete, the auditor concluded the loop was done.

The compression loop's defense is COMPLETE_IF predicates: each checklist item carries an optional shell command that the loop runs to verify completion. E.g., for "delete `_presheaf` wrapper X", `COMPLETE_IF: ! grep -q "theorem X_presheaf" Aristotle/...lean`. Items marked `[x]` by the evaluator are re-checked by the script before the auditor declares `loop_done`. In our run no item was ever falsely marked complete after this gate was added.

### 7.4 *Helper extraction bias* is intrinsic to the worker

The worker, when in doubt, extracts a helper. This is a defensible style preference for human code — small focused functions with descriptive names — but in proof code it is *anti-compression*: a helper costs a signature, a docstring, two newlines of separation, and a marshaling line at the call site, often more than the body it factors out. We saw this both during refactor (where the worker introduced ~40 single-call helpers across the cluster) and during early compression (where the worker proposed extracting helpers as a "compression" tactic).

Principle 3 ("Inline single-use helpers") with explicit evaluator rejection language was the fix. The evaluator scans new declarations and counts call sites; a 1-call helper introduced *this cycle* is rejected.

### 7.5 *Compilation is not correctness* — but it is necessary

Across both loops, every cycle's commit was gated on `lake env lean` succeeding for every modified file (and `lake build` succeeding when files were added/deleted/renamed). This caught dozens of regressions from rename cascades and signature changes. Stale `.olean` caches remain a real risk: a `lake build` that uses cached `.olean`s can pass against source that no longer compiles fresh, so we ran `lake env lean` per file (which always re-checks) as the per-cycle gate, with `lake build` as a tier-2 gate for structural changes only. The first paper [1] arrived at the same per-file gate via a different path; we adopt it here unchanged.

### 7.6 The *normalized-LOC ratchet* is the single most useful gate we added

Raw `wc -l` is gameable in roughly six ways: delete comments, add blank lines, stack tactics with `;`, stack with `<;>`, fold long calls onto one line via `apply ?_ <;> exact …`, or move long signatures to a single line. Normalized LOC (132 lines of Python; strips comments, ignores blanks, splits stacked tactics) is gameable in roughly zero. Making it the per-cycle ratchet meant the worker had to *actually* compress, which meant deletion or proof shortening, which meant we could trust the LOC trajectory as a proxy for progress. The first paper [1] used token count as a proxy for the same thing; in retrospect normalized LOC is sharper because tokens conflate identifier length (which changes nothing semantically) with structural change (which is the thing).

### 7.7 *Diminishing returns* are predictable and should be the loop's stop signal

The compression loop's per-cycle yield curve fell from ~−170 LOC/cycle in the first 10 cycles to ~−7 LOC/cycle in the last 30. We chose to set a *raw* LOC stop target (4 998 < 5 000, where 5 000 was the round-number target derived from the 4 200-line pre-refactor baseline + slack) and let the loop run to it; this gave us a clean termination criterion that did not depend on the loop self-reporting "done". Future runs should set the stop target deliberately rather than running to convergence — the marginal value of −7-LOC cycles is below the marginal cost of running them.

### 7.8 *Gate-repair as a first-class agent* is cheap insurance

The fifth agent introduced for the compression loop — gate-repair — runs only when `check_gates()` fails after the main worker. It receives the worker's diff, the failure details, and the principles file, and tries one repair pass. In our run it was invoked exactly once (cycle 84) and succeeded. A 1.2% invocation rate is low enough that the architectural complexity of a fifth agent looks unjustified ex post — but the alternative is reverting the cycle with `progress_score: -2` and re-attempting from scratch, which costs the worker's full budget. The repair budget (1 hour) is roughly a third of the worker's budget. Even at a 1% rate, gate-repair is net-positive in expectation; we recommend keeping it.

### 7.9 *Structural opportunities are scarce but high-leverage*

Of the 86 compression cycles, 4 were structural (file merger, class → def, cross-file move) and they produced ~150 LOC saved among them. Three cycles of mechanical golf produce the same yield. But the structural cycles were the only ones that *reduced file count*, and therefore the only ones that improved the project's discoverability — fewer files means fewer imports, fewer namespaces to remember, fewer module docstrings to keep aligned. Principle 7 ("structural opportunities backlog") and the curated `structural_ideas.md` file gave the loop a way to find these without re-deriving them every cycle. We recommend any minimization loop maintain a similar artifact.

### 7.10 The *Zorn-block episode* argues for adversarial third-party audits

The 226-line Zorn block survived 150 cycles because no agent in the loop had an incentive to challenge the auditor's claim that it was "60 lines". The loop's economy was self-reinforcing: the auditor said done, the planner moved on, the worker had no signal to revisit, the evaluator scored the cycle that didn't touch it as fine. A 30-minute hand audit by a different reader produced the diagnosis. We had a similar experience in the first paper [1] where Aristotle's auto-proofs had to be hand-vetted because the agent's own scoring rewarded "proof closed" rather than "proof closed with an argument that holds up". The general lesson is: agentic loops need at least one reviewer who is not part of the loop's reward function.

## 8. Related Work

The most direct precedent is the first arxiv paper from this project [1], which used Claude Code + Gemini DeepThink + Aristotle to formalize the Vlasov-Maxwell-Landau equilibrium in 10 days. That paper's "Lessons Learned" section identified *hypothesis creep*, *premature sorry*, and *agent gets "lazy"* as failure modes; this work re-encounters two analogues — *API doubling* and *helper extraction bias* — in a different agentic regime (loop-based rather than conversational) and with different models (gpt-5.5 + claude-opus-4-7 instead of Claude Sonnet + Gemini DeepThink). The lesson that *compilation is not correctness* transfers verbatim.

Other proof-engineering work on Lean 4 / Mathlib at scale focuses on individual proof automation (LeanCopilot, ReProver) or on retrieval (Lean state search, Loogle). To our knowledge, the multi-agent loop with mechanical metric gates and a specialized gate-repair agent is novel as an integration pattern; the components are not.

## 9. Limitations and Future Work

**Limitations.** (1) The compression loop's results are bounded below by what is structurally possible at this Lean+Mathlib version; we did not attempt an upstream Mathlib PR for `TopologicalKrullDim.lean` (which would remove ~200 lines from the project). (2) The loop's reliance on `gpt-5.5` for the worker means our results are tied to the specific tactic-search behavior of that model; preliminary tests with a `claude-opus-4-7` worker showed different (but not strictly better or worse) compression patterns. (3) The compression loop's normalized-LOC metric is one good metric but not the only metric; it is silent on, e.g., proof readability, namespace hygiene, or `simp` set health. (4) The Zorn-block episode shows that a single adversarial audit can find issues 150 cycles of the loop missed; we have not automated this audit step.

**Future work.** Three concrete next steps. (a) Run the compression loop with Idea 6 (Aristotle on body/sig outliers) — current estimate is 200–500 LOC of further yield with no architectural changes. (b) Upstream `TopologicalKrullDim.lean` to Mathlib (Idea 5); estimated −150 to −200 LOC. (c) Build a *third* loop, an "idiomaticity" loop, that runs after compression and uses LLM judgment (not mechanical gates) to identify proofs that compile but read poorly — the ones the next reviewer will flag. The metric here is harder, which is why it is third.

## 10. Conclusion

We took a 4 200-line Lean 4 formalization through a code review, an agentic refactor loop, a manual audit, and an agentic compression loop. The result is a 5 000-line tree that retains the refactor's structural improvements, closes 17 of 19 review items, and is at 0 sorry's / 0 axioms. Total wall-clock 13 days; total agent cycles 595. The single architectural lesson worth emphasizing is that *self-reported* progress is unreliable on long horizons — auditor prose drifts, completion is over-claimed, helpers proliferate — and the corrective is to push as much of the loop's control signal as possible onto mechanical, idempotent scans. The compression loop's normalized-LOC ratchet, fresh-each-cycle audit, and gate-repair agent are concrete instantiations of this principle.

We are reasonably confident this pattern generalizes: review → refactor loop → audit → compression loop is plausibly a stable shape for any agentic engagement with a non-trivial existing codebase.

## References

[1] V. Ilin. *Semi-Autonomous Formalization of the Vlasov-Maxwell-Landau Equilibrium.* arXiv:2603.15929, March 2026.

[2] R. Hartshorne. *Algebraic Geometry.* Graduate Texts in Mathematics 52, Springer, 1977. (Proposition III.2.7 — Grothendieck vanishing.)

[3] Mathlib contributors. *Mathlib4.* `Mathlib.Topology.KrullDimension`, `Mathlib.AlgebraicGeometry.Sheafified`, `Mathlib.CategoryTheory.ShortComplex.ShortExact`. v4.28, 2026.

## Appendix A — Files in `Aristotle/GrothendieckVanishing/main/` after compression (15 files, 4 998 raw LOC)

`CohomologyAPI.lean` 782 — sheaf cohomology API (the file the review demanded).
`PresheafFilteredColimitCore.lean` 493 — degree-0/1/successor comparison isos for filtered colimits of sheaves.
`IrreducibleStep.lean` 482 — the irreducible-case reduction; the technical heart of the proof.
`ClosedImmersion.lean` 474 — closed-inclusion topology and pushforward exactness.
`PresheafFilteredColimit.lean` 447 — `H^n` commutes with filtered colimits, on Noetherian.
`ZeroOutside.lean` 428 — extension-by-zero and `zeroOutsideInt` machinery.
`FlasqueVanishing.lean` 411 — flasque sheaves have vanishing higher cohomology (Zorn block: 39 lines).
`PresheafFilteredColimitGeneral.lean` 382 — general-colimit-of-presheaves helpers.
`TopologicalKrullDim.lean` 278 — Krull-dimension API analogous to `Ideal.height` (Idea-5 candidate for Mathlib upstream).
`FinitelyGeneratedVanishing.lean` 206 — Noetherian finitely-generated reduction.
`ConstantSheafFlasque.lean` 174 — constant sheaf on irreducible space is flasque.
`GeneratedSubsheaf.lean` 161 — subsheaf generated by a family of sections.
`GrothendieckVanishing.lean` 137 — main theorem and its dim-zero base case.
`ClosedImmersionCohomology.lean` 124 — pushforward iso + SES for closed immersions.
`GrothendieckVanishingOverview.lean` 19 — umbrella with `#check`s for every public lemma.

## Appendix B — Per-cycle compression LOC trajectory (every 10th cycle)

| Cycle | Norm LOC before | Norm LOC after | Cumulative Δ |
| ---: | ---: | ---: | ---: |
| 1 | 7 016 | 6 666 | −350 |
| 10 | 5 632 | 5 295 | −1 721 |
| 20 | 5 115 | 5 027 | −1 989 |
| 30 | 4 891 | 4 889 | −2 127 |
| 40 | 4 682 | 4 661 | −2 355 |
| 50 | 4 487 | 4 478 | −2 538 |
| 60 | 4 363 | 4 350 | −2 666 |
| 70 | 4 260 | 4 252 | −2 764 |
| 80 | 4 182 | 4 162 | −2 854 |
| 86 | 4 097 | **4 087** | **−2 929** |

Floor: at the current state, an additional pass of Idea 6 (Aristotle on the 12 body/sig outliers ≥ 40 lines) plus Idea 5 (Mathlib upstreaming) could plausibly take the tree to ~3 700–3 900 normalized LOC. Below that, structural rewrite would be needed.
