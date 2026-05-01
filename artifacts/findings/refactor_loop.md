# Codex Refactor Loop — Findings

## Architecture

`scripts/codex_refactor_loop.py` runs four stages on `wip/grothendieck-vanishing`.
**Planner**: `codex exec --ephemeral --dangerously-bypass-approvals-and-sandbox`
(`gpt-5.5`, reasoning effort `xhigh`) picks one `- [ ]` line from
`.refactor-state/review_tasks.md` and writes `codex_strategy.md`; the chosen
line is promoted to `- [>]` (WIP). If no `- [ ]` lines exist, an **auditor**
Claude call inspects `review.md` and either appends fresh `- [ ]` lines or
returns `loop_done: true`. **Worker**: Codex again (3 hr timeout) edits Lean
files. **Gate**: sorry count must not increase; changed `Aristotle/*.lean`
files must compile under `lake env lean`; on add/delete/rename, `lake build`
runs. On failure a **gate-repair** Codex call retries; second failure triggers
`git checkout -- .` and a `-2` record. **Evaluator**: Claude (`claude-opus-4-7`,
`bypassPermissions`, `--add-dir <repo>`, `--json-schema EVALUATOR_SCHEMA`)
reads diff + last 8 cycles and emits `progress_score ∈ [-2,+2]`,
`task_addressed`, `task_complete`, `stuck_on`, `strategy_recommendation`,
`completed_task_lines`. Lines whose `COMPLETE_IF:` shell test passes are
flipped to `- [x]`. Score ≥ 1 with diff auto-commits and pushes.

## Score distribution and worker exit codes (n = 478, cycles 1–520; 42 missing)

Schema is `[-2,+2]` but only `{0,1,2}` ever occurred:
**`{0: 220, 1: 154, 2: 104}`** — 46% no-progress, 32% modest, 22% strong.
**Zero records carry a `gate_failure` block, zero have
`gate_repair_attempted: true`.** Worker exit codes: `{0: 417, None: 61}` — Codex
never returned non-zero, and the 61 nulls are auditor-only cycles (worker not
run), all reporting `loop_done: true`. The gate-repair branch
(`codex_refactor_loop.py:944–965`) was therefore exercised **zero times**
across 478 cycles — either `--ephemeral` always exits 0 even on partial work,
or the 3-hour worker timeout plus pre-promotion to `- [>]` let Codex always
converge to *something*. The most defensive machinery in the design was dead
code in production.

## Recurring `stuck_on` themes (n = 339 non-empty)

Keyword bucketing of every `stuck_on` field:
**umbrella scope ("broader audit") = 139, checklist exhaustion = 123,
"no blocker" = 6, lake compile/build = 3, file-size target missed = 2,
other = 65.** Two dominant blockers: **scope mismatch** (the phrase
"this cycle only completed one declaration-anchored slice of [the umbrella]"
appears across 30+ sampled fields) and **checklist exhaustion**. Naming or
namespace collisions never appeared as a Codex-side blocker. Across all 478
cycles only 6 `principle_violations` fired, mostly off-strategy edits
(cycle 12: `.gitignore`; cycle 391: bookkeeping file) or layering
(cycle 102: `WithBot` helper in a topology file).

## What worked

Clean wins were nearly all **micro-mechanical refactors with a strict
COMPLETE_IF gate** — rename a public theorem, demote to `private`, delete a
sheaf-level wrapper whose only consumer is internal, extract a long proof body.
Cycles 410–462 are textbook: cycle 410 deleted 24 sheaf wrappers
(`CohomologyAPI.lean` 2125 → 1644 lines); cycles 422–445 each deleted one
wrapper or demoted one `extClass`-named lemma, gated by `rg -n '<symbol>'
Aristotle/`. Other landmarks: **cycle 22** (first Ext-leak step), **cycle 80**
(ad-hoc stalk-lifting replaced by a reusable `CohomologyAPI` lemma),
**cycle 396** (FlasqueCohomology.lean merged into FlasqueVanishing.lean),
**cycle 500** (Zorn machinery extracted into 4 helpers, 226 → 115 lines).

## What didn't work

The literal default
`"Pick the next still-unchecked checklist item and keep scope tighter."`
was returned for 4 runs — cycles 1–10, 453–460, 510–520, and most damningly
**463–498 (n = 36 consecutive)**. Daily mean score collapsed accordingly:
04-23 mean 0.07 (130/137 zero); 04-26 mean 0.00 (23/23 zero). **Cycles 268–331
— 64 consecutive checklist-exhaustion records**, every one "correctly executed
the assigned no-op." Treating score-0 no-op as acceptable instead of a backoff
signal let the loop spin. The second failure mode is **scope creep punished as
no-completion**: cycles 199, 215, 223–225, 230, 240, 250 each landed real
declaration-level diffs but couldn't tick the umbrella `- [ ]` line. Overall
`task_complete: True` rate is just **35% (166/478)**.

## Anecdotes

- **Cycle 47 task_results.md, fully reverted** — Codex tried to delete 3
  `inferInstanceAs` instances; all 3 were load-bearing because Lean's instance
  search "does not always unfold [`abbrev TopCat.Sheaf`] deeply enough." Task
  removed from backlog. (Caveat: only 4 of 478 `task_results/cycle_*.md` files
  survived, and the JSONL row for cycle 47 records a different,
  successful presheaf-generalization — the markdowns and JSONL don't always
  line up by number, so n = 4, can't generalize.)
- **Cycle 270** — `"Cycle 270 correctly preserved the intended no-op state by
  re-verifying that .refactor-state/review_tasks.md has no unchecked checklist
  entries."` Same sentence, cycle number swapped, in ~60 consecutive records.
- **Cycle 396, score 2** — after 64 cycles of checklist exhaustion the auditor
  added new `- [>]` lines and the worker landed `FlasqueCohomology.lean`
  deletion in a single cycle.
- **Cycles 500 → 504–509** — Zorn block extracted into 4 helpers (cycle 500),
  then 4 helpers progressively inlined back: classic extract-then-inline
  oscillation, but each step net-positive on counted LOC per its own gate.

## Cycle rate

Per UTC day: 04-19 (23), 04-20 (64), 04-21 (66), 04-22 (63), **04-23 (137)**,
04-24 (23), 04-25 (55), 04-26 (23), 04-27 (24). Median inter-cycle gap 920 s
(~15 min). **The 04-23 spike is artificial** — each of those 137 cycles was a
~90-second checklist-exhaustion no-op. Notable gaps: cycle 393 → 396 was
72 494 s (~20 h overnight, supervisor presumably regenerating the checklist);
cycle 199 → 215 was ~3 h 20 m. The rate did not slow sustainedly; what slowed
was the average value per cycle.

## Open questions

- Why did Codex never return non-zero? Does `--ephemeral` always exit 0, or did
  the worker silently succeed-with-no-diff on failure? The gate-repair branch is
  untested in production.
- Score schema is `[-2,+2]` but only `{0,1,2}` appeared. Was the negative path
  ever exercised, or did the evaluator prompt forbid it?
- 36 consecutive cycles got the literal default `strategy_recommendation`. Why
  didn't `recent_cycles_are_idle` (`IDLE_COOLDOWN` = 1 hr) trip earlier? Was the
  auditor returning empty `added_lines` and thus appearing to unblock the loop?
- Of 86 closed `completed_task_lines`, are any false positives — `COMPLETE_IF`
  passed but umbrella intent broader?
- Only 4 of 478 `task_results/cycle_*.md` markdowns survived. Hyak-local FS
  not synced back? Without them, qualitative record is JSONL only.
