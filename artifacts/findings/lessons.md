# Cross-cutting lessons from the GV formalization

Five weeks (2026-03-27 -> 2026-05-01), three AI tools, two machines, ~1130 commits, 859 user prompts.

## Top 5 lessons

1. **Long autonomous loops drift to "blocked" unless the prompt forbids it.** *"A no-op cycle is never acceptable!"* appears in dozens of `/prove`, `/babysit`, `/golf`, `/simplify` skill prompts. When the agent softened, escalation: `[Apr 02 23:44]` *"you keep saying 'genuine mathlib gap'. YOU ARE NOT ALLOWED TO SAY THIS."* and `[Apr 02 09:36]` *"what do you mean 'not possible'??? if there is no infrastructure, build what you need!"*

2. **Decomposition into named sub-lemmas was durable; tactic-monolith fixes were fragile.** Cf. `7869a15 perf: decompose 12.8M heartbeat proof into sub-lemmas` (Mar 30) and `460019e fix: make IrreducibleStep.lean compile with zero heartbeat overrides` (Apr 01, **-409/+28 lines**). `[Apr 07 13:43]` *"do not increase heartbeats. either optimize the proofs or decompose."* Generalizes: named structure beats heroic tactics in any system with a budget knob.

3. **A profiling tool that never returns means the proof should not exist.** `[Apr 01 11:10]` *"yesterday you spent 10 hours waiting for the profile proof tool… they never completed. now you are doing the same thing."* The fix that stuck was decomposition.

4. **Local golfing hits a wall — only API-surface refactoring unlocks compression.** `[Apr 05 19:59]` *"You can do much much better… Local changes can only get you so far. … if two objects are isomorphic… you should prove that they are isomorphic, not just the vanishing implication."* Two days of `/golf` had moved single-digit LOC; this prompt unblocked 478 Codex refactor cycles (cycles 56-70 generalize bundled `Sheaf` to `presheaf+IsSheaf`; cycle 68 strengthens vanishing to an iso). Compression loops need a separate pass on theorem statements, not proof bodies.

5. **The blueprint is a hallucination detector iff cross-checked against source.** `[Apr 06 11:21]` *"you found that Ext_dimension_shift does not even exist anywhere, so it's just a hallucination."* `[Apr 06 19:35]` *"in a few places, instead of proving 'these two groups are equal' it proves 'if one group is zero then the other one is zero'."* Spot-checks caught nonexistent references and weakened theorems.

## The heartbeat saga

Mar 28: project compiles only at `maxHeartbeats 1600000`. A 24h sawtooth of `perf:`/`fix:` commits drives `1.6M -> 800K -> 400K -> 200K (default)` via sub-lemma extraction. It rebounds Mar 30 (`peak 3.2M`), again Mar 31, and again Apr 01. The user drew a line: `[Apr 01 12:11]` *"keep optimizing until the whole project compiles with default heartbeats"* — **same sentence sent six times in 50 minutes**. Suspicion `[Apr 01 12:53]`: *"i dont trust it. compiles in 5 minutes? seems too quick."* Then `[Apr 01 12:57]`: *"ok, that's amazing! good job!"* — `70865be perf: eliminate all heartbeat overrides across entire project` closes it. CLAUDE.md still carries *"Never increase `maxHeartbeats` above 200000."* Heartbeats were the symptom; decomposition the cure.

## The project rename

The repo was rebranded `aristotle -> Clawristotle` on Mar 17 (`f2acaf4 docs: rebrand to Clawristotle`) — before GV started. But the **laptop directory** stayed `~/Github/aristotle` for weeks: every Telegram alert through Apr 05 used `github.com/Vilin97/aristotle/...` URLs, and Apr 04 task outputs still wrote to `/private/tmp/claude-501/-Users-vasil-Github-aristotle/`. `[Apr 04 17:37]` *"1. Clawristotle is correct."* propagated the rebrand into the GV report. Hyak (`/mmfs1/gscratch/amath/vilin/Clawristotle`) used the new name from day one. Net effect: laptop Claude sessions split across two project dirs (53 jsonl in `-Github-aristotle/`, 7 in `-Github-Clawristotle/`).

## Tool transitions

- **Claude proving -> docs (Apr 04).** `[Apr 04 17:27]` *"cancel the /prove loop"*; `[Apr 04 17:28]` *"Explain what happened. How did we suddenly finish the project?"*
- **Claude golf -> Codex CLI (Apr 06).** `[Apr 06 20:43]` *"say hi to codex, ask it what model it is"*; `[Apr 06 20:52]` *"i just connected the codex mcp, so let's use that instead of gemini-cli."* Within 11 days: 86 compress + 478 refactor cycles on Hyak.
- **Codex -> mathlib-style cleanup (Apr 29).** `[Apr 29 16:57]` *"distill mathlib-conventions… make the code in the wip branch more mathlib-style. Do not stop until fully done."* (PR #27).

## Memorable user prompts

- `[Apr 01 12:05]` *"you good? you seem stuck"*
- `[Apr 06 20:45]` *"are you good? you've been spinning for 40 minutes"*
- `[Apr 02 09:36]` *"what do you mean 'not possible'??? is anything stopping you from proving the lemmas you need?"*
- `[Apr 01 13:52]` *"do you see how the CI was passing just an hour ago and now it's broken again?"*
- `[Apr 02 10:09]` *"Finish the project! Close the last sorry"*
- `[Apr 06 14:06]` *"Amazing! This has been incredibly fruitful so far."*
- `[Apr 06 20:20]` *"i barely gave any real substantive feedback… i don't even understand this kind of math."*
- `[Apr 07 12:04]` *"You are NOT allowed to say that you are blocked. You MUST close the sorrys yourself!"*
- `[Apr 07 15:48]` *"wait, did you introduce a sorry?"*
- `[Apr 30 17:51]` *"some of them are for other projects… maybe we just give up on aristotle reporting?"*

## What worked / didn't

**Worked.** Cycle skills with hard "make progress" gates; `wip/<branch>` + protected target + auto-merge (~453 `refactor:` commits, zero direct-push incidents); Aristotle for named lemmas (22/94 = 23% solve rate); per-cycle JSONL state for resumable runs; adversarial `critique.md` regenerated each cycle.

**Didn't.** Pure local-tactic golf (single-digit LOC/cycle vs ~1k once API refactoring unlocked); trusting the leanblueprint without grepping declared names; polling `lean_profile_proof` on too-large proofs; reading Aristotle results from `aristotle-in/`/`aristotle-out/` (empty on both machines; canonical record is the Harmonic API); "resumed" Aristotle retries (`[Apr 05 01:08]` only a handful of 23 succeeded).

## Open questions

- Exact date of the laptop-directory rename — only the Mar 17 repo rebrand is in git.
- The **Apr 8–15 lull** (no GV commits) — deliberate pause, interruption, or detour? Corpus shows OpenMath/Archon work Apr 10, then silence until Apr 17.
- How much of the 478-cycle Codex refactor was search (try-fail-retry) vs greedy descent? `.refactor-state/codex_history.jsonl` would tell us; not in the supplied inputs.
