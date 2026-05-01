# Narrative synthesis: the GV formalization, end-to-end

Five-week story (2026-03-27 → 2026-05-01), four phases, three AI tools, two
machines. This file is the spine of the technical report; the four
phase-specific files (`proving_phase.md`, `refactor_loop.md`,
`compress_loop.md`, `aristotle_role.md`) are the appendix evidence.

---

## The arc

| Phase | Dates | Driver | Headline |
|---|---|---|---|
| 1. Proving | 2026-03-27 → 2026-04-04 | Claude Code (laptop), Aristotle | 0 → 35 → 0 sorries; 410 commits |
| 2. Lull / docs | 2026-04-05 → 2026-04-16 | Manual, light Claude | TECHNICAL_REPORT, PR #15, **8-day no-commit gap Apr 8–15** |
| 3. Refactor | 2026-04-19 → 2026-04-27 | Codex CLI worker + Claude evaluator (Hyak) | 478 cycles; **only 35% completed their assigned task**, **46% scored 0** |
| 4. Compress | 2026-04-27 → 2026-04-28 | Same architecture, different gate | 86 cycles; **7016 → 4087 normalized LOC (-42%)**; crossed the raw <5000 target on the very last cycle |
| 5. Mathlib polish | 2026-04-29 → 2026-05-01 | Claude (interactive + agents), report planning | PR #27 lint-clean + this report's data plumbing |

The bimodality is real: ~9 days of theorem-proving, ~14 days of automated
refactor/compression, with a quiet doc/PR week in the middle. Active days are
~23 of 35 elapsed.

---

## The mathematics, in sequence

The proof has four architectural pillars (well-founded induction on Krull dim
→ irreducible reduction → flasque vanishing → finite-generator reduction via
filtered colimits). They landed in dependency order, almost on schedule:

1. **Mar 27** — dim strict-inequality lemma proved sorry-free (by Aristotle).
   The induction skeleton existed.
2. **Mar 28 (busy day)** — `constantSheaf_flasque_of_irreducible` (00:49),
   `isFlasque_of_injective` via Aristotle (13:01), `epi_app_of_shortExact_flasque`
   integrated after **three resubmissions in 26 minutes** (14:24),
   `closedIncl_unit_stalk_isIso` via triangle identity (17:47), and
   `ReducibleVanishing` sorry-free by 22:20.
3. **Mar 29 – Apr 1** — heartbeat saga (see below) blocks real progress; the
   sorry count actually *regresses* 3 → 24 on Apr 01 12:35 when the user pushes
   for default-heartbeat compilation. Six identical *"keep optimizing"* prompts
   in 50 minutes; cleanup commit at 13:53 closes 14 regressed sorries.
4. **Apr 2–3** — filtered-colimit / finite-generator pillar. The hardest
   sub-goal is `hsep` separation; closed Apr 03 17:06. The user hits peak
   frustration here: *"YOU ARE NOT ALLOWED TO SAY 'genuine mathlib gap'."*
5. **Apr 04 17:18** — last sorry eliminated. **The breakthrough was a reframing**:
   instead of proving the dreaded "filtered colimits of injectives are injective,"
   the proof routes through *flasque* (injectives are flasque, filtered colimits
   of flasques are flasque, flasques have vanishing higher cohomology). What
   looked like a major missing infrastructure piece dissolved.

---

## Three big challenges (with quotes)

### 1. The heartbeat saga (Mar 28 – Apr 01)

`maxHeartbeats` and `synthInstance.maxHeartbeats` collided with Mathlib's
`HasDerivedCategory`/`HasExt` machinery. Three acts:

- **Act I (Mar 28-29)**: ratchet-down of overrides; `pushforwardH1Vanishing`
  blows up; budgets oscillate `1.6M ↔ 800K ↔ 1.6M ↔ 4M`.
- **Act II (Mar 30-31)**: peak `[Mar 30 10:51] perf: decompose 12.8M heartbeat
  proof into sub-lemmas`. A clean staircase 3.2M → 1.6M → 800K → 400K. Then a
  `set_option` chase on Mar 31 16:33–17:09 fails — every variant reverts.
- **Act III (Apr 01)**: triggered by *"yesterday you spent 10 hours waiting
  for the profile proof tool to complete on line 195 and line 212. they never
  completed. now you are doing the same thing."* (`[Apr 01 11:10]`). The fix
  was **instance caching plus sub-lemma extraction** — `[Apr 01 11:26] perf:
  eliminate all heartbeat overrides in SetupCore.lean`, propagated project-wide
  by `[Apr 01 12:28]`. Cost: sorry count blew 3 → 24, recovered in 6 hours.
  CLAUDE.md still bears the rule: *"Never increase `maxHeartbeats` above
  200000."*

Lesson: in a system with a budget knob, **decomposition is durable, override
juggling is fragile**.

### 2. Aristotle's most-consequential output was negative (Mar 28 02:34)

`d0cdf92 CRITICAL: flasque → injective is FALSE (Aristotle counterexample)`
overturned a target the user was actively pursuing. Aristotle doubled as a
falsification engine. The *converse* plus a triangle-identity stalk argument
ended up unlocking the reducible case. Three downstream Aristotle jobs
(`FlasqueComplete`, `PlusObjIsSheaf`, `FlasqueVanishing`) were CANCELED in
the same week.

Aristotle wins/losses for the proving phase: 22 COMPLETE / 66 COMPLETE_WITH_ERRORS
/ 5 CANCELED / 1 FAILED (matches PR #15 exactly). **Of 22 COMPLETEs, only 6
map to direct sorry-elimination commits**, all on Mar 27-28 (the foundational
layer). Apr 2-4 jobs uniformly returned errors or were canceled — the
filtered-colimit and Gabriel sorries were closed by Claude directly.

Lesson: **Aristotle was the path to sorry-free for foundational, well-scoped
lemmas only; conceptual hard steps (Hartshorne III.2.7 Steps 3-5) were too
coarse.** Aristotle was a tactic, not a strategy.

### 3. The refactor loop's "478 cycles" headline is misleading

478 sounds heroic. Actual quality breakdown:

- Schema is `[-2, +2]`; only `{0, 1, 2}` ever fired. **220 (46%) scored 0**;
  154 modest; 104 strong.
- `task_complete: true` rate is **35% (166/478)**.
- **Cycles 268–331 = 64 consecutive checklist-exhaustion no-ops.** Same
  sentence in every record, cycle number swapped.
- **Cycles 463–498 = 36 consecutive returns of the literal default fallback
  string.**
- `gate_repair_attempted: true` count = **0**. The defensive gate-repair branch
  is dead code — Codex `--ephemeral` always exits 0.

Real wins were micro-mechanical refactors with strict `COMPLETE_IF` gates
(cycle 410 deleted 24 wrappers, 2125 → 1644 lines; cycle 500 extracted Zorn
machinery 226 → 115 lines). The cycle-rate **was constant** but the average
value per cycle decayed; "478 cycles" should be reported as ~166 productive
cycles in the narrative.

Compress loop is much cleaner: 86 cycles, all negative-LOC by gate, top 5
drove 49% of the total reduction (sheaf-reversion phase 1-10, mean −180/cycle),
late phase (61-86) averaged −10/cycle and crossed the 5000 raw target on the
**very last possible cycle**.

---

## What worked (durable patterns)

- **Decomposition into named sub-lemmas.** Almost every proving-phase
  breakthrough is preceded by `refactor: decompose …`. Same pattern killed
  the heartbeat saga.
- **Cycle skills with hard progress gates.** *"A no-op cycle is never
  acceptable!"* in `/babysit`, `/prove`, `/golf`, `/simplify`. Generalizes:
  loops drift unless the prompt forbids "blocked."
- **`wip/<branch>` + protected target + auto-merge.** ~453 `refactor:` commits
  flowed through with zero direct-push incidents.
- **Reframing instead of grinding.** Last sorry closed by routing around a
  hard sublemma, not by proving it.
- **API-surface refactoring (compress)** — bundling `(F : Presheaf, h : F.IsSheaf)`
  triples into a single `Sheaf` argument. Cycle 1 alone removed −350 LOC; the
  pattern repeated 11 times. Local proof-body golf (`/golf`) hit a wall around
  single-digit LOC/cycle.

## What didn't (lessons from failure)

- **Override juggling.** Six identical heartbeat budgets in 90 minutes; none
  held until structural decomposition.
- **`lean_profile_proof` on too-big proofs.** "10 hours, never completed."
  Signal that the proof itself shouldn't exist.
- **Trusting `aristotle-in/` and `aristotle-out/`.** Empty on both machines;
  the canonical record is the Harmonic API.
- **Pure-tactic compress.** `;` and `<;>` chains were explicitly forbidden
  by `principles.md` because they don't reduce normalized LOC.
- **Local-only refactoring.** `[Apr 05 19:59]` *"Local changes can only get
  you so far. … if two objects are isomorphic… you should prove that they are
  isomorphic, not just the vanishing implication."* Two days of `/golf` had
  moved single-digit LOC; this prompt unblocked the 478-cycle Codex era.

---

## Five quotes that capture the experience

- `[Apr 01 11:10]` *"yesterday you spent 10 hours waiting for the profile
  proof tool to complete on line 195 and line 212. they never completed. now
  you are doing the same thing."*
- `[Apr 02 23:44]` *"you keep saying 'genuine mathlib gap'. YOU ARE NOT
  ALLOWED TO SAY THIS. THIS IS LAZY AND IRRESPONSIBLE."*
- `[Apr 03 21:04]` *"It's Friday but it's not done yet!"* (sorry count was 6;
  closed 19 h later.)
- `[Apr 06 20:20]` *"i barely gave any real substantive feedback… i don't
  even understand this kind of math."*
- `[Apr 07 15:48]` *"wait, did you introduce a sorry?"*

---

## Things still unknown (carry into the report or dig further)

| ? | Source |
|---|---|
| Why did Apr 2-4 Aristotle jobs uniformly fail/error? File size? Prompt quality? Real difficulty step? | proving_phase.md OQ-1 |
| What was on `SetupCore.lean` lines 195 & 212 that ate 10 h of `lean_profile_proof`? | proving_phase.md OQ-2 |
| Is `last_updated_at` ever distinct from compute completion, or always a dashboard refresh? | aristotle_role.md OQ-1 |
| Why did Codex `exec --ephemeral` always exit 0? Gate-repair branch never ran. | refactor_loop.md OQ-1 |
| What was actually in the 7 `aristotle-loop` outputs, and why was none merged? | aristotle_role.md OQ-3 |
| Apr 8–15 lull: deliberate pause, interruption, or external detour? | lessons.md OQ-2 |
| Could a successor "structural" phase have hit 4500 raw, or is residual ~5000 LOC genuinely irreducible? | compress_loop.md OQ-3 |

---

## How to use this for the report

The technical report should read in three layers:

1. **Headline** — the bimodal arc, the four pillars, 0-sorry result, ~1130
   commits, ~5 weeks, ~13.9M Claude output tokens + 6.7B cache reads, 5
   Codex-persisted GV sessions, 86 + 478 ephemeral cycles, 94+7 Aristotle
   submissions. (Numbers in `metrics.json`.)

2. **Three honest stories** — heartbeat saga, Aristotle's negative result,
   refactor loop's quality breakdown. Avoid the "478 cycles!" pitch — say
   "478 attempts, 166 productive."

3. **What it teaches** — the five durable patterns above, with the matching
   failure modes. The single biggest lesson is *decomposition beats override
   juggling*, demonstrated three independent times.

The phase files contain enough quotable detail for any section. The figures
in `artifacts/*_gv.png` already plot the headline numbers.
