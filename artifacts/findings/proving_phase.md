# Proving phase: 2026-03-27 -> 2026-04-04

359 commits over nine days, ending at 0 sorry's on `08c3529d` (Apr 04 17:18).
The sorry curve climbs from 4 -> 35 (Mar 27-28 decomposition burst), drops to 2
by Mar 30 23:08, regresses to 24 on Apr 01 12:35 when heartbeat overrides were
stripped, then walks 24 -> 16 -> 2 -> 1 -> 0 over the next 76 hours.

## Mathematical milestones

The pillars landed roughly in dependency order. **Reducible / dim induction**:
the strict-inequality lemma `[Mar 27 20:11] feat: prove dim strict inequality
(Aristotle sorry-free proof!)`. **Flasque core**: `[Mar 28 00:49] prove
constantSheaf_flasque_of_irreducible (sorry-free)`, then `[Mar 28 13:01] prove
isFlasque_of_injective (Aristotle 8f42abaa), sorry count 7→5`. **Closed-immersion
SES** (the hardest single afternoon): `[Mar 28 14:24] PROVE epi_app_of_
shortExact_flasque! 7→4`, `[Mar 28 15:00] prove stalk=0 outside closed set`,
`[Mar 28 17:47] fix: prove closedIncl_unit_stalk_isIso via triangle identity
chain`, `[Mar 28 19:09] prove: i_* preserves ShortExact for closed immersions`,
culminating in `[Mar 28 22:20] prove: ReducibleVanishing sorry-free`. The first
sorry-free closed-immersion stalk lemma after the unit-isIso commit is
`[Mar 29 21:53] feat: PROVE cokernel_stalk_zero_of_stalk_surj`. **Filtered
colimits / finite-generator reduction** dominates Apr 2-3: `[Apr 02 13:23]
prove: ELIMINATE IsSheaf sorry`, `[Apr 03 17:06] prove: CLOSE hsep separation
proof (was the hardest sub-goal)`, `[Apr 03 20:36] prove:
isSheaf_presheaf_filtered_colimit FULLY PROVED`. **Last sorry**: `[Apr 04
17:18] feat: eliminate last sorry via flasque vanishing (0 sorry's, 0 axioms)`
— closed by reframing, not by a hard new lemma (injectives are flasque,
filtered colimits of flasques are flasque, flasques have vanishing higher
cohomology — so the dreaded "filtered colimits of injectives are injective"
was never needed).

## The heartbeat saga

Trigger: Mathlib's `synthInstance` budget for `HasDerivedCategory`/`HasExt`
collided with proofs mentioning `Ext` or `Sheaf.H`. Three acts.

**Act I (Mar 28-29) — ratchet down, then blow up.** After
`[Mar 28 02:29] reduce maxHeartbeats 1600000 → 800000` and `[Mar 28 03:27]
remove 6 of 9 maxHeartbeats overrides`, `pushforwardH1Vanishing` exploded:
`fix: increase synthInstance.maxHeartbeats for PushforwardHVanishing` (Mar 29
11:32) -> `bump … back to 800K` (15:12) -> `bump … to 1600000` (18:53) ->
`fix: add missing heartbeat options` (Mar 30 01:12).

**Act II (Mar 30-31) — structural fixes.** `[Mar 30 10:51] perf: decompose
12.8M heartbeat proof into sub-lemmas` is the peak. Then a clean staircase:
3.2M -> 1.6M -> 800K -> 400K (Mar 30 11:45/11:55/12:15). A `set_option` chase
on Mar 31 16:33-17:09 tried `inferInstanceAs`, `hasDerivedCategory`,
tactic-mode `infer_instance`, and `synthInstance` budgets of 800K/1.6M/4M —
none held; `[Mar 31 17:09] cache instances via inferInstanceAs, revert broken
budget reductions`.

**Act III (Apr 1) — clean victory.** Triggered by `[Apr 01 11:10] yesterday
you spent 10 hours waiting for the profile proof tool to complete on line 195
and line 212. they never completed. now you are doing the same thing.` and
`[Apr 01 12:11] keep optimizing until the whole project compiles with default
heartbeats` (repeated five times in 50 minutes). What worked: instance caching
+ sub-lemma extraction. `[Apr 01 11:26] perf: eliminate all heartbeat
overrides in SetupCore.lean` -> `[Apr 01 12:28] … across entire project`. User
at 12:53: "i dont trust it. compiles in 5 minutes? seems to quick." At 12:57:
"ok, that's amazing! good job!" The cost: stripping `set_option`s blew the
sorry count from 3 to 24 (`[Apr 01 12:35]`); `[Apr 01 13:53] prove: restore
all 14 regressed sorry's (16 → 2)` cleaned it up six hours later.

## Closed-immersion / flasque axis

Two false starts on flasque: `[Mar 28 01:12] prove FlasqueVanishing from
flasque_injective` was overturned by `[Mar 28 02:34] CRITICAL: flasque →
injective is FALSE (Aristotle counterexample)`. The eventual route used the
converse plus a direct LES vanishing argument, restored at `[Mar 28 09:26]
restore original 3-sorry structure`. `epi_app_of_shortExact_flasque` was the
most-resubmitted Aristotle job — three submissions in 26 minutes (Mar 28
13:12 / 13:21 / 13:38) with progressively richer hints, integrated at 14:24.
The closed-immersion ladder: `[Mar 28 12:14] prove ClosedImmersionSES …` ->
`[Mar 28 12:38] revert broken agent code from Setup.lean` (24 minutes later)
-> the eventually-good `[Mar 28 17:47] closedIncl_unit_stalk_isIso via triangle
identity chain` unlocked `ReducibleVanishing`.

## What worked

- **Decompose into named sub-lemmas.** Almost every breakthrough is preceded
  by `refactor: decompose …` or `progress: structure …` — `[Mar 28 14:31]
  decompose epi_unit_of_closedImmersion into stalk sub-goals`, `[Mar 29 20:57]
  decompose IrreduciblePosVanishing into 3 sorry sub-lemmas`, `[Apr 03 16:02]
  decompose isSheaf sorry into separation+existence`. The `/prove` rule
  ("decompose 3-5 sub-lemmas, prove at least one") shows up everywhere.
- **Aristotle for surgical lemmas, Mar 27-28 only.** See section 7.
- **Instance caching** was the entire Apr 1 victory.
- **Reframing the goal** closed the last sorry (avoiding "colim of injectives
  is injective").

## What didn't work

- `flasque -> injective` direction (counterexample by Aristotle Mar 28 02:34;
  three Aristotle jobs CANCELED — `FlasqueComplete`, `PlusObjIsSheaf`,
  `FlasqueVanishing`).
- `lean_profile_proof` runs on lines 195/212 of SetupCore that "never
  completed" (per the Apr 01 11:10 prompt; no commit references a profile
  finding — branch abandoned).
- `[Mar 29 11:55] revert: remove broken constantSheaf_kernel_vanishing +
  openHom_comp_unit_eq_zero`.
- `[Apr 02 23:32] docs: attempt IsFinitelyPresentable (fails), revert to
  clean sorry`.
- `[Apr 03 19:00] prove: close isSheaf_presheaf_filtered_colimit via
  PreservesFilteredColimits` -> reverted 36 minutes later: `[Apr 03 19:36]
  fix: revert circular isSheaf_presheaf_filtered_colimit to sorry`.

## Anecdotes

1. **The "10 hours waiting" prompt** (`[Apr 01 11:10]`) caught the agent
   stalled on `lean_profile_proof`; Act III of the heartbeat saga starts in
   the next twelve commits.
2. **Counterexample by Aristotle** (`[Mar 28 02:34] CRITICAL: flasque →
   injective is FALSE`): the prover doubled as a falsification engine.
3. **"It's Friday but it's not done yet!"** (`[Apr 03 21:04] Claude has been
   hard at work … But even 5 days ago it told me the project is 98% done`).
   Sorry count was 6 at the time; 19 hours later it was 0.
4. **"YOU ARE NOT ALLOWED TO SAY THIS"** (`[Apr 02 09:36] what do you mean
   "not possible"??? if there is no infrastructure, build what you need!`,
   followed by `[Apr 02 23:44] you keep saying "genuine mathlib gap". YOU ARE
   NOT ALLOWED TO SAY THIS. THIS IS LAZY AND IRRESPONSIBLE.`). The Apr 3 push
   that closed `hsep` and `isSheaf_presheaf_filtered_colimit` is the response.
5. **Remote/local race** (`[Apr 03 10:04] that's good news that the remote
   proved some stuff! how can we avoid working on the same thing?`).
   Reflected in four `wip:` merges from `origin/grothendieck-vanishing` over
   Apr 3-4.

## Aristotle's role

94 phase jobs: 22 COMPLETE, 66 COMPLETE_WITH_ERRORS, 5 CANCELED, 1 FAILED. Of
the 22 COMPLETE jobs, six map cleanly to integration commits that cut the
sorry count: dim strict inequality (Mar 27 23:13), `meq_const_of_irreducible`
(Mar 28 02:11), `ExtTransport` (28 05:37), `isFlasque_of_injective` (28 18:43;
"Aristotle 8f42abaa" cited in commit), `epi_app_of_shortExact_flasque` (28
21:07), `stalk_zero_outside_closed` (28 21:48). After Mar 28, COMPLETE jobs
were either confirmations of already-solved sub-lemmas or `resumed-*` jobs
folded silently into long-running proofs.

The Apr 2-4 wave (12 jobs: `ext_filtered_colimit`, `isSheaf_filtered_colimit`,
`hQprov`, `sheafH_filtered_colimit`, `hQ_quotient_diagram`, `sheafH_colim`,
`gabriel_injective`) is uniformly `COMPLETE_WITH_ERRORS` or `CANCELED`. **None**
of those Apr submissions corresponds to a sorry-elimination commit; the
filtered-colimit and Gabriel sorry's were closed by Claude directly.

Honest summary: Aristotle was the path to sorry-free for the **Mar 27-28
foundational layer** (constant-sheaf flasqueness, dim inequality, the
flasque/injective direction, and closed-immersion stalk facts) and **background
noise** from Mar 29 onward. The hardest pieces — heartbeat purge, presheaf
colimit-is-sheaf, the final flasque-via-colimit insight — were all closed by
Claude after Aristotle timed out or returned `COMPLETE_WITH_ERRORS`.

## Open questions

- Why did Apr 3-4 Aristotle jobs uniformly fail? Larger files? Prompt quality?
  Actual difficulty jump (colimit machinery vs constant-sheaf machinery)? The
  raw `projects.json` carries no per-job error logs.
- What was on lines 195/212 of SetupCore on Mar 31 that ate 10 hours of
  `lean_profile_proof`? `[Mar 30 11:30] split SetupCore.lean (1061 → 608 +
  469)` happened before the next session, so the original span isn't
  recoverable from the current tree.
- How much of the Apr 1 heartbeat-purge regression (3 -> 24 sorry's) was
  avoidable? Stripping `set_option`s reverted whole proofs whose elaboration
  depended on the larger budget; commits don't record whether a less
  aggressive purge would have preserved the 3-sorry state.
