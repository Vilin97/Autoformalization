# Aristotle's Role in the Grothendieck Vanishing Formalization

Aristotle (Harmonic AI) appears in the GV project in two waves: the **proving
phase** (Mar 27 – Apr 4, **94 jobs**) and a brief **`aristotle-loop` infra burst**
(Apr 27, **7 jobs**). Filtering `artifacts/report-data/raw/aristotle/projects.json`
(1350 jobs, multi-project) reproduces PR #15's outcome split exactly:
**22 / 66 / 5 / 1** (`COMPLETE` / `COMPLETE_WITH_ERRORS` / `CANCELED` / `FAILED`).

## 1. Workflow

`tools/aristotle-mcp-server.py` is a FastMCP wrapper around `aristotlelib`.
A typical cycle:

1. Author a standalone `.lean` under `aristotle-in/` (imports + statement +
   `:= by sorry`) with strategy and Mathlib API hints in the docstring.
2. `/submit-aristotle` packages it as `tar.gz` and calls
   `Project.create(prompt=…, tar_file_path=…)`. The prompt names the Hartshorne
   step and which lemmas are already proved.
3. The returned UUID lands in `aristotle-jobs.json`.
4. `/check-aristotle` polls `Project.from_id(...)`; once status is `COMPLETE` /
   `COMPLETE_WITH_ERRORS` / `OUT_OF_BUDGET` it downloads `result.tar.gz`.
5. The user copies usable parts into `Aristotle/GrothendieckVanishing/main/`
   and tags the commit, e.g. `feat: Aristotle proves toPlus_surjective (0 sorry!)`.

## 2. Outcome stats (GV-only)

| Cohort | n | COMPLETE | C_W_ERRORS | CANCELED | FAILED | OOB |
|---|---|---|---|---|---|---|
| Proving phase | 94 | 22 | 66 | 5 | 1 | 0 |
| `aristotle-loop` | 7 | 7 | 0 | 0 | 0 | 0 |

PR #15's "22/66/5/1" is exact. **No GV job ran out of budget** (OOB shows up only
twice in the 1350-job total, on unrelated projects). 23 of the 94 are
`resumed-…` re-uploads, sometimes 4 hops deep
(`fca6885d → aa90d308 → 7a56ec72 → bc3176de → bc3176de.resumed`).

## 3. Turnaround

`updated - created` is the *open lifetime*, not pure compute (`last_updated_at`
seems to refresh on dashboard access). With that caveat:

- Median **6649 min ≈ 4.6 d**; p90 **8102 min ≈ 5.6 d**; max **8708 min**
  (`ClosedOpenDecomposition.lean`, Step 1).
- 90/94 stayed open >4 h; the four short-lived ones are the canceled-early
  jobs (`gabriel_injective`, killed at 23 % after 58 m) and the lone `FAILED`
  (`zeroOutsideInt → R` sheafifyLift, 35 %, ~75 h).
- `COMPLETE_WITH_ERRORS` spans 80 min – 145 h, consistent with Aristotle running
  to partial credit rather than a hard wall.

## 4. What got submitted (categorised, multi-tag)

| Topic | n | Example (job id, file) |
|---|---|---|
| irreducibility / Krull dim | 59 | `DimStrictInequality.lean` |
| Ext / sheaf-cohomology | 53 | `1676d0c9` `sheafH_filtered_colimit.lean` |
| (co)limits | 43 | `isSheaf_filtered_colimit.lean` |
| SES / LES manipulation | 42 | `step5_ses.lean` |
| epi / surjectivity | 41 | `4f061625` `epi_app_detailed.lean` |
| constant sheaf | 34 | `5175616d` `ConstantSheafFlasque.lean` |
| stalks | 32 | `819ad352` `stalk_surj_in_Z.lean` |
| flasque | 30 | `FlasqueVanishing.lean` |
| sheafification / Plus | 25 | `17b9bce9` `ToSheafifySurjective.lean` |
| Hartshorne full step | 18 | `bc3176de` `IrreducibleStep.lean` |
| closed immersion | 18 | `71c69301` `epi_unit_of_closedImmersion.lean` |

The mix skews toward conceptual hard steps (Hartshorne III.2.7 Steps 3-5, plus
sheafification surjectivity), not heartbeat-blocked lemmas.

## 5. Aristotle wins (landed)

- `8f42abaa` `isFlasque_of_injective` → `6f98b5f prove isFlasque_of_injective (Aristotle 8f42abaa)`.
- `17b9bce9` `toPlus_surjective` → `2a38cf8 feat: Aristotle proves toPlus_surjective (0 sorry!)`.
- `meq_const_of_irreducible` → `e32c0ac integrate meq_const_of_irreducible from Aristotle (sorry-free!)`.
- `daccfe4 feat: prove dim strict inequality (Aristotle sorry-free proof!)`.
- `887860fb` resumed → `epi_unit_of_closedImmersion`.
- `819ad352` resumed → `stalkPushforward` surjectivity at `x ∈ Z`.
- Empty / LES pieces from `8c16fc5 integrate Aristotle results — prove empty/irreducible cases + LES vanishing`.

## 6. Aristotle losses

- **Wrong direction (most consequential)**: Aristotle returned a counterexample
  to a target the user was trying to prove —
  `d0cdf92 CRITICAL: flasque → injective is FALSE (Aristotle counterexample)`.
  This forced a full re-architecture of the flasque story.
- **5 CANCELED**: user-killed when the outline drifted: `gabriel_injective`
  (23 %), `FlasqueVanishing` via Baer (48 %), `FlasqueComplete` (21 %),
  `PlusObjIsSheaf` (57 %), `ConstantSheafFlasqueFull` (26 %). See
  `f0ebb77 cancel 4 stale Aristotle jobs (false approach / already solved)`.
- **1 FAILED**: a `zeroOutsideInt → R` sheafifyLift construction.
- **66 COMPLETE_WITH_ERRORS**: partial proofs with residual sorries / errors.
  Most "Hartshorne-step" submissions (`bc3176de`, `fca6885d`) landed here —
  the asks were too coarse to close fully.

## 7. The `aristotle-loop` (Apr 27)

7 submissions, **all whole-project** `Clawristotle-aristotle-loop.tar.gz`, all
`COMPLETE`. 6 prompts are identical: *"Golf all the proofs … preserve 0 sorry's,
0 axioms, 0 admits."*; the 7th asks for Mathlib-style cleanup. **No
`aristotle-loop:`-tagged commit landed on `wip/grothendieck-vanishing`** — Apr 27's
commits are all `compress: codex cycle N`. The aristotle-loop was infra
shake-out only; the de-facto golfing winner was the parallel
**codex_compress_loop** (86 cycles, 7016 → 4087 norm LOC).

## 8. Anecdotes

- *flasque → injective is FALSE* (`d0cdf92`, Mar 28). Aristotle's most
  consequential output was a negative result.
- *toPlus_surjective (0 sorry!)* — job `17b9bce9` returned a fully closed
  proof of sheafification surjectivity for the constant presheaf, integrated
  in `2a38cf8` the same day.
- *j_! needed* — job `8d809cf1` (`COMPLETE` on `GrothendieckVanishingFull.lean`)
  confirmed extension-by-zero was the missing infrastructure
  (`7149ae9 Aristotle confirms: j_! needed for full theorem (8d809cf1 COMPLETE)`).
- *Three-hop resume chain* `f0bf6058 → 4a709958 → 3811cb0e` for the same
  `meq_const_all` sorry; the eventual landing was via `5ec05d55` (resume of
  `4e978c1c`).
- *Fast cancellation* — `gabriel_injective` killed at 23 % after 58 min when
  the user realised filtered colimits of *flasque* (not injective) suffice.

## Open questions

- Is `last_updated_at` ever distinct from compute completion, or always a
  dashboard-refresh artefact? The 4–6-day medians are unbelievable as compute
  time.
- How many `COMPLETE_WITH_ERRORS` outputs partially landed (one of N
  sub-lemmas salvaged) vs were discarded? The commit graph names the wins
  but not the salvages.
- What was actually in the 7 `aristotle-loop` outputs, and why was none
  merged — qualitatively worse than codex's golf, or simply unevaluated?
- Was re-submission ("resumed-…") driven by Aristotle's own re-queue, by
  `Project.cancel()` + re-create, or by manual user uploads? Not
  distinguishable from this data.
