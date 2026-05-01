# Plan: Technical Report for the Grothendieck-Vanishing Project

This is a draft plan for the GV technical report. Existing reports in the
repo (`TECHNICAL_REPORT.md`, `REFACTOR_REPORT.md`, `AUDIT_VERDICT.md`,
`review.md`, `codex-proof-notes.md`, etc.) are **all unreliable** and must
not be used as input — the new GV report is being written from scratch
against primary sources only.

The GV project differs from the prior VML formalization in three ways
that shape the analysis:

1. **Timeline is ~5 weeks elapsed (2026-03-27 → 2026-04-30)**, bimodal:
   ~9 days of initial proving (Mar 27 – Apr 4, ending sorry-free) and
   ~14 days of refactor / compression (Apr 17 – Apr 30). The repo
   `Clawristotle` itself was initialized 2026-01-07, but everything before
   Mar 27 is unrelated work (Lean experiments, Cayley-graph play,
   Auslander–Buchsbaum, the VML formalization that finished ~Mar 10). The
   `grothendieck-vanishing` branch first appears on 2026-04-01 (PR #2,
   `wip/grothendieck-vanishing → grothendieck-vanishing`) — that's when
   the wip→protected-branch PR workflow was set up; coding had been
   happening on the active dev branch since Mar 27.
2. **Three AI tools** were used: Claude Code (interactive + `/babysit` /
   autonomous loops), Codex CLI (compress and refactor loops, late April),
   and the Aristotle external prover (~94 submissions in early April per
   PR #15, plus an `aristotle-loop` infra burst on Apr 27). The Codex
   loops are the new piece relative to the prior VML formalization.
3. **Two machines**: local laptop (`~/Github/Clawristotle`, was
   `~/Github/aristotle` before the rename) and Hyak (UW HPC cluster,
   `/mmfs1/gscratch/amath/vilin/Clawristotle`). Logs live in different
   filesystems and the project rename split the Claude session dirs.

The plan below lists every statistic to collect, where it lives, how to collect it,
and what new analyses GV needs that VML didn't.

> **Note on existing scripts.** `scripts/*_gv.py` and `artifacts/*_gv.png`
> were written for GV (cutoff `2026-03-27` is GV's first commit, not
> VML's), but on the laptop under the pre-rename project name —
> `SESSION_DIR = ~/.claude/projects/-Users-vasil-Github-aristotle/` and
> repo path `~/Github/aristotle`. They need re-pointing at (a) the
> post-rename laptop project dir `…-Github-Clawristotle/`, (b) the Hyak
> project dir `/mmfs1/home/vilin/.claude/projects/-mmfs1-gscratch-amath-vilin-Clawristotle/`,
> and (c) the current repo path. They are not VML scripts — but they only
> see part of the GV picture (laptop, pre-rename) and miss the Codex
> loops and Hyak sessions entirely.
>
> **Note on this draft.** The original draft of this plan was produced
> on the laptop, which is git-only (no Claude/Codex jsonl, no
> `aristotle-in/`, `aristotle-out/`, `.compress-state/`, `.refactor-state/`
> — all gitignored). Several factual claims in the original draft —
> notably that `aristotle-jobs.json` being `[]` implies GV never used
> Aristotle — were artifacts of that blind spot. This revision was made
> on Hyak with full data access; corrections are flagged inline below.

---

## 1. Report Structure (proposed)

Standalone (the prior `TECHNICAL_REPORT.md` is not a base — see header note).
Sections cover the multi-tool / multi-phase nature of GV:

1. **The Mathematics** — Hartshorne III.2.7, hypotheses, proof architecture (well-founded induction on Krull dim; reducible→irreducible→dim-0; flasque vanishing; closed immersion SES; finite-generator reduction via filtered colimits).
2. **Development Process**
   - **Narrative** (~5-week timeline split into phases — see §2.3).
   - **Session Activity** across machines and tools.
   - **Token Usage** (Claude + Codex separately and combined).
   - **Loop modes**: `/babysit`, `autonomous_loop`, `aristotle-loop`,
     `codex_compress_loop`, `codex_refactor_loop`, mathlib-style refactor.
   - **Aristotle Integration** — ~94 submissions in the proving phase
     (per PR #15: 22 proved / 66 with sorry / 5 canceled / 1 failed),
     plus the Apr 27 `aristotle-loop` infra burst. The empty
     `aristotle-jobs.json` in git is misleading: per-job state lives in
     gitignored `aristotle-in/` and `aristotle-out/` and is only on the
     machine where prove/submit-aristotle commands ran.
   - **Lines of Code Over Time** (raw and normalized).
   - **Compress / Refactor Cycle Effectiveness** (NEW, GV-specific —
     86 compress cycles, 478 refactor cycles in `.refactor-state/codex_history.jsonl`).
   - **Git Churn**.
   - **Sorry Elimination**.
   - **Tool Usage** (Claude tools + Codex tools, side by side).
3. **Technical Stack**.
4. **Authors & Credits / License** — see §5.

---

## 2. Metrics to Collect

For each metric: what it is, the data source, how to extract it, and any pitfalls.

### 2.1 Headline metrics table (mirrors VML)

| Metric | Source | Notes |
|---|---|---|
| Lean 4 files | `find Aristotle/GrothendieckVanishing -name '*.lean' \| wc -l` | At HEAD. |
| Lines of code (raw, normalized) | `wc -l` and `scripts/normalized_loc.py` | GV uses both; normalized strips comments/blank lines. Currently ~4998 raw / ~4087 normalized after compress cycle 86. |
| Theorems / lemmas / definitions | grep `^theorem`, `^lemma`, `^def` (with namespace handling) | Need a script that respects `private`, `protected`, `noncomputable`. |
| Sorry / axiom / admit count | `grep -c sorry` w/ comment-stripping | Already implemented in `sorry_history_gv.py`. |
| Development duration | `git log --reverse` first GV commit → HEAD | **~5 weeks elapsed (2026-03-27 → 2026-04-30)**, ~23 active days. NOT 4 months. |
| Active days | distinct dates in `git log --pretty=%ad` filtered to GV-touching commits | Currently 23 distinct dates from 2026-03-27 onward (out of 35 elapsed). Distinguish from elapsed days. |
| Git commits | `git rev-list --count HEAD` | Currently ~1130 on `wip/grothendieck-vanishing`. |
| Claude Code sessions | jsonl file count in both `Github-aristotle` and `Github-Clawristotle` project dirs (laptop) + Hyak `/mmfs1/home/vilin/.claude/projects/-mmfs1-gscratch-amath-vilin-Clawristotle/` | Project was renamed mid-flight on the laptop; Hyak path was always Clawristotle. |
| Codex sessions | `~/.codex/sessions/**/*.jsonl` count | Laptop + Hyak (Hyak only has `2026/04/`). |
| Interactive prompts | classify user messages from Claude jsonl (filter slash commands & tool results) | Same logic as `session_viz_gv.py`. |
| `/babysit`, `/compress`, `/refactor` invocations | classify slash commands in Claude jsonl + cycle counts in `.compress-state/codex_history.jsonl` (86 cycles) & `.refactor-state/codex_history.jsonl` (478 cycles) | NEW: also count Codex-driven cycles separately. |
| Assistant turns | count `type=assistant` messages in Claude jsonl + Codex equivalents | |
| Tool calls | count `tool_use` blocks in Claude jsonl + Codex equivalents | |
| Tokens consumed | Claude jsonl `usage` field; Codex sqlite `logs_2.sqlite` (~30 MB; need to inspect schema) | NEW: Codex token accounting is under-explored, may need digging. |
| Estimated API cost | per-model pricing × tokens, separately for Claude/Codex | |
| Aristotle submissions | PR #15 description + `aristotle-out/` (gitignored, on the machine that ran the prover) + commit messages tagged `submit to Aristotle` | **~94 submissions in the proving phase** per PR #15 (22 proved / 66 with sorry / 5 canceled / 1 failed). Plus the Apr 27 `aristotle-loop` burst (~7 commits). Empty git-tracked `aristotle-jobs.json` is NOT evidence of zero usage. |

### 2.2 Per-figure metrics (graphs)

Each one becomes a `.png` in `artifacts/` plus narrative.

| Figure | What it shows | Data source |
|---|---|---|
| **Dependency graph** | All theorems/lemmas in `Aristotle/GrothendieckVanishing/` with proof edges. | Lean script `scripts/dep_graph_gv.lean` (already exists for VML — needs path & module changes). |
| **Session activity heatmap** | Hourly activity, hour-of-day distribution, **per machine and per tool**. | Claude jsonl timestamps + Codex jsonl timestamps. NEW: stack Claude vs Codex. |
| **Token usage (cumulative + per-turn)** | Cumulative input/output tokens; per-turn context size; autocompact markers; cost breakdown (cache reads / cache creation / output / fresh input). | Claude jsonl `usage`; Codex sqlite or jsonl. NEW: split by tool. |
| **LOC history (raw + normalized)** | LOC over commits, annotated by phase. | `git log` walk + `wc -l` + `normalized_loc.py`. NEW: two lines (raw, normalized). |
| **LOC by file group** | Stacked area: `main/` vs `Landau/` vs other (if any). | Group by directory at each commit. |
| **Git churn** | Daily +/- and net delta. | `git log --numstat`. |
| **Sorry count over time** | Sawtooth pattern with phase annotations. | Walk commits, count sorries (already in `sorry_history_gv.py`). |
| **Tool usage breakdown** | Per-category bar + daily stacked. | Classify tool_use blocks; need to extend categories for Codex tools (e.g. `apply_patch`, codex shell). |
| **Aristotle outcomes** | Stacked bar by date (proved/disproved/sorry/failed). | `aristotle-out/` on the machine that ran the prover (gitignored, NOT on Hyak — confirm laptop has it). Fall back to PR #15 totals if dir is gone. **Keep.** |
| **Aristotle turnaround** | Histogram by outcome. | Same. **Keep if `aristotle-out/` survives; else drop.** |
| **Compress cycle effectiveness** *(NEW)* | Per-cycle LOC delta (raw and normalized), success/skip rate, stuck-on reasons. | `.compress-state/codex_history.jsonl` (86 cycles). |
| **Refactor cycle effectiveness** *(NEW)* | Per-cycle metrics (similar). | `.refactor-state/` and `wip/grothendieck-vanishing` commit messages tagged "refactor:". |
| **Phase / loop-mode timeline** *(NEW)* | Gantt-style: which loop mode was active each day; commit-rate by loop mode. | Classify commit messages + state-dir timestamps. |
| **Cost per LOC removed (compress)** *(NEW)* | tokens spent / normalized LOC saved per cycle. | Codex usage × `codex_history.jsonl`. |

### 2.3 New analyses unique to GV

- **Phase decomposition.** GV has four phases visible from commit density
  and commit-message tags. Anchor each to a milestone:
  1. **Proving (2026-03-27 – 2026-04-04, ~9 days)** — skeleton →
     0 sorries / 0 axioms. Heavy interactive Claude Code + Aristotle
     (~94 jobs). Intermediate milestone: 2026-03-28 commit "close all
     sorry's: proof complete modulo 3 axioms in Setup.lean"; final
     sorry-and-axiom-free state in early April.
  2. **Documentation & polish (2026-04-05 – 2026-04-07)** — TECHNICAL_REPORT,
     visualizations, README updates (PRs #14, #15, #16, #17, etc.).
     Milestone: PR #15 "credit Brian Nugent, thorough Aristotle analysis".
  3. **Compression & refactor (2026-04-17 – 2026-04-28)** — Codex compress
     loop (86 cycles, ~5500 → 5008 raw LOC) and refactor loop (478 cycles).
     Apr 27 also includes the `aristotle-loop` infra burst.
     Milestone: compress cycle 86 crosses raw LOC < 5000.
  4. **Mathlib-style cleanup & report planning (2026-04-29 – 2026-04-30)** —
     PR #27 "mathlib-style refactor: docstrings, naming, lint-clean";
     PR #28 wip merge; this REPORT_PLAN.
- **Loop-mode attribution.** Of ~1130 commits on `wip/grothendieck-vanishing`,
  ~453 are tagged `refactor:` (mostly the codex refactor loop) and ~80 are
  tagged `compress: codex cycle N`; ~7 are `aristotle-loop:`; the rest are
  interactive/babysit/docs/wip. Attribute each commit to a loop mode and
  report time/tokens/LOC per mode.
- **Tool-vs-tool comparison.** Claude Code vs Codex CLI: tokens consumed,
  cycles run, LOC delta produced, error rate, $/LOC. Codex is doing the
  bulk of the late-April refactor; this comparison is the headline story
  the VML report did not have.
- **Laptop vs Hyak split.** Sessions per machine, tokens per machine,
  commit attribution per machine. The compress and refactor loops
  primarily ran on Hyak (state dirs are checked out here); the proving
  phase ran primarily on the laptop (where `aristotle-in/aristotle-out/`
  live).
- **Raw-LOC vs normalized-LOC convergence.** GV's compress loop optimized
  normalized LOC; raw LOC tracks differently. A two-line plot tells this story.
- **Activity gaps.** Apr 8 – Apr 15 is a real lull (no commits), as is
  Apr 23. Worth flagging and confirming there isn't a missing data source.

---

## 3. Data Sources

### 3.1 Laptop (`vasil@local`, `~/Github/Clawristotle`)

| Source | Path | Coverage |
|---|---|---|
| Claude Code sessions (current name) | `~/.claude/projects/-Users-vasil-Github-Clawristotle/` | 7 jsonl files, mostly Apr 27–30 (post-rename). |
| Claude Code sessions (old name) | `~/.claude/projects/-Users-vasil-Github-aristotle/` | 53 jsonl files, the bulk of the proving phase (pre-rename). |
| Claude Code sessions (related, possibly relevant) | `~/.claude/projects/-Users-vasil-Github-aristotle-mcp/`, `…-Aristotle-cayley-graph-Sn/` | Need to check whether these touched GV files. |
| Codex sessions | `~/.codex/sessions/2026/{03,04}/*.jsonl` | 30 files. |
| Codex history (slash-command-style) | `~/.codex/history.jsonl` | One-line entries. |
| Codex logs sqlite | `~/.codex/logs_2.sqlite` (51 MB) | Internal logs; schema has `logs(ts, level, target, feedback_log_body, …)`. Need to confirm whether token usage is recorded here or only in session jsonl. |
| Aristotle jobs (real data) | `aristotle-in/`, `aristotle-out/` (gitignored) | **The 94 GV submissions per PR #15 should live here.** Confirm directory survives on the laptop and capture before any cleanup. |
| Aristotle jobs (git-tracked) | `aristotle-jobs.json` | Currently `[]` and 3 bytes — IGNORE this file as a usage signal. The empty value reflects that per-job state was never checked in. |
| Git history | `git log` on `wip/grothendieck-vanishing` and `grothendieck-vanishing` | ~1130 commits. Same on both machines (git is shared). |

### 3.2 Hyak (`vilin@hyak-*`, `/mmfs1/gscratch/amath/vilin/Clawristotle`)

This is where the late-April compress / refactor loops ran. Already
accessible from the current shell.

| Source | Path | Coverage |
|---|---|---|
| Claude Code sessions | `/mmfs1/home/vilin/.claude/projects/-mmfs1-gscratch-amath-vilin-Clawristotle/` | The Hyak-side Claude sessions. Verify file count and date range. |
| Codex sessions | `/mmfs1/home/vilin/.codex/sessions/2026/04/*.jsonl` | April only — Hyak Codex usage started here. |
| Codex history | `/mmfs1/home/vilin/.codex/history.jsonl` (~14 KB) | |
| Codex logs sqlite | `/mmfs1/home/vilin/.codex/logs_2.sqlite` (~30 MB) | Same schema question as laptop. |
| Compress-loop state | `.compress-state/codex_history.jsonl` (86 cycles) + `codex_task_results/cycle_*.md` | Per-cycle metadata, scores, LOC deltas. |
| Refactor-loop state | `.refactor-state/codex_history.jsonl` (478 cycles) + `task_results/cycle_*.md` | Far sparser cycle markdowns than compress; main refactor history is in commit messages tagged `refactor:`. |
| Autonomous-loop state | `.prover-state/` | Referenced in `autonomous_loop.py`; not in current Hyak working tree — confirm whether it was ever populated and where. |
| `aristotle-loop` state | check `.aristotle-loop-state/` or similar; failing that, `aristotle-loop:`-tagged commits on Apr 27 are the trail | NEW: This was a separate ~10-cycle infra experiment, distinct from the proving-phase Aristotle submissions. |

### 3.3 Cross-machine consolidation

The plan was originally written on the laptop and only listed laptop
sources; running it from Hyak (as we are now) inverts the missing
direction — the laptop sources have to come to Hyak (or vice versa).
Pick one machine as the analysis host and rsync the other side in.

If the analysis host is the laptop, scrape Hyak with:

```bash
#!/usr/bin/env bash
# Pull Hyak logs to laptop under artifacts/hyak-logs/
HYAK_HOST=hyak-klone     # or whichever login node has the most recent state
DEST=$HOME/Github/Clawristotle/artifacts/hyak-logs

mkdir -p "$DEST"
rsync -avz --include='*/' --include='*.jsonl' --exclude='*' \
  $HYAK_HOST:'.claude/projects/' "$DEST/claude-projects/"
rsync -avz $HYAK_HOST:'.codex/sessions/' "$DEST/codex-sessions/"
rsync -avz $HYAK_HOST:'.codex/history.jsonl' "$DEST/codex-history.jsonl"
rsync -avz $HYAK_HOST:'.codex/logs_2.sqlite' "$DEST/codex-logs.sqlite"
rsync -avz $HYAK_HOST:'/mmfs1/gscratch/amath/vilin/Clawristotle/.compress-state/' "$DEST/compress-state/"
rsync -avz $HYAK_HOST:'/mmfs1/gscratch/amath/vilin/Clawristotle/.refactor-state/' "$DEST/refactor-state/"
```

If the analysis host is Hyak (current working directory), scrape the
laptop instead:

```bash
LAPTOP=vasil@laptop  # define an SSH alias
DEST=/mmfs1/gscratch/amath/vilin/Clawristotle/artifacts/laptop-logs

mkdir -p "$DEST"
rsync -avz $LAPTOP:'~/.claude/projects/-Users-vasil-Github-Clawristotle/' "$DEST/claude-Clawristotle/"
rsync -avz $LAPTOP:'~/.claude/projects/-Users-vasil-Github-aristotle/'    "$DEST/claude-aristotle/"
rsync -avz $LAPTOP:'~/.codex/sessions/'      "$DEST/codex-sessions/"
rsync -avz $LAPTOP:'~/.codex/history.jsonl'  "$DEST/codex-history.jsonl"
rsync -avz $LAPTOP:'~/.codex/logs_2.sqlite'  "$DEST/codex-logs.sqlite"
# CRITICAL: capture aristotle-in/out before any cleanup — these are
# the only record of the 94-job proving-phase activity.
rsync -avz $LAPTOP:'~/Github/Clawristotle/aristotle-in/'  "$DEST/aristotle-in/"
rsync -avz $LAPTOP:'~/Github/Clawristotle/aristotle-out/' "$DEST/aristotle-out/"
```

### 3.4 Token / cost accounting

- **Claude Code**: each assistant message in jsonl carries a `message.usage` block
  with `input_tokens`, `cache_creation_input_tokens`, `cache_read_input_tokens`,
  `output_tokens`, plus the `model` name. Same as VML.
- **Codex**: this is the tricky one. Need to inspect a Codex session jsonl to
  see whether token usage is recorded per turn. If not, fall back to:
  - Codex sqlite `logs_2.sqlite` (check `feedback_log_body` for usage records).
  - Per-cycle estimates from `.compress-state/codex_history.jsonl` if it logs them.
  - Last resort: rough estimate from message counts × average tokens.
- **Pricing tables** (per million tokens): keep in a small `scripts/pricing.py`,
  versioned by model name. Apply the relevant model per message.

---

## 4. Methodology & Tooling

### 4.1 Re-point the existing `_gv` scripts

The `scripts/*_gv.py` family was written for GV during the proving phase
on the laptop, with the pre-rename project name baked in. They are not
VML scripts — but they only see the laptop / pre-rename slice. Each one
needs:

- Repo path: parameterize (laptop `~/Github/Clawristotle`, Hyak
  `/mmfs1/gscratch/amath/vilin/Clawristotle`).
- Claude session source: union of laptop pre-rename
  (`-Users-vasil-Github-aristotle`), laptop post-rename
  (`-Users-vasil-Github-Clawristotle`), and Hyak
  (`-mmfs1-gscratch-amath-vilin-Clawristotle`).
- Date window: `2026-03-27 → HEAD` (not Mar 27 – Apr 5; the existing
  cutoff stops at the proving-phase boundary and misses the entire
  Codex / mathlib-style refactor era).
- Output filename: keep `_gv.png` — the suffix is not a misnomer, the
  data window just needs widening.

### 4.2 New scripts to write

- `scripts/report/codex_token_usage.py` — parse Codex sessions (laptop + Hyak) for token usage and cost.
- `scripts/report/cycle_effectiveness.py` — parse `.compress-state/codex_history.jsonl` (86 cycles) and `.refactor-state/codex_history.jsonl` (478 cycles) to chart per-cycle LOC delta, success rate, stuck-on reasons.
- `scripts/report/loop_mode_attribution.py` — classify each commit by loop mode (interactive / babysit / autonomous_loop / aristotle-loop / codex_compress / codex_refactor / mathlib-style cleanup / docs / wip) and produce a Gantt + summary table.
- `scripts/report/scrape_logs.sh` — see §3.3 (covers both directions).
- `scripts/report/build_metrics_table.py` — emit the headline metrics row, given all the inputs above. Source of truth for the table at the top of the report.

### 4.3 Dedup / merge strategy

The same conversation may appear on both machines if state was copied. Dedup by `session_id` (jsonl filename or first-line `sessionId` field). Annotate each session with `{machine: laptop|hyak, tool: claude|codex}` for the per-machine and per-tool splits.

### 4.4 Phase boundaries

The four phases in §2.3 are the working hypothesis. Derive precise boundaries from commit-rate breakpoints (changepoint detection on daily commit count) and confirm against the milestone events listed there.

---

## 5. Authors & Credits

These are the credits to bake into the report. Source: `README.md:37–43`,
PR #15 description, and user confirmation on 2026-04-30.

- **[Vasily Ilin](https://github.com/Vilin97) (Human)** — Architect &
  reviewer; ran the loops; owns the repo and infrastructure.
- **[Brian Nugent](https://github.com/brian-nugent) (Human)** — Wrote
  the **initial theorem statement**, supplied the Hartshorne III.2.7
  proof reference and the **flasque vanishing architecture**, and **did
  the review**. The agent built on his Mathlib PR #35790 code.
- **[Claude Code](https://claude.com/claude-code) (Agent)** — Engineer
  & prover. Drove the proving phase interactively and via
  `/babysit` / autonomous-loop modes.
- **[Codex CLI](https://openai.com/codex) (Agent)** — Compress and
  refactor loops in the late-April phase (86 + 478 cycles).
- **[Aristotle](https://aristotle.harmonic.fun/) (ATP)** — Lemma
  specialist; ~94 submissions in the proving phase.

---

## 6. Open Questions for User Feedback

(The original §5 list. Several earlier items have been resolved by the
user's 2026-04-30 corrections and pulled out; what remains:)

1. **Hyak coverage.** Confirm which login node has the most current
   `.codex/sessions/` and whether Hyak ran Claude Code, Codex, or both.
   Plan currently assumes Codex on Hyak (all the late-April loops),
   Claude on both.
2. **Aristotle data location.** Confirm whether the laptop still has
   `aristotle-in/aristotle-out/` from the proving phase. If it was
   cleaned up, the report falls back to the PR #15 totals (94 / 22
   proved / 66 with sorry / 5 canceled / 1 failed) without per-job
   timestamps.
3. **Phase narrative.** Are the four phases in §2.3 the right cut, or
   should the proving phase be sub-divided by mathematical milestone
   (closed-immersion, flasque, filtered-colimit)?
4. **Mathlib-style refactor (commit `6bce95f` / PR #27).** Treat as its
   own phase (current plan) or fold into the late-April refactor era?
5. **Cost vs tokens.** Pricing changed over the ~5-week window — use
   the price effective on each call's date, or one fixed price (latest)
   for the whole project?

---

## 7. Suggested Order of Work

Each step is independent enough to push as one commit; later steps depend on
earlier ones only for the final report assembly.

1. **Inventory.** Walk laptop Claude project dirs (both names) + Hyak Claude project dir + all Codex sessions on both machines + state dirs; produce a `data_manifest.json` listing every input file with size, date range, machine, tool. (Sanity-check that we're not missing data before building anything.)
2. **Cross-machine scrape.** Run the appropriate direction from §3.3, including capturing `aristotle-in/aristotle-out/` from the laptop before any cleanup.
3. **Headline metrics.** Build `metrics.json` from all sources. Verify against ground truth (`git rev-list --count`, file counts, etc.).
4. **Re-point + re-run existing `_gv` graphs** (LOC, sorry, churn, dep-graph, session, token, tool-use) for the full GV window (Mar 27 → HEAD), with merged Claude session sources.
5. **New graphs**: cycle effectiveness, loop-mode timeline, tool/machine split heatmap, raw-vs-normalized LOC.
6. **Token/cost analysis**, including Codex.
7. **Narrative & phases.** Write prose; cross-reference graphs.
8. **Final assembly.** New file `TECHNICAL_REPORT_GV.md` — the existing `TECHNICAL_REPORT.md` is on the don't-touch / unreliable list and stays for historical reference until the new one is in place.

---

## 8. Risks / Things That Might Break

- **Codex schema unknown.** If Codex jsonl doesn't expose token usage, we'll need to estimate, which weakens cost claims.
- **Cross-machine SSH.** If Hyak↔laptop scraping needs interactive 2FA, it has to be a one-shot manual run rather than scripted from inside the report build.
- **Project rename gap.** Some laptop sessions may straddle the `aristotle → Clawristotle` rename and split awkwardly. Need a sanity check that no session is double-counted nor lost across `-Github-aristotle/` and `-Github-Clawristotle/`.
- **Aristotle data may already be gone.** If `aristotle-in/aristotle-out/` was deleted from the laptop, we lose per-job timestamps and have to fall back to PR #15 totals.
- **Pricing drift over 5 weeks.** Claude pricing changed during the GV window; using flat pricing may over/under-state cost (less severe than originally feared with a hypothetical 4-month window).
- **Refactor commit volume (~453).** High cardinality; plots may need to bin by day rather than per-commit.

---

*Draft prepared 2026-04-30 by the laptop agent; revised 2026-04-30 on
Hyak after user feedback (timeline, Aristotle, authorship). Awaiting
further feedback before implementation begins.*
