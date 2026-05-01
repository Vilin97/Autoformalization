# GV Report Data

Structured extracts feeding the GV technical report. Generated 2026-05-01 per
`REPORT_PLAN.md` §7 step 1 (inventory) + step 3 (headline metrics).

## Files

```
report-data/
├── data_manifest.json         # row counts, sizes, date ranges per source
├── metrics.json               # headline metrics (mirrors REPORT_PLAN §2.1)
├── raw/
│   └── aristotle/projects.json   # full API dump (1350 jobs)
└── extracted/
    ├── claude_turns_laptop.jsonl     # 18,919 rows
    ├── claude_turns_hyak.jsonl       # 12,610 rows
    ├── codex_turns_laptop.jsonl      # 1 row (only 1 GV session has token blocks)
    ├── codex_turns_hyak.jsonl        # 287 rows across 4 GV sessions
    ├── cycle_history_compress.jsonl  # 86 cycles (Apr 27–30)
    ├── cycle_history_refactor.jsonl  # 478 cycles
    └── commits.jsonl                 # 904 commits since 2026-03-27
```

## Schemas

### `claude_turns_*.jsonl` — one row per assistant turn with `usage`

```
{machine, project, session_id, ts, model,
 input_tokens, cache_creation_input_tokens, cache_read_input_tokens, output_tokens}
```

Sources: `~/.claude/projects/-Users-vasil-Github-{Clawristotle,aristotle}/`
on the laptop (the `aristotle` dir is pre-rename, holds the proving phase),
and `/mmfs1/home/vilin/.claude/projects/-mmfs1-gscratch-amath-vilin-Clawristotle/`
on Hyak.

### `codex_turns_*.jsonl` — one row per Codex turn carrying token info

```
{machine, cwd, session_file, ts,
 tt_input, tt_cached_input, tt_output, tt_reasoning_output, tt_total,    # cumulative
 lt_input, lt_cached_input, lt_output, lt_reasoning_output, lt_total}    # last call
```

Filtered to GV cwd only. **Caveat:** the compress (86 cycles) and refactor
(478 cycles) loops invoke Codex with `exec --ephemeral`, which does NOT
persist sessions. Token usage for those cycles is not in this file (or
anywhere else recoverable). The 5 sessions captured here are interactive
Codex use, not the loops.

### `cycle_history_compress.jsonl` / `cycle_history_refactor.jsonl`

```
{cycle, timestamp, worker_exit_code, sorry_before, sorry_after,
 loc_before, loc_after, loc_delta, raw_loc_after, completed_task_lines,
 gate_repair_attempted, gate_repair_exit_code, evaluation: {...}}
```

(Refactor schema is leaner — no LOC fields, just cycle/timestamp/exit/sorry/eval.)

### `commits.jsonl` — git log walk

```
{sha, ts, author, subject, files_changed, insertions, deletions}
```

`git log wip/grothendieck-vanishing --since=2026-03-27 --numstat`.

### `aristotle/projects.json` — full Aristotle API dump

```
[{id, status, created, updated, pct, file_name, description, input_prompt}, …]
```

1,350 entries. **Filter to GV** before any per-job figure — see
`REPORT_PLAN.md` §2.3 for the rules. Quick filters:
- `2026-03-27 ≤ created ≤ 2026-04-04` → 94 jobs (matches PR #15 exactly).
- `file_name` substring in `{clawristotle, aristotle-loop, flasque,
  irreducible, grothendieck, constant_sheaf, closed_immersion,
  zero_outside}` → 31 jobs (deduplicated).

## Reproducing

Re-run with `ARISTOTLE_API_KEY` set and SSH access to `klone-login`.
The full extraction logic is inline in the conversation that produced
this directory; convert it to `scripts/report/extract_data.py` if you
want a one-shot rebuild.

## Caveats / known gaps

- **Codex worker tokens for the compress/refactor cycles are lost** to
  the `--ephemeral` flag. Estimating these requires a one-off measured
  re-run of one cycle, scaled by cycle count.
- **Codex sqlite** (`logs_2.sqlite`) was *not* extracted here — it
  covers Apr 16–24 only and is auxiliary to the session jsonl. Worth
  digging into if the ephemeral-cycle gap matters.
- **Aristotle filter is approximate.** ~49 `cycle_*`-named jobs are
  ambiguous between GV and the augmented B-series project; final
  attribution requires prompt-text inspection (see §2.3 decision rule).
- The cycle history `date_range` shows `null` in the manifest because
  the field is `timestamp`, not `ts` — read it directly from the file.
