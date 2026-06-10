# Automation Suite: Loops and Slash Commands for the GV Project

This document collects the loop modes and slash commands that drove the
Grothendieck-Vanishing formalization. Five distinct loop modes ran across
~5 weeks (2026-03-27 → 2026-05-01), on two machines (laptop and Hyak),
through three AI tools (Claude Code, Codex CLI, Aristotle).

---

## Loop modes and cycle counts

| Loop | Tool | Phase | Machine | Cycles | First → last |
|---|---|---|---|---|---|
| `/babysit` | Claude Code | Proving | Laptop | many (interactive) | 2026-03-27 → 2026-04-04 |
| `autonomous_loop` | Claude Code | Proving / docs | Laptop | scripted, untracked count | 2026-03-27 → 2026-04-07 |
| `aristotle-loop` | Aristotle (via custom infra) | Proving / infra | Laptop | ~10 cycles, ~7 commits | 2026-04-27 |
| `codex_compress_loop` | Codex CLI (worker) + Claude Code (evaluator) | Compress | Hyak | **86** | 2026-04-27 → 2026-04-28 |
| `codex_refactor_loop` | Codex CLI (worker) + Claude Code (evaluator) | Refactor | Hyak | **478** | 2026-04-19 → 2026-04-27 |
| Mathlib-style cleanup | Claude Code (interactive + agents) | Polish | Both | per-PR | 2026-04-29 → 2026-05-01 |

The Codex loops invoke Codex with `exec --ephemeral`, which does **not** persist
session jsonl files; Codex's per-cycle token cost is therefore not directly
recoverable from `~/.codex/sessions/`. The Claude side of the same loops
(structured-output evaluator runs) is fully captured in
`~/.claude/projects/-mmfs1-gscratch-amath-vilin-Clawristotle/`.

---

## `/babysit` — main interactive proving loop

Cycles through critique → plan → submit-Aristotle → prove → check-Aristotle →
simplify → strengthen → log → cleanup → commit → alert. **Every cycle must
make progress**; "no-op" cycles are unacceptable while sorries remain.

Steps (each is a separate slash command, run in order):

1. `/critique` — adversarial review against `critique.md`
2. `/plan` — prioritized work plan against `plan.md`
3. `/submit-aristotle` — package and submit hard lemmas to Aristotle
4. `/prove` — close sorries directly, decomposing into sub-lemmas
5. `/check-aristotle` — fetch and integrate completed Aristotle proofs
6. `/simplify` — fix code-quality issues from `critique.md`
7. `/strengthen` — weaken hypotheses, strengthen conclusions
8. `/log` — record what changed
9. `/cleanup` — delete stale files / dead code
10. `/commit` — commit and push (always to `wip/grothendieck-vanishing`)
11. `/alert` — Telegram notification with summary + commit link

State tracking: `state.md` in repo root records current step number;
`/babysit` resumes from there if it exists.

---

## `autonomous_loop`

Driver script `scripts/autonomous_loop.py`. Runs Claude Code headlessly
with a fixed system prompt, executing one full proof iteration per
invocation. Used during the proving phase as a non-interactive variant
of `/babysit`.

---

## `aristotle-loop`

A late-April infrastructure experiment that batched Aristotle submissions
through a dedicated loop, distinct from the proving-phase Aristotle calls.
Visible as `aristotle-loop:`-tagged commits on 2026-04-27. This loop did
not produce new mathematical content; it shook out Aristotle integration
issues.

---

## `codex_compress_loop`

Driver: `scripts/codex_compress_loop.py` + `scripts/run_codex_compress_loop.sh`.

Each cycle:

1. **Worker run** — Codex CLI (`codex exec --ephemeral`) attempts to
   compress one or more files in `Aristotle/GrothendieckVanishing/`,
   targeting normalized LOC reduction without changing semantics.
2. **Gate** — `lake env lean` verifies the modified files still compile.
3. **Evaluator run** — Claude Code (with `--json-schema`) scores progress
   on a 0-3 scale, records LOC delta, sorry counts before/after, and
   suggests strategy for the next cycle.
4. **Persist** — append a row to `.compress-state/codex_history.jsonl`
   and write `.compress-state/codex_task_results/cycle_N.md`.

86 cycles ran 2026-04-27 → 2026-04-28, reducing normalized LOC from
~7,016 to ~4,087 (raw LOC: ~5,500 → ~5,000) without changing the
mathematical content or introducing sorries.

---

## `codex_refactor_loop`

Driver: `scripts/codex_refactor_loop.py` + supervisor script.

Same structure as compress loop, but the worker prompt targets *style*
(Mathlib conventions, naming, docstrings) rather than line count.

478 cycles ran 2026-04-19 → 2026-04-27. Most produced small, individually
mergeable commits tagged `refactor:`.

---

## Mathlib-style cleanup (PR #27)

A focused cleanup phase combining interactive Claude Code with the
`/critique` slash command for style adherence. Outputs: docstrings,
namespace fixes, lint clean-up. Captured in commit `6bce95f`
("mathlib-style refactor: docstrings, naming, lint-clean").

---

## Tools referenced

- **Claude Code** — primary driver for interactive proving and the
  evaluator side of the Codex loops.
- **Codex CLI** — worker for compress / refactor loops.
- **Aristotle (Harmonic)** — automated theorem prover, used for hard
  lemmas via `/submit-aristotle` and the `aristotle-loop` infra burst.
- **Lean LSP / Mathlib** — all loops gate on `lake env lean` succeeding.

The slash commands themselves live in user-level Claude Code config
(`~/.claude/commands/` or shipped with the binary); only project-level
`/alert` and `/commit` are checked into the repo at `.claude/commands/`.
