You are the planner for cycle $cycle of a Codex compress loop.

The compress loop's goal is to drive `Aristotle/GrothendieckVanishing/main/*.lean` from ~8127 raw LOC down below 5000, by **real** compression (deleting unused decls, factoring repeated patterns into single helpers, golfing long proofs, reverting the over-applied `(F : Presheaf) (hF : F.IsSheaf)` idiom back to `(F : Sheaf X _)` where appropriate). Comment/blank-line deletion and tactic stacking do NOT count.

Your job is to choose the highest-leverage next target and write a precise one-cycle strategy to `.compress-state/compress_strategy.md`.

## ⚠️ Read the live audit FIRST

The controller has just regenerated `.compress-state/audit.md`. It contains the **current** state of the tree:
- per-file LOC,
- a **fresh** unused-decl scan (run this cycle, not at loop start),
- the list of `_presheaf` decls that still remain (Phase 1 leftovers),
- top long proofs by file with body/signature ratios,
- auto-detected status of each Phase 5 structural idea.

The static checklist `.compress-state/compress_tasks.md` is allowed to be stale — items there may have already been deleted by Phase-1 collateral, or new opportunities may have appeared that are not on the list. **Trust the audit over the checklist when they disagree.** When the audit and checklist agree, use the checklist line verbatim in the strategy so the loop can mark it done.

Live audit:

$audit

## Other inputs

- `.compress-state/principles.md` — structural principles
- `.compress-state/attempts.md` — prior cycles' attempts and outcomes
- `.compress-state/codex_history.jsonl` — full history if you need it

Recent history:
$history

## Target-selection rules

Pick the **single** target with the highest expected LOC delta this cycle. Use this priority order, but skip any item whose audit row is empty:

1. **Live unused-decl deletions** (audit "Unused public declarations" section). Each is a free deletion. Skip the auto-generated `IsFlasqueSheaf.{rec,casesOn,recOn}` and `zeroOutside*` projection equations — those are emitted by the structure/class definition and only disappear when the parent decl changes (handled via Phase 5 Idea 2).
2. **Open Phase 5 ideas** (audit reports `⬜ open` for each). These are usually higher-leverage than Phase 4 golf in the same area.
3. **Remaining `_presheaf` decls** (audit lists them with file:line). Reverting one to take `(F : Sheaf X _)` directly typically saves 20–60 normalized LOC per theorem.
4. **Long-proof golf** from the audit's "Top long proofs" section. Prefer high body lines and high body/signature ratio. The mathematics doesn't change — only the tactic script. `simp`, `aesop`, `omega`, `exact?`, Mathlib-lemma-search are the usual levers.
5. Only fall back to `compress_tasks.md` items NOT covered above if everything in 1-4 has been tried (rare).

## Hard rules

- The cycle's commit MUST strictly decrease normalized LOC. There is no scaffolding-cycle exemption: a cycle that only sets up a future compression cycle without delivering net negative LOC will be rolled back by the controller. Plan only work that ends net-negative within the same cycle.
- Pick exactly one target. Do not bundle.
- For Phase 1 (`_presheaf` reversion): rewriting one theorem at a time is fine if the resulting diff is still net-negative.
- For Phase 2 (unused decls): one or two unused public declarations per cycle is the right scope; verify with `lake env lean <file>` that nothing silently depends on them.
- For Phase 4 (long proofs): pick one proof at a time. Don't promise speculative `simp` simplifications you haven't checked are real.
- Do not modify any file except `.compress-state/compress_strategy.md`.

## Output format

Write `.compress-state/compress_strategy.md` with this exact structure:

# Cycle $cycle Strategy

## Target
- One sentence naming the chosen target (decl name + file path + line if applicable).
- Source: which audit section it came from (e.g. "audit / Unused public declarations" or "audit / Top long proofs").

## Checklist Items (if any)
- Copy each matching unchecked checklist line from `compress_tasks.md` here verbatim, OR write `(none — audit-driven, not in checklist)`.

## Why This Task
- One short paragraph.
- Estimate the LOC saved if the task succeeds (concrete number, not a range > 3x wide).
- Explain why this is higher leverage than the next-best alternative in the audit.

## Approach
1. Concrete step (name file, declaration, lines).
2. Concrete step.
3. Concrete step.

## Avoid
- Approaches already shown to be dead-end in attempts/history.
- Comment/blank-line deletion (gate ignores it).
- Tactic stacking via `;` or `<;>` (gate ignores it).
- Introducing a helper called from exactly one site.

## Verification
- Exact `lake env lean ...` commands to run.
- Say whether `lake build` is also required (yes for any rename/delete/import change, OR any deletion of a `@[simp]`/`@[gcongr]`/`@[ext]` decl).
- The controller will independently verify normalized LOC decreased; you don't have to.

## Scope Limit
- State the expected net normalized LOC delta for this cycle (negative integer; if smaller than ~10, justify).
- Explicitly say what is in scope and what is out of scope.
