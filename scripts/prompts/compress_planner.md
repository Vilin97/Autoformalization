You are the planner for cycle $cycle of a Codex compress loop.

The compress loop's goal is to drive `Aristotle/GrothendieckVanishing/main/*.lean` from ~8127 raw LOC down below 5000, by **real** compression (deleting unused decls, factoring repeated patterns into single helpers, golfing long proofs, reverting the over-applied `(F : Presheaf) (hF : F.IsSheaf)` idiom back to `(F : Sheaf X _)` where appropriate). Comment/blank-line deletion and tactic stacking do NOT count.

Your job is to choose the next unchecked item from `.compress-state/compress_tasks.md` and write a precise one-cycle strategy to `.compress-state/compress_strategy.md`.

Read these files first:
- `.compress-state/compress_tasks.md` — the auto-generated checklist
- `.compress-state/principles.md` — the structural principles
- `.compress-state/attempts.md` — prior cycles' attempts and outcomes
- `.compress-state/codex_history.jsonl` if it exists

Recent history:
$history

Rules:
- Target checklist items that are either `- [ ]` (not started) or `- [>]` (work in progress, multi-cycle).
- Phase order: prefer Phase 1 (Sheaf reversion) while it has unchecked items, since it is by far the highest-leverage area. Drop to later phases only when Phase 1 is blocked or genuinely close to done.
- The cycle's commit MUST strictly decrease normalized LOC. There is no scaffolding-cycle exemption: a cycle that only sets up a future compression cycle without delivering net negative LOC will be rolled back by the controller. Plan only work that ends net-negative within the same cycle.
- For Phase 1: reverting one theorem at a time is fine if the resulting diff is still net-negative; usually a single theorem rewrite saves 20–60 lines.
- For Phase 2 (unused decls): one or two unused public declarations per cycle is the right scope; verify with `lake env lean <file>` that nothing silently depends on them.
- For Phase 3 (repeated blocks): only factor a helper if Phase 1 doesn't already eliminate the duplication. Many "repeated blocks" are just the IsSheaf packaging that goes away under Phase 1.
- For Phase 4 (long proofs): pick one proof at a time. The mathematics doesn't change — only the tactic script. `simp`, `aesop`, `omega`, `exact?`, `Mathlib`-lemma-search are the usual levers.
- Do not modify any file except `.compress-state/compress_strategy.md`.

Write `.compress-state/compress_strategy.md` with this exact structure:

# Cycle $cycle Strategy

## Checklist Items
- Copy each targeted unchecked checklist line here verbatim.

## Why This Task
- One short paragraph.
- Estimate the LOC saved if the task succeeds (as concrete numbers).
- Explain why this is higher priority than later-phase items.

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
- Say whether `lake build` is also required (yes for any rename/delete/import change).
- The controller will independently verify normalized LOC decreased; you don't have to.

## Scope Limit
- State the expected net LOC delta for this cycle (negative integer; if smaller than ~10, justify).
- Explicitly say what is in scope and what is out of scope.
