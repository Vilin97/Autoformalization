You are the planner for cycle $cycle of a Codex refactoring loop.

Your job is to choose the next unchecked item from `.refactor-state/review_tasks.md` and write a precise one-cycle strategy to `.refactor-state/codex_strategy.md`.

Read these files first:
- `.refactor-state/review_tasks.md`
- `.refactor-state/principles.md`
- `.refactor-state/attempts.md`
- `.refactor-state/history.jsonl`
- `.refactor-state/codex_history.jsonl` if it exists

Recent history:
$history

Rules:
- Only target checklist items that are still `- [ ]`.
- Respect phase order. Do not jump to later phases while earlier-phase unchecked items remain unless the earlier item is clearly blocked and you explicitly say why.
- If the earliest unchecked item is an umbrella/sweep task rather than a declaration-anchored task, do not target the umbrella item directly. Instead, pick the highest-priority concrete declaration-anchored subtask in the same phase that advances it, or explicitly declare the umbrella item non-actionable for one cycle and move to the next concrete hard item.
- Hard-item priority: while any unchecked item remains in Phases 1-4, do not choose polish, golf, docstring, naming, or file-placement cleanup from Phases 5-6 unless it is a necessary prerequisite for one specific unchecked Phase 1-4 item.
- If the previous 2 cycles on the same checklist item earned only partial progress (`+1` or `0`), either decompose the item into a sharper enabling sub-task or declare it blocked and move to the next hard item.
- Prefer fully completing one checklist item. If that is too large, choose a single enabling sub-task that is explicitly in service of exactly one unchecked item.
- Avoid approaches already shown to be dead ends in attempts/history.
- Be concrete about current files, current declarations, signatures, likely Mathlib lemmas, and verification commands. Treat stale line numbers in the checklist as historical only.
- Do not modify any file except `.refactor-state/codex_strategy.md`.

Write `.refactor-state/codex_strategy.md` with this exact structure:

# Cycle $cycle Strategy

## Checklist Items
- Copy each targeted unchecked checklist line here verbatim.

## Why This Task
- One short paragraph.
- Explicitly say why this is higher priority than any available polish task.

## Approach
1. Concrete step.
2. Concrete step.
3. Concrete step.

## Avoid
- Dead-end approach 1.
- Dead-end approach 2.

## Verification
- Exact `lake env lean ...` commands to run.
- Say whether `lake build` is also required.

## Scope Limit
- State what counts as success for this cycle and what is out of scope.
- If this is an enabling sub-task rather than full completion, name the exact parent checklist item it serves.
