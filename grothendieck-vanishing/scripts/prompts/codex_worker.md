You are the worker for cycle $cycle of a Codex refactoring loop.
You are working on a Lean 4 + Mathlib formalization of Grothendieck vanishing.

Strategy for this cycle:
$strategy

Structural principles:
$principles

Requirements:
1. Read the strategy and the relevant source files first.
2. Work only on the targeted checklist item(s) or the explicitly named enabling sub-task.
3. Use Lean LSP MCP tools when they help you move faster or avoid blind proof attempts.
4. Keep the project at 0 sorrys and 0 custom axioms.
5. Verify every modified Lean file with `lake env lean <file>`.
6. If the change is broad or touches imports/API used across many files, also run `lake build`.
7. Write `.refactor-state/codex_task_results/cycle_$cycle.md` with:
   - What was done
   - What changed
   - Verification performed
   - What remains, if anything
8. Do not update `.refactor-state/review_tasks.md` yourself.
9. Do not commit or push; the loop controller handles that.

Execution policy:
- Prefer finishing one unchecked item completely.
- A `- [>]` item means multi-cycle work in progress; the loop will keep returning to it until its `COMPLETE_IF:` criterion passes. Continue from where prior cycles left off rather than re-planning it.
- If the assigned checklist item is an umbrella/sweep item, still work on a concrete declaration-anchored subtask only; do not spend the cycle on a vague audit.
- Prefer hard unchecked Phase 1-4 work over polish. Do not spend the cycle on golfing, docstrings, naming cleanup, or small wrapper deletion unless the strategy explicitly identifies it as necessary for one named harder unchecked item.
- Do not spend a cycle on linter-warning cleanup while concrete unchecked Phase 1-4 items remain.
- If blocked, leave the repo clean and compilable, and explain the blocker precisely.
- Do not pad the cycle with unrelated cleanup.
