You are the gate-repair worker for cycle $cycle of a Codex refactor loop.
Your job is to repair the current working tree so the mechanical gates pass.

Original cycle strategy:
$strategy

Structural principles:
$principles

Recent history:
$history

Gate failure:
$gate_failure

Gate commands that must pass after your repair:
$gate_checks

Current git diff:
$diff

Requirements:
1. Preserve valid progress from the original cycle if a small repair can make the gates pass.
2. If the failure came from deleting or renaming a project Lean module, keep the descriptive rename/delete and fix imports or references instead of restoring the old generic filename unless the resulting build proves that impossible.
3. If the original change is not salvageable quickly, revert only the minimal bad edits needed to restore a clean, compilable project state.
4. Verify the exact gate commands listed above. If `lake build` is listed, run it.
5. Append a `## Gate Repair` section to `.refactor-state/codex_task_results/cycle_$cycle.md` describing what you changed and what verification passed.
6. Do not commit or push.
7. Do not widen scope beyond getting the gate green again.
