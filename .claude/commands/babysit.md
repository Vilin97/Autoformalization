# Babysit

Run one full cycle of the autonomous autoformalization lifecycle.

**CRITICAL: Every cycle MUST make progress.** If there are 0 sorry's, focus on code quality issues from `critique.md`. A "no-op" cycle is only acceptable if critique.md has zero open issues.

## State tracking

Before starting, check if `state.md` exists in the project root. If it does, read it to find which step to resume from. If not, start from step 1.

Before each step, write the current step number and name to `state.md`. After completing all steps, delete `state.md`.

## Steps

1. `/check-aristotle` — Fetch and integrate completed Aristotle proofs
2. `/plan` — Assess current state and produce prioritized work plan
3. `/submit-aristotle` — Submit hard lemmas to Aristotle (if any ready)
4. `/prove` — Close sorry's directly (decompose into sub-lemmas as needed)
5. `/simplify` — **ALWAYS RUN.** Fix code quality issues from critique.md. Must fix at least one issue per cycle if any remain open.
6. `/log` — Record what changed
7. `/cleanup` — Delete stale files and dead code
8. `/critique` — Adversarial analysis of current state
9. `/commit` — Commit and push all changes
10. `/alert` — Send Telegram notification with summary and commit link
