# Babysit

Run one full cycle of the autonomous autoformalization lifecycle.

**CRITICAL: Every cycle MUST make progress.** If there are 0 sorry's, focus on code quality issues from `critique.md`. A "no-op" cycle is only acceptable if critique.md has zero open issues.

**CRITICAL: Every step below MUST be executed.** Do not skip steps. Even if a step has "nothing to do", run the command and let it determine that.

## State tracking

Before starting, check if `state.md` exists in the project root. If it does, read it to find which step to resume from. If not, start from step 1.

Before each step, write the current step number and name to `state.md`. After completing all steps, delete `state.md`.

## Steps

1. `/critique` — Adversarial analysis of current state
2. `/plan` — Assess current state and produce prioritized work plan
3. `/submit-aristotle` — Submit hard lemmas to Aristotle
4. `/prove` — Close sorry's directly (decompose into sub-lemmas as needed)
5. `/check-aristotle` — Fetch and integrate completed Aristotle proofs
6. `/log` — Record what changed
7. `/cleanup` — Delete stale files and dead code
8. `/commit` — Commit and push all changes
9. `/alert` — Send Telegram notification with summary and commit link
