Commit and push all changes.

Steps:

1. Run `lake build` on the main theorem files to verify compilation (sorry warnings OK, errors NOT OK). If the build fails, fix the errors first — do NOT commit broken code.

2. Stage all changed files in `Aristotle/Landau/` and `.claude/commands/`. Do NOT stage:
   - `.env` or other secrets
   - Large binary files
   - Files in `.claude/` other than commands

3. Write a concise commit message summarizing what changed (sorry count, files added/split/deleted, proofs closed, etc.).

4. Push to the current branch.
