Commit and push all changes.

Steps:

1. Identify all modified `.lean` files (via `git status`). Force a rebuild of each by deleting its `.olean` and rebuilding:
   ```
   for f in <modified files>; do
     mod=$(echo "$f" | sed 's|/|.|g; s|\.lean$||')
     rm -f .lake/build/lib/lean/${f%.lean}.olean
     lake build "$mod" 2>&1 | grep "error"
   done
   ```
   This catches errors that `lake build` might miss with stale cache. Sorry warnings OK, errors NOT OK. If any file fails, fix the errors first — do NOT commit broken code.

   If no `.lean` files were modified, run `lake build` as a basic sanity check.

2. Stage all changed files in the active project directory (e.g. `Aristotle/GrothendieckVanishing/`), `.claude/commands/`, and `tools/`. Do NOT stage:
   - `.env` or other secrets
   - Large binary files
   - Files in `.claude/` other than commands

3. Write a concise commit message summarizing what changed (sorry count, files added/split/deleted, proofs closed, etc.).

4. Push to the current branch.
