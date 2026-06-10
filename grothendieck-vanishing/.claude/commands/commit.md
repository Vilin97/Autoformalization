Commit and push all changes via the `wip/grothendieck-vanishing` branch.

The `grothendieck-vanishing` branch is protected: direct pushes are blocked, and the `build` CI check must pass before merging. Agents work on `wip/grothendieck-vanishing` and push there freely. A single PR from `wip/grothendieck-vanishing` → `grothendieck-vanishing` stays open with auto-merge enabled; it merges automatically once CI is green.

Steps:

1. Ensure you are on `wip/grothendieck-vanishing`. If not, switch to it:
   ```bash
   git checkout wip/grothendieck-vanishing || git checkout -b wip/grothendieck-vanishing
   ```

2. Identify all modified `.lean` files (via `git status`). Force a rebuild of each by deleting its `.olean` and rebuilding:
   ```
   for f in <modified files>; do
     mod=$(echo "$f" | sed 's|/|.|g; s|\.lean$||')
     rm -f .lake/build/lib/lean/${f%.lean}.olean
     lake build "$mod" 2>&1 | grep "error"
   done
   ```
   This catches errors that `lake build` might miss with stale cache. Sorry warnings OK, errors NOT OK. If any file fails, fix the errors first — do NOT commit broken code.

   If no `.lean` files were modified, run `lake build` as a basic sanity check.

3. Stage all changed files in the active project directory (e.g. `Aristotle/GrothendieckVanishing/`), `.claude/commands/`, and `tools/`. Do NOT stage:
   - `.env` or other secrets
   - Large binary files
   - Files in `.claude/` other than commands

4. Write a concise commit message summarizing what changed (sorry count, files added/split/deleted, proofs closed, etc.).

5. Commit and push:
   ```bash
   git add <files>
   git commit -m "<message>"
   git push -u origin wip/grothendieck-vanishing
   ```

6. Ensure a PR exists from `wip/grothendieck-vanishing` → `grothendieck-vanishing` with auto-merge:
   ```bash
   # Check if a PR already exists
   existing=$(gh pr list --head wip/grothendieck-vanishing --base grothendieck-vanishing --json number -q '.[0].number')
   if [ -z "$existing" ]; then
     gh pr create --base grothendieck-vanishing --head wip/grothendieck-vanishing --title "wip: grothendieck-vanishing" --body "Persistent working PR. Auto-merges when CI passes."
     gh pr merge --auto --squash
   fi
   ```
   The PR auto-merges once CI passes. After merge, sync before continuing:
   ```bash
   git pull origin grothendieck-vanishing
   ```
