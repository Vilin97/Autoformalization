# /golf — One cycle of code compression (loop-friendly)

Execute ONE meaningful simplification, verify it compiles, and commit. Designed for `/loop 10m /golf`.

**Hard rules:**
- A no-op cycle is NEVER acceptable. There is always something to improve.
- Everything must compile at default heartbeats after your change.
- Deleting comments or docstrings does not count.
- One cycle = one coherent change = one commit.

## Step 1: Pick the highest-impact action you haven't tried

Read the current line count: `wc -l <project>/main/*.lean | sort -rn | head -6`

Then pick from this list, IN ORDER. Skip categories that have been exhausted in recent cycles (check git log).

### Tier 1: Structural (target: 30–100+ lines per cycle)

**1a. Extract a repeated proof pattern into a helper lemma.**
Search: `grep -c 'PATTERN' main/*.lean` for patterns like:
- `epi_unit_of_closedImmersion` — closed complement SES construction
- `ShortComplex.mk.*kernel.ι` — kernel/cokernel SES boilerplate
- `topologicalKrullDim_lt_of_isIrreducible` — dimension arguments
- `sheaf_isZero_of_zero_stalks` — stalk-vanishing-to-IsZero

If any pattern appears 3+ times, extract a helper parameterized over the differences. Place it in the earliest common import. Replace all call sites.

**1b. Replace a hand-rolled proof with Mathlib API.**
Search for proofs that manually build something Mathlib provides:
- Use `lean_leansearch`, `lean_loogle`, `lean_leanfinder` to search
- 20+ line proofs of "standard" facts are prime candidates
- Check if `simp` or `exact?` can close goals that currently use manual `rw` chains

**1c. Generalize a lemma to subsume multiple specializations.**
If lemma A is a special case of lemma B, and B is easy to prove, delete A and use B everywhere. Common examples:
- Presheaf version + sheaf version → prove presheaf version, derive sheaf version in 1 line via `toSheafify`
- `finsetCoproductIncl` (specific) vs `finsetCoproductInclGen` (general) → keep only the general one

**1d. Merge induction cases that share 80%+ of their proof.**
Extract the shared structure as a parameterized lemma. Each case becomes a 2–3 line application.

### Tier 2: Medium (target: 5–30 lines per cycle)

**2a. Inline single-use `have`/`let`/`set` bindings.**
Find with: `grep -n 'have \w\+ :=' main/*.lean` then check if used once.
- `have X := Y; exact Z X` → `exact Z Y`
- `set X := Y with hX; ... rw [hX] ...` where hX used once → inline Y
- `have X : T := rfl; rw [X]` → delete (rfl rewrites are no-ops)

**2b. Move declarations to fix import structure.**
If a helper is defined late but needed early, move it to a shared ancestor file. This unblocks other simplifications.

**2c. Remove dead code.**
`grep -c 'DECL_NAME' main/*.lean` — if a non-instance declaration appears only at its definition, delete it.

### Tier 3: Local golf (target: 3–15 lines per cycle)

**3a. Merge `intro x` with the following tactic via semicolons.**
```bash
grep -Pn '^\s+intro \w+$' main/*.lean
```
Merge: `intro x; by_cases`, `intro x; obtain`, `intro x; rw`, `intro x; exact`, etc.
Do ALL of them in one cycle (they're safe and mechanical).

**3b. Compress `constructor; intro a b` → `⟨fun a b => by ...⟩`.**

**3c. Convert `by exact X` → `X` (term-mode).**

**3d. Merge sequential `simp only` calls.**

**3e. Compress `cases e; rfl` onto one line.**

## Step 2: Execute the change

- Edit the files
- Delete stale `.olean` files for modified modules: `rm -f .lake/build/lib/lean/<path>.olean`
- Rebuild: `lake build 2>&1 | grep error | head -10`
- If errors: fix them. If unfixable after 3 attempts, REVERT and pick a different action.

## Step 3: Commit via /commit

Use the `/commit` skill. The commit message should state:
- Net lines saved (e.g., "-42 lines")
- What was done (e.g., "extract closedComplementVanishing helper, replace 3 call sites")
- Files changed

## Step 4: Report

End with a one-line summary: `[TIER X] -N lines: <what was done>. Total: YYYY lines.`

If you completed a Tier 3 action, note: "Tier 1–2 opportunities may remain — check git log for what's been tried."
