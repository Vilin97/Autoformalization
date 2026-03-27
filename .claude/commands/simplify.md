Systematically fix code quality issues identified in `critique.md` and in the codebase.

**Rule: If any non-FIXED issue exists in `critique.md`, you MUST work on at least one per cycle.** "All issues are too hard" is not acceptable — pick the easiest one and fix it.

## Phase 1: Read critique.md and identify open issues

Find the active project directory: the subdirectory of `Aristotle/` that contains `main/` (e.g. `Aristotle/GrothendieckVanishing/`). All paths below are relative to this directory.

Read `critique.md`. Extract every issue that is NOT marked as ~~strikethrough~~ or **FIXED**. These are your work items.

Also scan `main/*.lean` for:
- Files over 600 lines (`wc -l`)
- `set_option maxHeartbeats` above 800000
- Proofs over 50 lines
- Duplicate definitions across files
- `import Mathlib` (should be granular imports)

Merge the scan results with critique issues (deduplicate).

## Phase 2: Prioritize and pick a target

Rank issues by impact × feasibility:

| Priority | Type | Examples |
|----------|------|----------|
| 1 | Quick wins | Stale docs, unused imports, dead code |
| 2 | Bounded refactors | Consolidate duplicates, extract lemmas |
| 3 | File splits | Files >600 lines → split along logical boundaries |
| 4 | Heartbeat reduction | Decompose proofs, add type annotations |
| 5 | Architectural | Change definitions, redesign typeclasses |

Pick the highest-priority item you can make progress on. If the top item is blocked, skip to the next.

## Phase 3: Execute the fix

### For file splits (>600 lines):
1. Identify logical boundaries (group by mathematical topic)
2. Create new file with appropriate imports
3. Move declarations, preserving order
4. Add `import` in the original file
5. Build to verify both files compile

### For heartbeat reduction (>800000):
1. Use `lean_goal` to understand the proof structure
2. Extract `have` blocks >10 lines as standalone lemmas
3. Add explicit type annotations to reduce typeclass search
4. Replace `simp` with `simp only [...]`
5. Build to verify heartbeats decreased

### For duplicate definitions:
1. Identify which file should own the definition
2. Move definition to the owner file
3. Replace uses in other files with imports
4. Build to verify

### For stale documentation:
1. Check actual line counts, sorry counts, file lists
2. Update to match reality
3. Mark the critique issue as FIXED

### For `import Mathlib`:
1. Comment out `import Mathlib`
2. Build and collect errors
3. Add specific imports for what's actually needed
4. Build to verify

## Phase 4: Verify and update critique

- Build all modified files with `lake build`
- If the fix works, update `critique.md`: mark the issue as ~~strikethrough~~ **FIXED** with the cycle number
- If the fix partially works, update critique.md with the new status

## Code Smells Checklist (secondary — fix when encountered)

**Proof smells:**
- Non-terminal `simp` (use `simp only [...]`)
- Monolithic tactic scripts >50 lines (split with `have`/`obtain`)
- Duplicated proof patterns (extract shared lemma)

**Performance smells:**
- `set_option maxHeartbeats` above 800000
- Heavy `simp` calls without `only`
- Deep typeclass synthesis chains (add type annotations)

**Architecture smells:**
- Files over 600 lines (split by topic)
- Duplicate definitions across files
- Missing API lemmas for custom definitions

## Reference

See the project's `CLAUDE.md` for project conventions, if it exists.
