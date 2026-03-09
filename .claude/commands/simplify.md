Review changed code for reuse, quality, and efficiency, then fix any issues found.

Systematically simplify and decompose Lean files to improve compilation performance, readability, and maintainability.

## Targets

1. **No file over ~600 lines.** Split along logical/mathematical boundaries.
2. **No proof over ~50 lines.** Extract helper lemmas with clear names.
3. **No `set_option maxHeartbeats` above 800000.** If needed, the proof is doing too much work — decompose it.

## Procedure

### Phase 1: Identify problems

Scan `Aristotle/Landau/main/*.lean` for:
- Files over 600 lines (`wc -l`)
- Proofs over 50 lines (count lines between `:= by` and the next top-level declaration)
- `set_option maxHeartbeats` above 800000
- Code smells (see checklist below)

### Phase 2: Plan splits

For each oversized file, identify logical boundaries for splitting:
- Group definitions and their API lemmas together
- Group related lemmas by mathematical topic (e.g., "Coulomb kernel bounds", "Schwartz decay estimates", "flux integrability")
- Keep the main theorem file thin — it should mostly assemble pre-proved lemmas
- New files import predecessors; avoid circular dependencies

For each oversized proof, identify extractable sub-goals:
- `have` blocks with 10+ lines of proof → extract as standalone lemma
- Repeated patterns → extract as reusable lemma
- `calc` steps with heavy justifications → extract the justification

### Phase 3: Execute refactors

For file splits:
1. Create the new file with appropriate imports
2. Move declarations, preserving order
3. Add `import` in the original file
4. Verify both files compile

For proof decomposition:
1. Use `lean_goal` to identify the exact type of the sub-goal
2. Extract as a `private lemma` (or public if reusable) with explicit hypotheses
3. Replace the inline proof with `exact new_lemma ...` or `apply new_lemma`
4. Verify heartbeats decrease

### Phase 4: Verify

- Run `lean_diagnostic_messages` on all modified files
- Confirm no new errors (sorry warnings are fine)
- Confirm heartbeat requirements decreased

## Code Smells Checklist

Fix these when encountered:

**Proof smells:**
- [ ] Non-terminal `simp` (use `simp only [...]` or `simp?` to pin lemmas)
- [ ] Monolithic tactic scripts >50 lines (split with `have`/`obtain`/`show`)
- [ ] `erw` or extra `rfl` after `simp`/`rw` (missing API lemma — add one)
- [ ] `unfold`/`dsimp` exposing definition internals (use characteristic theorems instead)
- [ ] Duplicated proof patterns (extract shared logic into a lemma)

**Performance smells:**
- [ ] `set_option maxHeartbeats` above 800000 (decompose the proof)
- [ ] Heavy `simp` calls without `only` (pin the lemma set)
- [ ] Deep typeclass synthesis chains (add type annotations or `show` goals)
- [ ] `synthInstance.maxHeartbeats` overrides (simplify the typeclass problem)

**Architecture smells:**
- [ ] Files over 600 lines (split by mathematical topic)
- [ ] Re-proving Mathlib lemmas (use `exact?`, `apply?`, `lean_leansearch`)
- [ ] Missing API lemmas for custom definitions (add `@[simp]` lemmas)
- [ ] Definitions used only once with heavy unfolding (inline or add simp lemmas)

**Style smells:**
- [ ] Naming convention violations (types: `UpperCamelCase`, theorems: `snake_case`)
- [ ] Missing `variable` declarations (repeated explicit parameters)
- [ ] Unused imports or opens

## Reference

See `Aristotle/Landau/CLAUDE.md` for project conventions.
