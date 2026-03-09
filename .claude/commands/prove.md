Prove sorry's directly. This is hands-on theorem proving — not planning (use `/plan`) and not Aristotle submission (use `/submit-aristotle`).

## Scope

This command covers:
- Closing sorry's with direct proofs (Mathlib one-liners, algebraic identities, tactic chains)
- Decomposing sorry's into sub-lemmas and proving the sub-lemmas
- Introducing useful definitions that make proofs tractable
- Refactoring proof strategies (e.g., changing approach when stuck)

This command does NOT cover:
- Planning what to work on (use `/plan`)
- Submitting to Aristotle (use `/submit-aristotle`)
- Code simplification without closing sorry's (use `/simplify`)

## Steps

### 1. Pick a target

- Read `Aristotle/Landau/critique.md` for priorities.
- Grep for `sorry` in `Aristotle/Landau/main/*.lean`.
- Pick the highest-priority sorry that is feasible to prove directly (not blocked on other sorry's or Aristotle).
- If all remaining sorry's are hard, pick one and decompose it and work on it.

### 2. Understand the goal

- Use `lean_goal` to see the exact proof state at the sorry.
- Read the surrounding context (hypotheses, definitions used).
- Understand what mathematical fact is being asserted.

### 3. Search for Mathlib lemmas

Use search tools in this order:
1. `lean_local_search` — check if a relevant lemma already exists in the project.
2. `lean_leansearch` — natural language search ("integral of bounded function is bounded").
3. `lean_loogle` — type pattern search (`?a ≤ ?b → ∫ ?f ≤ ∫ ?g`).
4. `lean_leanfinder` — semantic/conceptual search.
5. `lean_state_search` — find lemmas that close the current goal.
6. `lean_hammer_premise` — find premises for `simp`/`aesop`.

### 4. Attempt the proof

- Use `lean_multi_attempt` to try multiple tactics without editing: `["simp", "ring", "omega", "exact?", "apply?"]`.
- For multi-step proofs, edit the file incrementally. Use `lean_goal` after each step to verify progress.
- For complex proofs:
  1. Start with `have` statements for intermediate claims.
  2. Prove each `have` separately.
  3. Combine with `exact` or `linarith` or `calc`.

### 5. Decompose if stuck

If a sorry can't be proved directly in ~15 minutes:
- Extract the sorry as a standalone `private lemma` above the current proof.
- Give it a descriptive name and explicit hypotheses (use `lean_goal` to get the exact type).
- Make the lemma more general than needed — this is often easier to prove and more reusable.
- Try to prove the new lemma. If still too hard, consider creating an Aristotle submission (use `/submit-aristotle`).

### 6. Verify

- After each sorry closed, run `lean_diagnostic_messages` on the modified file.
- Confirm no new errors (sorry warnings for OTHER sorry's are fine).
- Report: what was proved, what was decomposed, what remains.

## Reference

See `Aristotle/Landau/CLAUDE.md` for proof style guidelines.
