Prove sorry's directly. This is hands-on theorem proving — not planning (use `/plan`) and not Aristotle submission (use `/submit-aristotle`).

**CRITICAL RULE: You MUST make concrete progress on at least one sorry every time this command runs.** "All sorry's are too hard" or "blocked on Aristotle" are NOT acceptable outcomes. If the sorry is hard:
- Decompose it into 3-5 sub-lemmas. Prove at least one sub-lemma.
- If sub-lemmas are still hard, decompose further until you reach something provable.
- Even replacing `by sorry` with `by have h1 := sorry; have h2 := sorry; exact sorry` is progress if h1 and h2 are well-chosen intermediate claims.

**Aristotle submission does NOT excuse you from working on the proof.** Aristotle might fail, return sorry, or prove the negation. Always work on sorry's in parallel with Aristotle.

## Scope

This command covers:
- Closing sorry's with direct proofs (Mathlib one-liners, algebraic identities, tactic chains)
- Decomposing sorry's into sub-lemmas and proving the sub-lemmas
- Introducing useful definitions that make proofs tractable
- Refactoring proof strategies (e.g., changing approach when stuck)
- Proving helper lemmas that building blocks for sorry's (e.g., a `‖z‖⁻²` local integrability lemma)

This command does NOT cover:
- Planning what to work on (use `/plan`)
- Submitting to Aristotle (use `/submit-aristotle`)
- Code simplification without closing sorry's (use `/simplify`)

## Steps

### 1. Pick a target

- Read `Aristotle/Landau/critique.md` for priorities.
- Grep for `sorry` in `Aristotle/Landau/main/*.lean`.
- Pick the highest-priority sorry that is feasible to prove directly.
- **If all sorry's are hard: pick the hardest one and decompose it.** Do not skip this step.

### 2. Understand the goal

- Use `lean_goal` to see the exact proof state at the sorry.
- Read the surrounding context (hypotheses, definitions used).
- Understand what mathematical fact is being asserted.
- If the goal is too complex, identify which parts you CAN prove and which you need to decompose.

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
- Extract sub-goals as standalone lemmas above the current proof.
- Give each a descriptive name and explicit hypotheses (use `lean_goal` to get the exact type).
- Make lemmas more general than needed — this is often easier to prove and more reusable.
- Try to prove each new lemma. Close as many as you can.
- Any remaining sorry'd sub-lemmas are now smaller, better-defined targets for the next cycle.

**The goal of decomposition is to make measurable progress every cycle, even on hard proofs.** A sorry that was 1 opaque block is now 4 well-defined sub-lemmas, 2 of which are proved. That's real progress.

### 6. Verify

- After each sorry closed, run `lean_diagnostic_messages` on the modified file.
- Confirm no new errors (sorry warnings for OTHER sorry's are fine).
- Report: what was proved, what was decomposed, what remains.

## Reference

See `Aristotle/Landau/CLAUDE.md` for proof style guidelines.
