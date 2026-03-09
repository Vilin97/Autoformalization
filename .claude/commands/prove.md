Systematically work on closing remaining sorry's and addressing issues from the critique.

Steps:

1. **Assess the current state:**
   - Read `Aristotle/Landau/critique.md` for known issues and priorities.
   - Grep for `sorry` across all files in `Aristotle/Landau/main/` to find remaining gaps.
   - Run `/check-aristotle` (via `source .env && python Aristotle/Landau/check-aristotle.py`) to check if any Aristotle jobs have completed and integrate results.

2. **Plan the attack:**
   - For each remaining sorry, assess: can it be proved directly (simple Mathlib argument), or does it need decomposition and Aristotle submission?
   - Consult the Gemini MCP (`mcp__gemini-cli__ask-gemini`) for planning complex proof strategies.
   - Prioritize: fix issues from critique.md in severity order (completeness > epistemic > scope > cosmetic).

3. **Attempt direct proofs:**
   - For simple sorry's (algebraic identities, bound calculations, Mathlib one-liners): try proving them directly using `lean_multi_attempt`, `lean_goal`, and `lean_completions`.
   - Use `lean_leansearch`, `lean_loogle`, `lean_leanfinder`, `lean_state_search`, and `lean_hammer_premise` to find relevant Mathlib lemmas.
   - If a direct proof works, edit the file to replace the sorry.

4. **Decompose and submit to Aristotle:**
   - For sorry's that are too complex to prove directly, decompose into smaller sub-lemmas.
   - Create standalone files in `Aristotle/Landau/aristotle-in/` (self-contained, `import Mathlib`, single sorry'd lemma).
   - Add `-- Harmonic \`generalize_proofs\` tactic` comment to avoid Aristotle injecting its custom tactic.
   - Verify each file compiles (sorry warnings OK, errors not OK) before submitting.
   - Submit via `source .env && python Aristotle/Landau/check-aristotle.py submit aristotle-in/NAME.lean`.

5. **Verify and report:**
   - After making changes, check diagnostics on modified files using `lean_diagnostic_messages`.
   - Report what was proved, what was submitted, and what remains.

Reference: See `Aristotle/Landau/CLAUDE.md` for Aristotle workflow rules and proof style guidelines.
