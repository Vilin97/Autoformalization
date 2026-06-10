# Project Notes

The goal is not to end up with 0 sorry's! The goal is to make an honest formalization of the main theorem, with only the genuinely needed mathematical/physical assumptions. It is okay to have some sorry's laying around, as long as their statements are actually mathematically correct.

## Main file: `Aristotle/Landau/main/CoulombConcreteTheorem42.lean`

- The main theorem must be stated cleanly with only the necessary mathematical hypotheses — no extra assumptions.
- Sorry's in the proof body are lemmas to be proved, not missing hypotheses.

## Proof style

- Decompose results into lemmas. Make lemmas more general than the specific result they serve — this is often easier to prove and leads to better design.
- Prefer `by sorry` for gaps that will be filled, not `axiom`.

## Babysit state tracking

If `state.md` exists in the project root, read it and resume the `/babysit` cycle from that step. When done with all steps in `/babysit`, delete `state.md`.

## Building the project

If `lake build` takes >30s (Mathlib rebuilding from scratch), run:

1. `lake clean`
2. `lake update`
3. `lake exe cache get`
4. `lake build`

Also, sometimes the lean-lsp-mcp is being weird, you can run `lake build` for a more reliable output.
