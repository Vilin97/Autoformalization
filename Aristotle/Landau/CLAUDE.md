# Project Notes

## Main file: `Aristotle/Landau/landau-steady-state.lean`

- The main theorem (`Theorem42`) must be stated cleanly at the end of the file with only the necessary mathematical hypotheses — no extra assumptions.
- Sorry's in the proof body are lemmas to be proved, not missing hypotheses.

## Proof style

- Decompose results into lemmas. Make lemmas more general than the specific result they serve — this is often easier to prove and leads to better design.
- Prefer `by sorry` for gaps that will be filled, not `axiom`.

## Aristotle workflow

- Non-trivial lemmas go to `Aristotle/Landau/aristotle-in/` as standalone files (self-contained, `import Mathlib`, single sorry'd lemma).
- Submit with: `aristotle prove-from-file FILE --output-file aristotle-out/NAME_aristotle.lean --no-wait`
- API key is in `.env`.
- If Aristotle proves it: integrate the proof into the main file, delete the submission.
- If Aristotle times out: decompose the lemma into smaller pieces and resubmit.
- If Aristotle proves the negation: fix the lemma statement (missing hypotheses, wrong conclusion, etc.).
