# Project Notes

The goal is not to end up with 0 sorry's! The goal is to make an honest formalization of the main theorem, with only the genuinely needed mathematical/physical assumptions. It is okay to have some sorry's laying around, as long as their statements are actually mathematically correct.

## Main file: `Aristotle/Landau/Theorem42.lean`

- The main theorem (`Theorem42`) must be stated cleanly at the end of the file with only the necessary mathematical hypotheses — no extra assumptions.
- Sorry's in the proof body are lemmas to be proved, not missing hypotheses.

## Files

Update these files after major changes:

- `progress.md` and `MEMORY.md` describe the project progress
- `critique.md` gives the critique of the current state, pointing to the weakest links

## Proof style

- Decompose results into lemmas. Make lemmas more general than the specific result they serve — this is often easier to prove and leads to better design.
- Prefer `by sorry` for gaps that will be filled, not `axiom`.

## Aristotle workflow

- Non-trivial lemmas go to `Aristotle/Landau/aristotle-in/` as standalone files (self-contained, `import Mathlib`, single sorry'd lemma).
- Submit with: `aristotle prove-from-file FILE --output-file aristotle-out/NAME_aristotle.lean --no-wait`. Before submitting to Aristotle, make sure the file has no errors and in particular, that the syntax is correct. The file submitted to aristotle must have sorry's but it must have no errors. DO NOT use `axiom`, instead if a lemma is not to be attempted, state the lemma and close it by `admit` instead of `sorry`.
- API key is in `.env`.
- If Aristotle proves it: integrate the proof into the main file, delete the submission.
- If Aristotle times out: decompose the lemma into smaller pieces and resubmit.
- If Aristotle proves the negation: fix the lemma statement (missing hypotheses, wrong conclusion, etc.).

## Gemini

- For planning and reasoning tasks, especially requiring large context or heavy mathematical reasoning, call Gemini. Use `gemini-3.1-pro-preview`.

## Cleanup

From time to time run cleanup:

- Delete the files that are no longer needed, e.g. Aristotle's proofs that have already been processed and integrated in the main file. Do make sure that the file(s) you are deleting is no longer needed.
- Extract self-contained lemmas from the main theorem (e.g. with `extract_goal`), and attempt to prove them independently. Important: ensure the lemmas are actually correct!

## Building the project

Sometimes Lean decided to rebuild all Mathlib from scratch, which takes forever. If basic commands `lake build` take >30 seconds, that's why. In this case, run

1. `lake clean` to clean build outputs
2. `lake update` to update dependencies and save them to manifest
3. `lake exe cache get` to fetch Mathlib cache
4. `lake build` to ensure it worked

Also, sometimes the lean-lsp-mcp is being weird, you can run `lake build` for a more reliable output.
