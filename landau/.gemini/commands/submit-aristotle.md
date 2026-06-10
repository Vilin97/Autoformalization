Prepare and submit lemmas to Aristotle for automated proving.

## Input

Accepts an optional argument: a comma-separated list of sorry names or file paths to submit. If no argument is given, check for ready-to-submit files in `aristotle-in/` and submit them.

## Pre-submission checklist

For each lemma to submit:

1. **File format**: Must be a standalone `.lean` file in `Aristotle/Landau/aristotle-in/` with:
   - `import Mathlib` at the top (self-contained, no project imports)
   - Exactly ONE sorry'd lemma (the target)
   - All dependencies either proved inline or `admit`ted (NEVER use `axiom`)
   - Add `-- Harmonic \`generalize_proofs\` tactic` comment at the top to prevent Aristotle from injecting its custom tactic
   - Keep the file as short as possible — Aristotle works better with less context

2. **Compilation check**: The file MUST compile without errors. Sorry warnings and admit warnings are fine, syntax/type errors are NOT. Verify with `lake build` or `lean_diagnostic_messages`.

3. **Mathematical correctness**: The sorry'd statement must be actually true. Check:
   - Are all necessary hypotheses present? (Aristotle has proved negations when hypotheses were missing — e.g., missing measurability led to Vitali-set counterexamples)
   - Is the conclusion correctly stated?
   - If unsure, use `lean_goal` to inspect the goal state, or consult Gemini for mathematical review.

## Submission

Submit using the tracking script (handles job ID recording automatically):

```bash
cd /home/vilin/aristotle && source .env && python3.10 Aristotle/Landau/check-aristotle.py submit aristotle-in/NAME.lean
```

**IMPORTANT: Use `python3.10`, NOT `python`.** The default `python` is 3.7, which is too old for `aristotlelib`.

## Handling failures

### API is down (httpx.ReadTimeout, connection refused, curl returns 000)
- Report that the API is unreachable.
- Keep the input file in `aristotle-in/` for later resubmission.
- Do NOT retry in a loop — just report and move on.
- Consider proving the lemma directly instead (see `/prove`).

### Submission script errors
- "Could not find project ID in output" — the `aristotle` CLI may not be installed or the API key in `.env` may be invalid. Check with `which aristotle` and verify `.env` exists.
- Python import errors — ensure `aristotlelib` is installed under python3.10: `python3.10 -m pip install aristotlelib`.

### Job completed but Aristotle returned sorry
- The lemma was too hard for Aristotle. Decompose it into smaller sub-lemmas and resubmit each.
- Consider what building blocks Aristotle might need as `admit`ted helpers.

### Job completed but Aristotle proved the negation
- The lemma statement is FALSE. Common causes:
  - Missing hypothesis
  - Wrong types
  - Slightly incorrect conclusion
- Fix the statement and resubmit.

### Job expired (500 error on status check)
- The job timed out on Aristotle's end. Mark as "expired" in `aristotle-jobs.json`.
- Resubmit if the lemma is still needed.

## Post-submission

- Verify the job ID was recorded in `Aristotle/Landau/aristotle-jobs.json`.
- Report what was submitted and the job ID.
