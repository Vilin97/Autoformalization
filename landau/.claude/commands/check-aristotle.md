Check the status of all Aristotle jobs and process completed results.

Steps:

1. Run `source .env && python Aristotle/Landau/check-aristotle.py` to check all pending jobs and download completed solutions.

2. For each completed job (newly downloaded to `aristotle-out/`):
   a. Check if the proof has 0 sorry's (grep for `sorry` excluding comments).
   b. If 0 sorry's: integrate the proof into the appropriate file in `Aristotle/Landau/main/`. Add `import Aristotle.Landau.main.Defs` if needed, add bridge lemmas with `rfl`-based equality proofs to connect standalone primed definitions to VML namespace definitions, and verify the file compiles.
   c. If sorry's remain: report what was proved and what's still sorry'd. Consider whether to decompose and resubmit.

3. For jobs that failed ("Aristotle failed to find a proof"): report the failure and consider decomposing the lemma into smaller pieces for resubmission.

4. If Aristotle proved the nagation, fix the lemma statement and resubmit.

5. For jobs still running: just report their status.

6. After processing, update `Aristotle/Landau/aristotle-jobs.json` if needed and report a summary table of all jobs.

Reference: See `Aristotle/Landau/CLAUDE.md` for the full Aristotle workflow rules.
