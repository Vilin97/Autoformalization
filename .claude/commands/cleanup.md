Delete stale files and dead code. Do NOT do code simplification here (that's `/simplify`).

Steps:

1. **Delete stale Aristotle output files:**
   - Check `aristotle-out/` for files already integrated into `main/`
   - Verify each file is truly no longer needed before deleting

2. **Delete stale Aristotle input files:**
   - Check `aristotle-in/` for files whose jobs completed and results were integrated
   - Keep files whose jobs are still pending or need resubmission

3. **Check for dead code in main files:**
   - Unused lemmas, commented-out code, stale imports in the project's `main/` directory
   - Unused inline definitions (e.g. primed variants no longer needed)

Report what was deleted and what was kept, with reasons.
