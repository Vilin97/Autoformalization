Run project cleanup:

1. **Delete stale Aristotle files:**
   - Check `aristotle-out/` for files that have already been integrated into `main/`
   - Check `aristotle-in/` for submissions whose results are already integrated or that are superseded by newer versions
   - Verify each file is truly no longer needed before deleting

2. **Delete stale input files:**
   - Check `aristotle-in/` for files that were superseded by v2/v3 versions and whose jobs have completed
   - Keep files whose Aristotle jobs are still pending

3. **Check for dead code in main files:**
   - Look for unused lemmas, commented-out code, or stale imports in `Aristotle/Landau/main/`

4. **Extract and attempt lemmas:**
   - Find remaining sorry's in `Aristotle/Landau/main/`
   - For each sorry, check if the statement is self-contained enough to extract
   - If so, create a standalone file in `aristotle-in/` and verify it compiles
   - Important: ensure extracted lemmas are actually mathematically correct

5. **Update tracking files:**
   - Update `progress.md` if the sorry count has changed
   - Update `MEMORY.md` if there are new architectural insights

Report what was deleted and what was kept, with reasons.
