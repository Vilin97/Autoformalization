Check the status of all Aristotle jobs and process completed results.

## Finding the project directory

The current project lives under `Aristotle/` — look for the subdirectory that contains `main/` and `aristotle-jobs.json` (e.g. `Aristotle/GrothendieckVanishing/`). All paths below are relative to that project directory.

## Steps

1. Read `aristotle-jobs.json` to find pending jobs (those without `"status": "done"`, `"expired"`, or `"failed"`).

2. For each pending job, check its status using the Aristotle MCP tool:
   ```
   mcp__aristotle__get_status(project_id="<job-id>")
   ```

3. For each completed job:
   a. Download the result:
      ```
      mcp__aristotle__download_result(project_id="<job-id>", destination="/absolute/path/to/aristotle-out/NAME_aristotle.lean")
      ```
      Or for tar.gz results, extract:
      ```
      mcp__aristotle__extract_result(project_id="<job-id>", extract_to="/absolute/path/to/aristotle-out/")
      ```
   b. Check if the proof has 0 sorry's (grep for `sorry` excluding comments).
   c. If 0 sorry's: integrate the proof into the appropriate file in `main/`. Add necessary imports, add bridge lemmas with `rfl`-based equality proofs if needed, and verify the file compiles.
   d. If sorry's remain: report what was proved and what's still sorry'd. Consider whether to decompose and resubmit.

4. For jobs that failed: report the failure and consider decomposing the lemma into smaller pieces for resubmission.

5. If Aristotle proved the negation, fix the lemma statement and resubmit.

6. For jobs still running: just report their status and percent complete.

7. After processing, update `aristotle-jobs.json` and report a summary table of all jobs.

## Listing all projects (optional)

To see recent Aristotle projects across the account:
```
mcp__aristotle__list_projects(limit=10)
```

Filter by status:
```
mcp__aristotle__list_projects(limit=10, status_filter="IN_PROGRESS,QUEUED")
```
