Analyze the current state and produce a prioritized work plan.

This is NOT just about closing sorry's — it covers all issues: sorry's, code quality, documentation, architectural problems, and anything from `critique.md`.

## Steps

### 1. Gather state

- Read `Aristotle/Landau/critique.md` for known issues.
- Grep for `sorry` across `Aristotle/Landau/main/*.lean` to find remaining gaps.
- Check `Aristotle/Landau/aristotle-jobs.json` for pending/failed jobs.
- Scan for code smells: files over 600 lines, proofs over 50 lines, `maxHeartbeats` above 800000.
- Check documentation accuracy in `critique.md`.

### 2. Classify issues

For each issue, assign a category and priority:

| Priority | Category | Examples |
|----------|----------|---------|
| P0 | Compilation errors | Build failures, type errors |
| P1 | Completeness | Sorry's in the main theorem, missing instances |
| P2 | Epistemic | Overly strong hypotheses, hidden assumptions |
| P3 | Code quality | High heartbeats, oversized files/proofs, code smells |
| P4 | Documentation | Stale counts, inaccurate descriptions |

### 3. For each sorry, assess the approach

- **Direct proof** (< 30 min): simple Mathlib argument, algebraic identity, one-liner.
- **Decompose + prove** (30 min – 2 hrs): split into sub-lemmas, prove each.
- **Submit to Aristotle**: non-trivial lemma that Aristotle might handle.
- **Blocked**: depends on another sorry or on Aristotle results.

### 4. Output the plan

Write a numbered work plan to stdout. Each item has:
- What to do
- Which file(s) to touch
- Estimated approach (direct / decompose / Aristotle / blocked)
- Dependencies (what must be done first)

Do NOT execute the plan — just output it. The user or `/babysit` will decide what to execute.
