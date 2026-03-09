Analyze the current state and produce a prioritized work plan.

**CRITICAL RULE: The plan MUST contain at least one actionable item that you can execute RIGHT NOW.** "Waiting for Aristotle" is not a plan. If all sorry's are submitted to Aristotle, then:
- Work on the sorry's yourself IN PARALLEL with Aristotle. Aristotle might fail. You are the backup.
- Decompose hard sorry's into sub-lemmas and prove what you can.
- Improve code quality: reduce heartbeats, split large files, clean up proofs.
- Fix documentation inaccuracies.
- Strengthen the formalization: weaken hypotheses, add missing edge cases.

**"Nothing to do" is NEVER an acceptable output.** If you think there's nothing to do, you haven't looked hard enough.

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
- **Already submitted but work on it anyway**: Aristotle is not reliable. Attempt the proof yourself in parallel.

**There is no "blocked" category.** If a sorry depends on another sorry, decompose it so that the dependency is explicit and you can work on the pieces independently.

### 4. Output the plan

Write a numbered work plan to stdout. Each item has:
- What to do
- Which file(s) to touch
- Estimated approach (direct / decompose / parallel-with-Aristotle)
- Dependencies (what must be done first)

The FIRST item must be something you can start immediately.

Do NOT execute the plan — just output it. The user or `/babysit` will decide what to execute.
