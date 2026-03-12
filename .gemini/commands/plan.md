Analyze the current state and produce a prioritized work plan. Write it to `Aristotle/Landau/plan.md`.

**CRITICAL RULE: The plan MUST contain at least one actionable item that you can execute RIGHT NOW.** "Waiting for Aristotle" is not a plan. If all sorry's are submitted to Aristotle, then:
- Work on the sorry's yourself IN PARALLEL with Aristotle. Aristotle might fail. You are the backup.
- Decompose hard sorry's into sub-lemmas and prove what you can.
- Improve code quality: reduce heartbeats, split large files, clean up proofs.
- Strengthen the formalization: weaken hypotheses, add missing edge cases.

**"Nothing to do" is NEVER an acceptable output.** If you think there's nothing to do, you haven't looked hard enough.

## Steps

### 1. Gather state

- Read `Aristotle/Landau/critique.md` for known issues.
- Read `Aristotle/Landau/plan.md` if it exists — build on previous plans, don't start from scratch. Drop items that are done. Keep multi-cycle strategies that are still in progress.
- Grep for `sorry` across `Aristotle/Landau/main/*.lean` to find remaining gaps.
- Check `Aristotle/Landau/aristotle-jobs.json` for pending/failed jobs.
- Scan for code smells: files over 600 lines, proofs over 50 lines, `maxHeartbeats` above 800000.

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

### 4. Brainstorm big moves

Consider whether any ambitious structural change could resolve multiple issues at once. Consult Gemini (`mcp__gemini-cli__brainstorm`) for ideas if the path forward is unclear. Think about:
- Changes to the theorem statement that would make the result stronger or more general
- Alternative proof strategies that might simplify the overall architecture
- Connections to other formalizations or Mathlib developments

### 5. Write the plan

Write the plan to `Aristotle/Landau/plan.md`. Structure:

- **Status summary**: sorry count, file count, top-level health
- **Active multi-cycle strategies**: ongoing efforts that span multiple babysit cycles (keep from previous plan if still relevant)
- **This cycle's work items**: numbered list, each with what to do, which file(s), estimated approach, and which step handles it (`/prove`, `/simplify`, `/strengthen`)
- **Backlog**: lower-priority items not planned for this cycle

The FIRST work item must be something that can start immediately.

Do NOT execute the plan — just write it. The subsequent `/babysit` steps will execute.
