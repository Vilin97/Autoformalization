# Automation Suite: Slash Commands for Semi-Autonomous Formalization

This document collects all the slash commands that defined the `/babysit` automation loop. These were stored in `.claude/commands/` and invoked by Claude Code as custom skills. The loop ran for 122 documented cycles over 10 days.

---

## `/babysit` — The Main Loop

Run one full cycle of the autonomous autoformalization lifecycle.

**CRITICAL: Every cycle MUST make progress.** If there are 0 sorry's, focus on code quality issues from `critique.md`. A "no-op" cycle is only acceptable if critique.md has zero open issues.

**CRITICAL: Every step below MUST be executed.** Do not skip steps. Even if a step has "nothing to do", run the command and let it determine that.

### State tracking

Before starting, check if `state.md` exists in the project root. If it does, read it to find which step to resume from. If not, start from step 1.

Before each step, write the current step number and name to `state.md`. After completing all steps, delete `state.md`.

### Steps

1. `/critique` — Adversarial analysis of current state
2. `/plan` — Assess current state and produce prioritized work plan
3. `/submit-aristotle` — Submit hard lemmas to Aristotle (if any ready)
4. `/prove` — Close sorry's directly (decompose into sub-lemmas as needed)
5. `/check-aristotle` — Fetch and integrate completed Aristotle proofs
6. `/simplify` — Fix code quality issues from critique.md. Must fix at least one issue per cycle if any remain open.
7. `/strengthen` — Improve mathematical content: weaken hypotheses, strengthen conclusions, resolve epistemic issues from critique.md. Must make meaningful progress each cycle.
8. `/log` — Record what changed
9. `/cleanup` — Delete stale files and dead code
10. `/commit` — Commit and push all changes
11. `/alert` — Send Telegram notification with summary and commit link

---

## `/critique` — Adversarial Review

You are a hostile reviewer trying to REJECT this formalization. Your job is to find every weakness, gap, and dishonesty. Do not be polite. Do not give credit. Do not soften your language. If you catch yourself writing "mitigating factor" or "well-addressed", stop and ask whether a reviewer would actually accept that mitigation.

Write the full adversarial critique to `Aristotle/Landau/critique.md` with the exact timestamp.

**CRITICAL: There is ALWAYS something to improve.** Even if the formalization has 0 sorry's, perfect code quality, and Mathlib-level generality, there is still work to do. Your job is to find it. Examples of issues that always exist:

- Can hypotheses be weakened? (e.g., C^inf -> C^2, strict positivity -> a.e. positivity, T^3 -> general compact manifold)
- Can the conclusion be strengthened? (e.g., uniqueness, rate of convergence, stability)
- Are there unnecessary hypotheses that could be dropped entirely?
- Could the proof strategy be generalized to cover more kernels (soft potentials, moderately soft)?
- Are there Mathlib PRs that could be extracted from this work?
- Is the formalization future-proof against Mathlib API changes?
- Could the typeclass design be improved for reuse?

**You MUST produce a non-empty list of open issues.** "Everything is perfect" is NEVER an acceptable conclusion.

### Mandatory sections

For EACH of the following, either find a real problem or explicitly state "I found no issue" (do not skip silently):

0. **CI status** — run `gh run list --branch landau --limit 3` to check the latest CI runs. A failing CI is P0.
1. **Sorry's** — List every `sorry` with file:line. For each: is the statement actually true? Could Aristotle prove the negation?
2. **Hidden axioms** — Every `admit`, `axiom`, `native_decide`. Run `lean_verify` on the main theorems. List every axiom beyond `propext`, `Classical.choice`, `Quot.sound`.
3. **Circularity** — Trace the full dependency chain. Is any hypothesis equivalent to the conclusion?
4. **Hypothesis audit** — List every hypothesis of the main theorem. For each: is it necessary? Could it be weakened?
5. **Mathematical correctness** — Are there ANY steps where the formalization diverges from the standard mathematical proof?
6. **Code quality** — `maxHeartbeats` above 800000, files over 600 lines, unmaintainable proofs.
7. **Documentation lies** — Check every numerical claim against reality.
8. **Generalization opportunities** — What would it take to weaken hypotheses or strengthen conclusions? At least 3 items.
9. **Mathlib upstreamability** — Which lemmas could be PR'd to Mathlib?

### Tone

Write as if you are a referee who has been asked "should this paper be accepted?" and your default answer is NO. End with a verdict: ACCEPT, CONDITIONAL ACCEPT, REVISE, or REJECT.

---

## `/plan` — Prioritized Work Planning

Analyze the current state and produce a prioritized work plan. Write it to `Aristotle/Landau/plan.md`.

**CRITICAL RULE: The plan MUST contain at least one actionable item that you can execute RIGHT NOW.** "Waiting for Aristotle" is not a plan. **"Nothing to do" is NEVER an acceptable output.**

### Priority classification

| Priority | Category | Examples |
|----------|----------|---------|
| P0 | Compilation errors | Build failures, type errors |
| P1 | Completeness | Sorry's in the main theorem, missing instances |
| P2 | Epistemic | Overly strong hypotheses, hidden assumptions |
| P3 | Code quality | High heartbeats, oversized files/proofs, code smells |
| P4 | Documentation | Stale counts, inaccurate descriptions |

**There is no "blocked" category.** If a sorry depends on another sorry, decompose it so that the dependency is explicit and you can work on the pieces independently.

---

## `/prove` — Hands-On Theorem Proving

Prove sorry's directly. This is hands-on theorem proving — not planning (use `/plan`) and not Aristotle submission (use `/submit-aristotle`).

**CRITICAL RULE: You MUST make concrete progress on at least one sorry every time this command runs.** "All sorry's are too hard" is NOT acceptable. If the sorry is hard:
- Decompose it into 3-5 sub-lemmas. Prove at least one sub-lemma.
- If sub-lemmas are still hard, decompose further until you reach something provable.
- Even replacing `by sorry` with `by have h1 := sorry; have h2 := sorry; exact sorry` is progress if h1 and h2 are well-chosen intermediate claims.

**Aristotle submission does NOT excuse you from working on the proof.** Always work on sorry's in parallel with Aristotle.

### Steps

1. **Pick a target** — Read `critique.md` for priorities. Grep for `sorry`. Pick the highest-priority sorry.
2. **Understand the goal** — Use `lean_goal` to see the proof state. Read the context.
3. **Search for Mathlib lemmas** — `lean_local_search`, `lean_leansearch`, `lean_loogle`, `lean_state_search`, `lean_hammer_premise`.
4. **Attempt the proof** — Use `lean_multi_attempt` to try tactics. Edit incrementally. Use `lean_goal` to verify.
5. **Decompose if stuck** — Extract sub-goals as standalone lemmas. Prove what you can.
6. **Verify** — Run `lean_diagnostic_messages`. Confirm no new errors.

---

## `/submit-aristotle` — Automated Theorem Prover Submission

Prepare and submit lemmas to Aristotle for automated proving.

### Pre-submission checklist

1. **File format**: Standalone `.lean` file in `aristotle-in/` with `import Mathlib`, exactly ONE sorry'd lemma, all dependencies proved inline or `admit`ted.
2. **Compilation check**: The file MUST compile without errors (sorry/admit warnings OK).
3. **Mathematical correctness**: The sorry'd statement must be actually true. Aristotle has proved negations when hypotheses were missing — e.g., missing measurability led to Vitali-set counterexamples.

### Handling failures

- **Aristotle returned sorry**: Decompose into smaller sub-lemmas and resubmit.
- **Aristotle proved the negation**: The statement is FALSE. Fix and resubmit.
- **Job expired**: Resubmit if still needed.

---

## `/check-aristotle` — Process Completed Results

Check the status of all Aristotle jobs and process completed results.

1. Run the tracking script to check pending jobs and download solutions.
2. For completed jobs with 0 sorry's: integrate the proof into `main/`.
3. For jobs with sorry's remaining: report what was proved and what's still sorry'd.
4. For negated statements: fix the lemma and resubmit.
5. For jobs still running: report status.

---

## `/simplify` — Code Quality Fixes

Systematically fix code quality issues identified in `critique.md` and in the codebase.

**Rule: If any non-FIXED issue exists in `critique.md`, you MUST work on at least one per cycle.**

### Targets

- Files over 600 lines -> split along logical boundaries
- `set_option maxHeartbeats` above 800000 -> decompose proofs, add type annotations
- Duplicate definitions across files -> consolidate
- Non-terminal `simp` -> `simp only [...]`
- Monolithic tactic scripts >50 lines -> split with `have`/`obtain`

---

## `/strengthen` — Mathematical Improvement

Improve the mathematical content of the formalization by addressing open issues from `critique.md` that are NOT about code quality and NOT about closing sorry's.

`/prove` handles sorry's. `/simplify` handles code quality. `/strengthen` handles everything else: hypothesis minimality, conclusion strength, circularity, generalization, epistemic gaps.

**Do not default to the easiest item.** Weigh impact against effort honestly. An ambitious change that requires experimentation is fine — a failed experiment that rules out an approach is still progress.

---

## `/cleanup` — Delete Stale Files

Delete stale files and dead code. Do NOT do code simplification here (that's `/simplify`).

1. Delete stale Aristotle output files already integrated into `main/`.
2. Delete stale Aristotle input files whose jobs completed.
3. Check for dead code: unused lemmas, commented-out code, stale imports.

---

## `/log` — Record Progress

Write what was done since the last timestamp in `Aristotle/Landau/LOG.md`.

Rules:
- Entries are in reverse chronological order (newest first).
- Each entry has a timestamp and concise summary.
- Record: what was accomplished, what was submitted to Aristotle, what sorry's were closed, what remains.
- Include the current sorry count.

---

## `/commit` — Commit and Push

1. Rebuild all modified `.lean` files (delete `.olean` and rebuild to catch stale cache issues).
2. Stage all changed files. Do NOT stage `.env` or secrets.
3. Write a concise commit message.
4. Push to the current branch.

---

## `/alert` — Telegram Notification

Send a Telegram alert summarizing what was done in this babysit cycle.

1. Get the latest commit hash and message.
2. Build the GitHub diff URL.
3. Compose a 1-2 sentence summary.
4. Send via Telegram bot API.
