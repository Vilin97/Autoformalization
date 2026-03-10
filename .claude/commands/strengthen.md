Improve the mathematical content of the formalization by addressing open issues from `critique.md` that are NOT about code quality and NOT about closing sorry's.

`/prove` handles sorry's. `/simplify` handles code quality (heartbeats, file sizes, linter warnings, style, documentation, dead code). `/strengthen` handles everything else: hypothesis minimality, conclusion strength, circularity, generalization, epistemic gaps — anything about making the mathematics better.

## Phase 1: Identify targets

Read `Aristotle/Landau/critique.md`. Extract every open (non-strikethrough) issue. Discard issues that belong to `/prove` or `/simplify`. Everything remaining is a `/strengthen` target.

Also read `Aristotle/Landau/plan.md` — it may contain multi-cycle strategies or experimental results from previous cycles that inform what to attempt next.

## Phase 2: Think big, then decide

Before picking a target, consider whether multiple open issues share a common root cause that a single structural change could address. A large refactor that resolves 3 issues is better than 3 small patches. Examples:
- Weakening a function class might simultaneously resolve a non-minimality concern, a circularity worry, and a generalization opportunity
- Strengthening a conclusion might subsume several lesser issues

**Do not default to the easiest item.** Weigh impact against effort honestly. An ambitious change that requires experimentation is fine — use `Aristotle/Landau/experiments/` to prototype ideas without touching `main/`. A failed experiment that rules out an approach or reveals a subtlety is still progress worth documenting.

## Phase 3: Execute

- For changes ready for `main/`: edit files in `Aristotle/Landau/main/`, build to verify.
- For exploratory work: create files in `Aristotle/Landau/experiments/`. Document what you tried and what you learned.
- Leave sorry's for sub-lemmas that `/prove` or `/submit-aristotle` can handle later.
- Report what was accomplished and what remains.
- Do NOT update critique.md (that's `/critique`'s job).
