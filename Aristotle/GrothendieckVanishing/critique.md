# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-02T18:20Z
**Reviewer verdict**: CONDITIONAL PASS

## 0. CI Status

Latest CI run (push dd87a8d) is **in_progress**. Previous runs both **green**.
Local `lake build` succeeds with 0 errors.

**Docs deployment is BROKEN**: both `https://vilin97.github.io/aristotle/blueprint/` and
`https://vilin97.github.io/aristotle/blueprint/dep_graph_document.html` return **HTTP 404**.

**Assessment**: P1 — docs are inaccessible.

## 1. Sorry's (1)

One `sorry` at `IrreducibleStep.lean:1245` in `ext_comm_filtered_colimit_mono`.

The comment at line 1236 says "This is the ONLY axiom in the formalization". This is
**misleading terminology**: it is not a Lean `axiom` declaration, it is a `theorem` with
`sorry`. Calling it an "axiom" obscures the fact that it is an unproved claim.

The statement IS mathematically true (Hartshorne III.2.9). No risk of falsity.

## 2. Hidden Axioms

None. No `admit`, `axiom`, `native_decide`, or linter/heartbeat overrides.

## 3. File Sizes

- `IrreducibleStep.lean`: **1582 lines** (over 1000-line guideline by 58%)

25 `private` declarations. Should be split: extract filtered diagram infrastructure
(~1238-1357) and finitely generated vanishing (~1359-1515) into a separate file.

## 4. Dead Code: Cascade Theorems

`sheafH_vanishing_succ` and `sheafH_vanishing_cascade` in `GrothendieckVanishing.lean`
are **private and never used** outside their own file. Neither is called from
`grothendieck_vanishing_aux` or `GrothendieckVanishing`. Dead code.

## 5. Documentation Issues

1. **GrothendieckVanishing.lean docstring** (line 23): says "m₀ ≥ 1" but
   `sheafH_vanishing_cascade` has NO such constraint — works for m₀ = 0.

2. **IrreducibleStep.lean line 1236**: "ONLY axiom" should say "ONLY sorry".

3. **CLAUDE.md** code tree lists `FiniteGeneratorReduction.lean` as a child of
   `IrreducibleStep.lean`, but this file does NOT exist. Stale.

4. **CLAUDE.md** line 65 references "Existing violations in SetupCore.lean" but
   there are none. Stale (carried over from previous critique).

## 6. Generalization Opportunities

1. **Drop NoetherianSpace from cascade theorems**: `sheafH_vanishing_succ` doesn't
   use `NoetherianSpace` — remove the unneeded `[NoetherianSpace X]` hypothesis.
   **Feasibility: trivial.**

2. **Drop mono condition from sorry**: Hartshorne III.2.9 states the result WITHOUT
   mono transitions. The mono condition is not necessary for the mathematical truth.
   **Feasibility: hard (proof infrastructure not in Mathlib).**

3. **Generalize to arbitrary Grothendieck topologies**: The theorem currently works
   for `Opens.grothendieckTopology` on `TopCat`. The cascade theorems already work
   for arbitrary sites. The sorry could be stated for general sites too.
   **Feasibility: moderate.**

## 7. Mathlib Upstreamability

1. **Cascade theorems**: General facts about Ext + injective presentations. Could go
   to `Mathlib.CategoryTheory.Sites.SheafCohomology` after making non-private and
   dropping `NoetherianSpace`.

2. **Filtered diagram of finitely generated subsheaves**: `finsetGenFunctor` etc.
   could be useful for other colimit arguments on Noetherian spaces.

## 8. Open Issues

| # | Priority | Issue |
|---|----------|-------|
| 1 | P0 | Sorry in `ext_comm_filtered_colimit_mono` (line 1245) |
| 2 | P1 | Docs/blueprint return 404 |
| 3 | P2 | IrreducibleStep.lean at 1582 lines — split |
| 4 | P2 | Dead code: cascade theorems unused |
| 5 | P3 | Misleading "axiom" comment (line 1236) |
| 6 | P3 | Stale CLAUDE.md (nonexistent FiniteGeneratorReduction.lean, stale heartbeat ref) |
| 7 | P3 | Docstring "m₀ ≥ 1" inaccurate |
