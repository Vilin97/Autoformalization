# Compress Loop Principles

These are the evaluator's primary criteria. Every cycle is judged against them.

## Principle 1: Real compression, not metric gaming

- Deleting comments or blank lines does NOT count as compression. The
  normalized-LOC metric ignores both, and the gate uses normalized LOC.
- Stacking tactics on one line via `;` or `<;>` does NOT count. The
  normalized-LOC metric splits on these.
- Replacing a clear lemma with an inscrutable one-liner is NOT compression
  even when it lowers the metric. The evaluator rejects spirit-violations.

EVALUATOR: REJECT cycles that lower the metric only by gaming.

## Principle 2: Sheaf, not Presheaf+IsSheaf

The previous refactor over-applied `(F : Presheaf X) (hF : F.IsSheaf)` as the
public idiom. Many lemmas should take `(F : TopCat.Sheaf AddCommGrpCat.{u} X)`
directly. The canonical illustration is `CohomologyAPI.lean:1734-1776`: a
43-line theorem packaging six `(F : Presheaf) (h : F.IsSheaf)` triples that
should be ~1 line if it took `(S : ShortComplex (Sheaf …))` directly.

- When a theorem packages `(⟨F, h⟩ : Sheaf …)` more than once in its body, take
  a `Sheaf` argument directly.
- When `hF : F.IsSheaf` is not used outside the `⟨F, h⟩` packaging, take a
  `Sheaf` argument directly.
- Keep `_presheaf` forms only where the call site genuinely cannot supply a
  bundled `Sheaf` (rare).

EVALUATOR: REWARD Sheaf-reversion cycles. REJECT new lemmas that re-introduce
the `(F : Presheaf X) (hF : F.IsSheaf)` triple where a `Sheaf` argument suffices.

## Principle 3: Inline single-use helpers

- A helper called from exactly one site is almost always net-bigger than its
  inlined body once you account for signature, docstring, and call-site
  marshaling.
- A `_presheaf` / sheaf-level wrapper pair where the wrapper is used 0–1 times
  externally should collapse to one declaration at the more useful level.
- An `abbrev` that just renames a structure projection is bloat; inline it.

EVALUATOR: REJECT helpers introduced this cycle that are called from exactly
one site in the same file.

## Principle 4: Delete unused declarations

- Public declarations not transitively reachable from `GrothendieckVanishing`
  are dead code. The metaprogram in `scripts/unused_decls.lean` finds them.
- Deletion may cascade — once a public lemma is gone, its private helpers may
  also become unreachable.

EVALUATOR: REWARD unused-decl deletion cycles. Verify with `lake env lean`
that no other file silently depended on what was deleted.

## Principle 5: Replace ad-hoc proofs with Mathlib lemmas

- A 30-line proof that re-derives a Mathlib fact is bloat. Use the Mathlib
  lemma. Search via `lean_loogle`, `lean_leansearch`, `lean_state_search`.
- A custom definition that duplicates a Mathlib structure should be replaced.

EVALUATOR: REWARD replacements that delete custom code in favor of Mathlib.

## Principle 6: Hard mechanical gates

- Project must stay at 0 sorrys and 0 axioms.
- Every modified `Aristotle/**/*.lean` must compile under `lake env lean`.
- For add/delete/rename of project Lean files, `lake build` must also pass.
- The cycle's commit must strictly decrease normalized LOC (the controller
  enforces this; the worker does not get to override it).

EVALUATOR: A cycle that fails any mechanical gate is a regression.

## Principle 7: Structural opportunities backlog

When the mechanical Phase 1-4 backlog has only small-yield items left, consult
`.compress-state/structural_ideas.md` for higher-leverage initiatives that the
auto-scanner cannot detect (cross-file restructurings, file mergers, class →
def collapses, Mathlib upstreaming). Each idea there lists a single-cycle
entry point sized to fit one loop iteration.

PLANNER: Read `structural_ideas.md` and prefer its entry-point cycles over
small-yield Phase-4 golf when both are available.

AUDITOR: When rescanning, do NOT delete `structural_ideas.md`. The scan
overwrites `compress_tasks.md`, but `structural_ideas.md` is the durable
source for cross-file structural work.
