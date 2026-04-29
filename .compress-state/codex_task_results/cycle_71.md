## What was done

Golfed `finsetGeneratedSheaf_vanishing` in
`Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`.

## What changed

- No declarations were renamed or deleted.
- Inlined the single-use `heq` fact in the insert-case epi proof.
- Replaced the non-`σ₀` component rewrite chain with one `simpa` over the
  congruence of the finite-coproduct inclusion equality.
- Added proof-local abbreviations `qIns` and `qS` for repeated
  `factorThruImage (finsetGeneratorMap ...)` morphisms.
- Removed an unnecessary local `Balanced` instance.
- Collapsed the `suffices ... from by exact ...` wrapper to `from h S`.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
- `rg -n "\b(sorry|admit|axiom)\b" Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean`
  returned no matches.
- `lake build` was not run; this was a proof-body-only golf with no imports,
  renames, deletions, generated attributes, or project file changes.

## Normalized LOC

- Before: `4252`
- After: `4238`
- Delta: `-14`

## Raw `wc -l` for `main/*.lean`

- Before: `5154`
- After: `5140`
- Delta: `-14`

## What remains

No blocker remains from this cycle. Further savings in this theorem would likely
require a different categorical lemma for the insert-case cokernel component or
a broader helper that has more than one real call site.
