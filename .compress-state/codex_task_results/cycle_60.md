## What was done

Golfed `ReducibleVanishing` in
`Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`.

## What changed

- No declarations were renamed or deleted.
- Reverted the local induction target from `(G : Presheaf) (hG : G.IsSheaf)`
  to a bundled `Gsh : TopCat.Sheaf AddCommGrpCat.{u} X`.
- Passed `S.X₁` directly to the recursive induction hypothesis, and used
  `Gsh.cond` only where `sheaf_isZero_of_zero_stalks` needs an `IsSheaf`.
- Removed redundant local packaging (`Fsh`, local `Gsh`, and the closed
  inclusion alias) after the bundled-sheaf rewrite made them unnecessary.
- Golfed nearby setup and stalk-zero plumbing with direct `simp`/`simpa`
  arguments and removed a redundant `by exact` wrapper.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `python3.9 scripts/normalized_loc.py --per-file --raw` before and after
- `wc -l Aristotle/GrothendieckVanishing/main/*.lean` before and after
- `rg -n "\\b(sorry|admit|axiom)\\b" Aristotle --glob '*.lean' || true`
  showed only comment/docstring matches.
- `git diff --check -- Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build` was not run; this was a proof-body edit in one existing file
  with no public declaration/import/attribute changes.

## Normalized LOC

- Before: `4363`
- After: `4350`
- Delta: `-13`

## Raw `main/*.lean` wc -l

- Before: `5260`
- After: `5251`
- Delta: `-9`

## What remains

No blocker remains for this cycle. Further compression in
`ReducibleVanishing` would likely need a broader refactor of the stalk-vanishing
premise shape or the closed-immersion SES API.
