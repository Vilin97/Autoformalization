# Cycle 24 Results

## What was done

- Deleted the unused public wrapper theorem `FlasqueVanishing`.
- Left `sheafH_subsingleton_of_flasque` intact as the canonical theorem.
- Retargeted the umbrella module smoke check from the deleted wrapper to
  `sheafH_subsingleton_of_flasque`.

## What changed

- Deleted declaration:
  - `FlasqueVanishing`
- Renamed / inlined / golfed declarations:
  - None.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishingOverview.lean`
- `lake build`
- `rg -n "\b(sorry|admit|axiom)\b" Aristotle --glob '*.lean'`
  - No Lean `sorry`, `admit`, or `axiom` declarations found; matches were only
    prose/comment occurrences.
- `git diff --check`

## Normalized LOC

- Before: `4983`
- After: `4978`
- Delta: `-5`

## Raw `wc -l` for `main/*.lean`

- Before: `5886`
- After: `5879`
- Delta: `-7`

## What remains

- No source theorem named `FlasqueVanishing` remains.
- Remaining `FlasqueVanishing` text hits are comments or module/file import names.
