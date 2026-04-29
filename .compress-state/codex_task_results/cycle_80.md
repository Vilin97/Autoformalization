## What was done

- Golfed `sheafH_filtered_colimit_comparison_isIso_succ_succ` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.
- Reused the existing injective-colimit vanishing lemma instead of rebuilding the local flasque witness.
- Replaced the final manual transport rewrite with direct `IsIso.of_isIso_fac_left` on the successor-step compatibility equality.

## What changed

- No declarations were renamed or deleted.
- Removed the one-use local `hFlasqueInj` proof block.
- Shortened `h_colim` to call `sheafH_filtered_colimit_succ_inj_subsingleton`.
- Eliminated the local `hcompat` binding plus `rw`/`simp`/`infer_instance` tail in favor of a direct `exact IsIso.of_isIso_fac_left ...`.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `rg -n "^\\s*(axiom|admit|sorry)\\b|:=\\s*by\\s*sorry\\b|by\\s+admit\\b" Aristotle --glob '*.lean'`

The Lean commands completed successfully; the placeholder scan returned no matches.

## Normalized LOC

- Before: `4182`
- After: `4162`
- Delta: `-20`

`PresheafFilteredColimit.lean` normalized count changed from `454` to `434`.

## Raw `wc -l` for `main/*.lean`

- Before: `5087`
- After: `5067`
- Delta: `-20`

`PresheafFilteredColimit.lean` raw line count changed from `499` to `479`.

## What remains

- No blocker remains from this cycle. The targeted long proof is shorter and still compiles.
