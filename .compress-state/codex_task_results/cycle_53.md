## What was done

Golfed `sheafH_filtered_colimit_comparison_isIso_succ_succ` in
`Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`.

## What changed

- Replaced the hand-expanded `hInj` proof with the existing
  `inferInstanceAs (Injective (IsGrothendieckAbelian.monoMapFactorizationDataRlp ...).Z)`
  pattern used elsewhere in the file.
- Inlined the one-use `hqColim` proof into the induction-hypothesis call.
- Replaced separate `h_mid_n` / `h_mid_succ` proofs with one local `h_mid`.
- Replaced separate `h_colim_n` / `h_colim_succ` proofs with one local `h_colim`.
- No declarations were renamed or deleted.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean`
- `lake build` was not run; this cycle only changed a private proof body in one file.

## Normalized LOC

- Before: 4451
- After: 4437
- Delta: -14

## Raw `wc -l` of `main/*.lean`

- Before: 5348
- After: 5334
- Delta: -14

## What remains

Nothing blocked in this target. Further compression would require a separate pass on other long proofs or structural targets.
