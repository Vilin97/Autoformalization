# Cycle 8 Report

## What was done

Reverted the Phase-1 stalk-zero pair in `CohomologyAPI.lean` from presheaf plus
`IsSheaf` packaging to sheaf-level `ShortComplex` arguments, then updated the
four direct callers in `IrreducibleStep.lean` and `GrothendieckVanishing.lean`.

## What changed

- Renamed `stalk_zero_of_ses_g_iso_presheaf` to `stalk_zero_of_ses_g_iso`.
- Renamed `stalk_zero_of_shortExact_kernel_presheaf` to
  `stalk_zero_of_shortExact_kernel`.
- Deleted the duplicated local `ShortComplex.mk` reconstruction and bundled
  `Sheaf.Hom.mk` argument marshaling inside both proofs.
- Updated the four call sites to pass `S hSE x ... a` directly.

## Verification performed

- `lake env lean Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean`
- `lake build Aristotle.GrothendieckVanishing.main.CohomologyAPI`
- `lake env lean Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean`
- `lake env lean Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`
- `lake build`

The full build completed successfully. It printed existing linter warnings in
unmodified files, but no errors.

## LOC

- Normalized LOC before: `5779`
- Normalized LOC after: `5708`
- Normalized LOC delta: `-71`
- Raw `wc -l` of `main/*.lean` before: `6809`
- Raw `wc -l` of `main/*.lean` after: `6735`
- Raw `wc -l` delta: `-74`

## Remaining work

The targeted stalk-zero pair and its direct callers are complete. Other
presheaf-boundary clusters, especially the cokernel stalk-zero cluster that was
out of scope for this cycle, remain for later cycles.
