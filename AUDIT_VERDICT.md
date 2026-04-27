# Refactor audit verdict — 2026-04-26

Audited the current tree against the original review (`review.md`) after the
codex refactor loop self-reported `loop_done: true` at cycle 498
(2026-04-27 idle).

## Bottom line

**~95% complete.** The structural goals from the review are achieved. The
loop's "genuinely finished" call is largely correct, but one concrete item
the auditor has consistently understated remains, plus a few minor leftovers.
The auditor's prose has been progressively misreporting the Zorn block size
("30 lines" → "60 lines") while the actual measurement is ~226 lines.

## Verified done

- `Ext`/`extClass` confined to `CohomologyAPI.lean` (grep confirms).
- All `ext_*`/`extClass_*` core lemmas in `CohomologyAPI` are `private`.
- `PushforwardHVanishing` deleted.
- `(F : Presheaf) (hF : IsSheaf F)` idiom is the dominant public surface.
- `IsFlasqueSheaf` is a `class` (`FlasqueVanishing.lean:34`).
- `sheafCohomologyFunctor` exists with `Additive` instance
  (`CohomologyAPI.lean:1265–1270`).
- `FlasqueVanishing.lean` is the single flasque module
  (`FlasqueCohomology.lean` is gone).
- `FiniteGeneratorReduction.lean` → split into `FinitelyGeneratedVanishing.lean`
  + `PresheafFilteredColimit{,Core,General}.lean`.
- `ULiftInt.lean` is 28 lines, just an `AddEquiv` transport;
  `ulift_int_subgroup_cyclic` removed.
- `TopologicalKrullDim.lean` has `topologicalKrullDim_eq_bot_iff_isEmpty` +
  full API; `topologicalKrullDim_lt_of_add_one_le_of_lt_top` is `private`.
- `ConstantSheafFlasque.lean` is parameterized over `A : AddCommGrpCat.{u}`;
  intermediate theorems conclude `IsFlasqueSheaf` directly.
- Dim-zero base case lives inline in `GrothendieckVanishing.lean`.
- 17 files in `main/`, 8131 lines total — file structure matches review.

## Where the auditor is wrong

**The Zorn block in `FlasqueVanishing.lean` is NOT "~60 lines" — it is ~226
lines** (lines 108–333):

| range | lemma | lines |
| --- | --- | --- |
| 110–114 | `Under` abbrev | 5 |
| 115–235 | `under_exists_extension_containing` | **121** |
| 237–307 | `under_chain_upper_bound` | 71 |
| 308–314 | `structuredArrowsElementsSheafChainsBounded` (redundant wrapper) | 7 |
| 316–333 | `under_maximal_eq_top` | 18 |

The review explicitly asked for this to be replaced by the simpler Zorn
argument from the user's PR (target: ≤40 lines using Mathlib's `zorn_*`
directly). The prior COMPLETE_IF criteria measured from one specific lemma
to another, and "passed" only because the bigger lemmas were moved earlier
in the file — not because the block actually shrank. The COMPLETE_IF in
Phase 17 now measures the full hand-rolled block.

## Small remaining items

1. **`structuredArrowsElementsSheafChainsBounded`** at `FlasqueVanishing.lean:308`
   is a 7-line pass-through to `under_chain_upper_bound`. Inline the call
   site (line 314 is just `exact under_chain_upper_bound g s c hchain`) and
   delete the wrapper.
2. **`abbrev constPresheaf`** at `ConstantSheafFlasque.lean:15` — review
   said "doesn't need to exist". It's used pervasively in the file but
   inlining is mechanical; leaving it is acceptable but does not match the
   review.
3. **`PresheafFilteredColimit{,Core,General}.lean`** total ~2614 lines vs.
   review's "main comparison theorem ought to be ~100 lines" aspiration.
   The 3-file split is principled and `sheafH_preserves_filtered_colimits_presheaf`
   itself is now 14 lines. Probably acceptable as-is; the bulk lives in the
   compatibility lemmas the review itself acknowledged would be heavy.

## Recommended manual follow-up

One concrete ticket: **replace `FlasqueVanishing.lean:108–333` with the
shorter Zorn argument from the user's PR**, and delete the redundant
`structuredArrowsElementsSheafChainsBounded` wrapper as part of that
change. Phase 17 of `review_tasks.md` is added to push the loop on this.
