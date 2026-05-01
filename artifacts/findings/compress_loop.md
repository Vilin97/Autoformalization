# Compress Loop — Findings

**Window:** 2026-04-27 15:24 UTC → 2026-04-28 22:53 UTC, 86 cycles on Hyak.
**Driver:** `scripts/codex_compress_loop.py` (Codex worker + Claude evaluator + lake gate).
**Result:** 7016 → 4087 normalized LOC (−2929, −41.7%); 7763 → 4998 raw LOC; crossed the raw <5000 stop target on cycle 86.

## 1. Architecture vs refactor loop

Same three-process shape (worker / evaluator / auditor over `wip/grothendieck-vanishing`), but the gate function differs in two material ways:

- **LOC-decrease gate.** `codex_compress_loop.py:714-720` adds a hard mechanical gate: `loc_after >= loc_before` is treated like a sorry — cycle is rejected and gate-repair fires. Refactor allowed equal-LOC commits.
- **Raw-LOC stop.** `RAW_LOC_STOP_TARGET = 5000` (line 63). When `wc -l Aristotle/GrothendieckVanishing/main/*.lean < 5000` the loop self-terminates.
- **Anti-gaming evaluator rules.** `principles.md` codifies "comments and blanks don't count," "tactic-stacking via `;`/`<;>` doesn't count," and explicitly rewards Sheaf-reversion plus unused-decl deletion.
- **Markdown reports preserved.** All 86 per-cycle Codex reports survive under `.compress-state/codex_task_results/cycle_*.md` (3711 lines total); the refactor loop discarded them.

## 2. Per-cycle delta distribution

86 cycles, all negative. **Mean = −33.9, median = −14, std = 74.3, range = [−501, −1].**

Top 5 single-cycle wins:
1. **Cycle 2 (−501):** sheaf-reverted successor-map / H¹ cokernel-iso / H¹ vanishing clusters in `CohomologyAPI.lean` (1609 → 1193 raw).
2. **Cycle 1 (−350):** bundled the successor connecting iso onto `ShortComplex (Sheaf …)`.
3. **Cycle 10 (−337):** sheafified the entire filtered-colimit boundary, deleting ~10 `_presheaf` shims.
4. **Cycle 7 (−148):** sheaf-reverted CohomologyAPI dimension-shift cluster.
5. **Cycle 3 (−103):** sheaf-reverted FlasqueVanishing's `sheafShortComplexOfPresheaf` bridge plus 5 `_presheaf` wrappers.

Top 5 alone account for **−1439 LOC (49%)**. The bottom decile (cycles 30, 31, 73, 75, 77, 78) hovered at −1 to −4 LOC.

## 3. Strategy evolution

Three discernible phases:

- **Phase 1 — Sheaf reversion (cycles 1–10):** every cycle deletes a `_presheaf` wrapper and bundles the `(F : Presheaf) (h : F.IsSheaf)` triple to a `Sheaf` argument. Mean delta ≈ −180. The phase-1 gate (`raw < 6500`) was met at cycle 10.
- **Phase 2 — Unused-decl deletion (cycles 11–25):** driven by `scripts/unused_decls.lean`. Cycles 17–18 wipe eleven `TopCat.Sheaf.{family,finset}*` wrappers from `GeneratedSubsheaf.lean`. Cycles 22–26 are a Codex-CLI 401 outage — five evaluator failures returned `authentication_error`, but the worker still produced real progress (−12, −19, −5, −22, −10) because the LOC gate is purely mechanical.
- **Phase 3/4 — Long-proof golf (cycles 27–86):** `_presheaf` reversions exhausted (cycle 31: "last `_presheaf` declaration in CohomologyAPI is gone"). Strategy pivots to highest body-to-signature outliers via `compress_audit.py`. Mean delta drops to ~−12.

`structural_ideas.md` (Idea 1) had explicitly framed the filtered-colimit cluster as the highest-yield single initiative; cycle 10 executed Idea 1's entry-point cycle. Ideas 2–6 were referenced but only partially landed.

## 4. Per-file effectiveness

By cumulative delta attributable to summary mentions:

- **CohomologyAPI.lean: −1228 LOC over 10 cycles** — single largest source. Cycles 1, 2, 7, 8, 9 each took 100+ LOC; cycles 13–15, 21, 27–31 stripped unused decls.
- **PresheafFilteredColimit.lean / Core: −910 over 13 cycles**, mostly cycle 10. Cycles 32, 33, 35, 38, 39, 47, 52, 55, 58, 62, 66, 79–84 returned for golf.
- **FlasqueVanishing.lean: −103** in cycle 3, then idle.
- **IrreducibleStep.lean: −166 over 9 cycles**, almost all on `exists_section_generating_stalks` (11 visits showing diminishing returns).

Resistant files: `PresheafFilteredColimitGeneral.lean` (one mention, −10), `ConstantSheafFlasque.lean` (one mention, −10 in the final cycle).

## 5. The "ShortComplex bundling" pattern

The signature compression idiom of Phase 1, formalized in Principle 2 (`principles.md:16-32`). A presheaf-era theorem typically packaged six arguments — `(F₁ F₂ F₃ : TopCat.Presheaf X) (h₁ h₂ h₃ : Fᵢ.IsSheaf)` plus a hand-built `f ≫ g = 0` hypothesis. Bundling collapses these to one: `(S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))`.

Worked example, **cycle 1** (`.compress-state/codex_task_results/cycle_1.md:6-30`):
- Renamed `sheafH_succ_iso_of_subsingleton_middle_presheaf` → `sheafH_succ_iso_of_subsingleton_middle`.
- Deleted same-cluster wrappers `sheafH_succ_map_presheaf_eq_succ_iso_hom`, `sheafH_exists_preimage_of_subsingleton_middle_presheaf`.
- At call sites in `PresheafFilteredColimitCore.lean` and `ClosedImmersionCohomology.lean`, replaced reconstructed presheaf zero proofs with already-bundled short complexes (`sheafH_filtered_colimit_succ_stage_shortExact`).

Result: `CohomologyAPI.lean` 1776 → 1609 raw and `PresheafFilteredColimitCore.lean` 1110 → 919 raw. The pattern repeats in cycles 2, 3, 6, 7, 8, 9, 10, 27, 29, 85.

## 6. What worked

- **Bundled API change with cross-file caller fan-out** (cycle 2, −501): renaming + wrapper deletion + ≥4 caller updates in one cycle is the most leveraged single move.
- **Following Idea 1 from `structural_ideas.md`** (cycle 10, −337): cross-file structural rewrites the auto-scanner can't surface dwarfed mechanical golf.
- **Cascade deletions**: cycle 17 deleted 5 `TopCat.Sheaf.*` wrappers, cycle 18 another 6 — private helpers go unreachable once their public consumer dies.
- **Reusing Mathlib lemmas**: cycle 36 (−29) replaced hand-built `AddMonoidHom.mk'` δ with composition through `sheafH_succ_map`; cycle 51 (−15) used `IsIso.of_isIso_fac_right`; cycle 82 (−20) swapped a 22-line `IsZero.mk` for `sheaf_isZero_of_zero_stalks` plus an import swap.

## 7. What didn't work / got stuck

- **`exists_section_generating_stalks` over-mining**: 11 cycles (41, 50, 54, 56, 59, 63, 68, 69, 73, 75, 76); body went 161 → ~50 lines but cycles 73 and 75 each yielded only −3/−4 LOC. Cycle 56 stuck-on: "further compression likely needs structural restructuring of the minimality argument."
- **`sheafH_filtered_colimit_comparison_one_iso_hom` over-mining**: cycles 32, 33, 35, 39, 47, 52, 55, 58, 62, 66 — 10 visits to a categorical-bookkeeping body resistant to sub-100 LOC because `PreservesCokernel.π_iso_hom` plumbing was load-bearing.
- **Late-cycle decay**: cycles 73–86 averaged −7.6 LOC. Cycles 30, 31, 77, 78 returned just −1 or −2 — mostly `@[simps]` removal.

## 8. Outcome trajectory

Frontloaded then linear-decay, not exponential.

| Cycle | norm | raw | notes |
|------|------|-----|------|
| 0 | 7016 | 7763 | start |
| 10 | 5295 | 6275 | end of Sheaf-reversion phase |
| 20 | 5027 | 5939 | mid Phase-2 |
| 42 | 4606 | 5496 | first below 5500 raw |
| 60 | 4350 | 5251 | mid golf phase |
| 86 | 4087 | **4998** | crossed 5000 raw |

Cycles 1–10 averaged **−172/cycle**; 11–60 averaged **−24**; 61–86 averaged **−10**. The 4500-raw target was never reached. 5000-raw was crossed on the **last possible cycle** — cycle 86 trimmed `toPlus_surjective_of_firstPlus` for −10 to land at 4998.

## Open questions

- Would routing high-ratio golf candidates to Aristotle (Idea 6 in `structural_ideas.md`) recover the late-cycle yield decay? The compress loop never executed Idea 6.
- Did the `claude-opus-4-7` 401 outage (cycles 22–26) silently skip principle-violation checks? Score-0 cycles still committed real deltas.
- Could a successor "structural" phase have plausibly hit 4500 raw, or is residual ~5000 LOC genuinely irreducible without API redesign? Stuck-on themes from cycles 55–67 suggest the latter.
