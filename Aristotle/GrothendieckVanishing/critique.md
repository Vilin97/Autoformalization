# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-01T20:30Z
**Reviewer verdict**: REVISE

## 0. CI Status

CI is GREEN (commit `31af56b`). All heartbeat overrides have been removed (was ~30 overrides). However, CI passes only because **21 previously-proved theorems were replaced with `sorry`** to eliminate compilation errors. This is a Pyrrhic victory — CI is green but the formalization has regressed massively.

**P1 — Docs deployment broken.** Both `https://vilin97.github.io/aristotle/blueprint/` and `https://vilin97.github.io/aristotle/blueprint/dep_graph_document.html` return HTTP 404.

## 1. Sorry's (19)

**Was 2 sorry's before the heartbeat elimination; now 19.** All in `IrreducibleStep.lean`. Of these, 17 are regressions — proofs that previously existed but broke when heartbeat overrides were removed and were sorry'd out rather than fixed.

### Original sorry's (2, genuine Mathlib gaps):
1. **`exists_good_section`** (line 306): Subsheaf structure lemma (Step 4 core). Requires stalk-level sheaf algebra not in Mathlib.
2. **`cohomology_vanishing_of_finitelyGenerated_vanishing`** (line 393): Hartshorne 2.9 — cohomology commutes with filtered colimits. Confirmed Mathlib gap.

### Regressed sorry's (17, previously proved):
3. **`zeroOutsideInt_vanishing`** (line 69): SES argument for zeroOutsideInt cohomology.
4. **`presheaf_stalk_surj_openHom`** (line 79): Presheaf stalk surjectivity via restriction.
5. **`sheaf_stalk_surj_openHom`** (line 96): Sheaf stalk surjectivity via toSheafify.
6. **`sheaf_stalk_bijective_openHom`** (line 111, injectivity half): Stalk injectivity.
7. **`cokernel_stalk_zero_V`** (line 120): Cokernel stalks vanish on V.
8. **`cokernel_openHom_vanishing`** (line 139): Cokernel cohomology vanishing.
9. **`zeroOutsideInt_cohomology_vanishing`** (line 162): Step 5 cohomology vanishing.
10. **`subsingleton_ext_of_ses_third`** (line 170): Third-term LES.
11. **`isZero_zeroOutsideInt_bot`** (line 183): zeroOutsideInt bot is zero.
12. **`stalk_zeroOutsideInt_zero_outside`** (line 190): Stalks vanish outside support.
13. **`exists_nonzero_stalk_in_V`** (line 201): Nonzero subsheaf has nonzero stalk in V.
14. **`sheaf_mono_of_stalk_injective`** (line 210): Stalkwise injective implies mono.
15. **`presheaf_stalk_zeroOutside_eq_zsmul_generator`** (line 228): Generator span for presheaf stalks.
16. **`stalk_zeroOutsideInt_eq_zsmul_generator`** (line 239): Generator span for sheaf stalks.
17. **`cokernel_stalk_zero_of_stalk_surj`** (line 345): Cokernel stalk zero from surjectivity.
18. **`subsheaf_zeroOutsideInt_vanishing`** (line 363): Step 4 vanishing.
19. **`epiImage_zeroOutsideInt_vanishing`** (line 381): Steps 3C+4+LES vanishing.

The main theorem `grothendieck_vanishing` depends on ALL of these through `IrreduciblePosVanishing`. The theorem is not proved — it is sorry'd at 19 points in its dependency chain.

## 2. Hidden Axioms

No `admit`, `axiom`, or `native_decide` found. The 5 disabled Mathlib linters remain (`mathlibStandardSet`, `unusedSimpArgs`, `unnecessarySimpa`, `unusedTactic`, `unreachableTactic`).

## 3. Circularity

No circularity found. Well-founded induction on `topologicalKrullDim` is correct.

## 4. Hypothesis Audit

Main theorem signature unchanged. All hypotheses necessary. No issues.

## 5. Mathematical Correctness

All sorry'd statements are mathematically correct (they were previously proved). The proof strategy follows Hartshorne III.2.7 faithfully.

## 6. Code Quality

- **P0 — 19 sorry's** (was 2). The formalization has regressed.
- **Heartbeat overrides**: 0 (good, but achieved by sorry'ing out proofs).
- **File sizes**: ZeroOutside.lean at 733 lines, FlasqueVanishing.lean at 616 lines — over the 600-line guideline.
- **IrreducibleStep.lean**: 517 lines (reduced from 920, but only because proofs were deleted).
- **5 Mathlib linters disabled** in lakefile — unchanged.

## 7. Documentation Lies

- **CLAUDE.md "Remaining Work"**: Says "2 sorry's remain" — **FALSE**, there are now 19.
- **IrreducibleStep.lean header comment**: Says "2 sorry's: exists_good_section, cohomology_vanishing_of_finitelyGenerated_vanishing" — **FALSE**, there are 19 sorry's.
- **GrothendieckVanishing.lean header**: References "2 sorry's in IrreducibleStep.lean" — **FALSE**.
- **GitHub Pages docs**: Broken (404).

## 8. Generalization Opportunities

1. **Generalize from AddCommGrpCat to Grothendieck abelian categories** (LOW feasibility). Major refactor touching all stalk arguments.
2. **Strengthen `Subsingleton` to `IsZero`** (MEDIUM feasibility). More useful for downstream consumers.
3. **Extract FlasqueVanishing as standalone Mathlib PR** (HIGH feasibility). Self-contained package, already heartbeat-clean.
4. **Extract `sheaf_isZero_of_zero_stalks`** (HIGH feasibility). Basic missing lemma, clean PR candidate.
5. **Extract `closedIncl_unit_stalk_isIso`** (MEDIUM feasibility). Useful infrastructure for closed immersion theory.

## 9. Mathlib Upstreamability

1. **Flasque sheaf package** — `FlasqueVanishing`, `epi_app_of_shortExact_flasque`, `isFlasque_X₃_of_shortExact`. Now heartbeat-clean.
2. **`sheaf_isZero_of_isEmpty`** — trivial PR.
3. **`closedIncl_unit_stalk_isIso`** — stalk of adjunction unit for closed immersion.
4. **`pushforward_stalk_zero_closedIncl`** — stalk of pushforward vanishes outside closed set.

## Open Issues

| # | Priority | Issue | Status |
|---|----------|-------|--------|
| 1 | P0 | 17 regressed sorry's in IrreducibleStep.lean (proofs broken by heartbeat removal) | OPEN |
| 2 | P1 | 2 original sorry's (Mathlib API gaps: exists_good_section, filtered colimits) | OPEN |
| 3 | P1 | Docs deployment broken (404 on blueprint) | OPEN |
| 4 | P2 | CLAUDE.md and file headers claim "2 sorry's" — actually 19 | OPEN |
| 5 | P2 | ZeroOutside.lean (733 lines), FlasqueVanishing.lean (616 lines) over 600-line guideline | OPEN |
| 6 | P3 | 5 Mathlib linters disabled in lakefile | OPEN |

## Verdict: REVISE

The formalization has **regressed** from 2 sorry's to 19. CI is green only because proofs were replaced with sorry. The 17 regressed proofs need to be restored — they were working before, so the fix is to adapt them to the current (heartbeat-override-free) environment by providing explicit instances (`haveI`, `letI`, `inferInstanceAs`). This is mechanical but substantial work.

Conditions for CONDITIONAL ACCEPT:
1. Restore all 17 regressed sorry's (bring count back to 2)
2. Fix documentation claims to match actual sorry count
3. Fix docs deployment (404)

Conditions for ACCEPT:
- All of the above, plus both original sorry's resolved
