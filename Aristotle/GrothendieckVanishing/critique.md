# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-01T21:10Z
**Reviewer verdict**: REVISE

## 0. CI Status

CI run 23869853940 is IN PROGRESS (commit 663f12f). Previous runs 23869817892 and 23869793658 were CANCELLED. The last completed non-cancelled run (23869487254, commit a3bef4a) FAILED with kernel type mismatch and `Opens.mk σ₀` errors. Fix was pushed (1c5420d + 663f12f) but CI has not yet confirmed GREEN.

**P0 — CI status UNKNOWN.** Cannot verify the fix compiles until CI completes.

**P1 — Docs deployment broken.** Both `https://vilin97.github.io/aristotle/blueprint/` and `https://vilin97.github.io/aristotle/blueprint/dep_graph_document.html` return HTTP 404.

## 1. Sorry's (16)

All in `IrreducibleStep.lean`. 16 actual sorry's (was 19 last review, reduced by other agent closing 3).

### Original sorry's (2, genuine Mathlib gaps):
1. **`exists_good_section`** (line 324): Step 4 core — find V' ≤ V and section inducing stalk bijection. Requires stalk-level sheaf algebra not in Mathlib.
2. **`cohomology_vanishing_of_finitelyGenerated_vanishing`** (line 429): Hartshorne 2.9 — cohomology commutes with filtered colimits. Confirmed Mathlib gap.

### Regressed sorry's (14, previously proved):
3. **`zeroOutsideInt_vanishing`** (line 76): Uses `sorry : IsFlasqueSheaf S.X₂` — needs `zeroOutsideInt ⊤` is flasque.
4. **`presheaf_stalk_surj_openHom`** (line 88): Presheaf stalk surjectivity via restriction.
5. **`sheaf_stalk_surj_openHom`** (line 105): Sheaf stalk surjectivity via toSheafify.
6. **`sheaf_stalk_bijective_openHom`** (line 120, injectivity half): Stalk injectivity.
7. **`cokernel_stalk_zero_V`** (line 129): Cokernel stalks vanish on V.
8. **`cokernel_openHom_vanishing`** (line 148): Cokernel cohomology vanishing.
9. **`zeroOutsideInt_cohomology_vanishing`** (line 171): Step 5 cohomology vanishing.
10. **`isZero_zeroOutsideInt_bot`** (line 198): zeroOutsideInt bot is zero.
11. **`stalk_zeroOutsideInt_zero_outside`** (line 205): Stalks vanish outside support.
12. **`exists_nonzero_stalk_in_V`** (line 216): Nonzero subsheaf has nonzero stalk in V.
13. **`presheaf_stalk_zeroOutside_eq_zsmul_generator`** (line 246): Generator span for presheaf stalks.
14. **`stalk_zeroOutsideInt_eq_zsmul_generator`** (line 257): Generator span for sheaf stalks.
15. **`subsheaf_zeroOutsideInt_vanishing`** (line 399): Step 4 vanishing.
16. **`epiImage_zeroOutsideInt_vanishing`** (line 417): Steps 3C+4+LES vanishing.

The main theorem `GrothendieckVanishing` depends on ALL of these through `IrreduciblePosVanishing`. The theorem is not proved — it is sorry'd at 16 points in its dependency chain.

## 2. Hidden Axioms

No `admit`, `axiom`, or `native_decide` found. The 5 disabled Mathlib linters remain (`mathlibStandardSet`, `unusedSimpArgs`, `unnecessarySimpa`, `unusedTactic`, `unreachableTactic`).

## 3. Circularity

No circularity found. Well-founded induction on `topologicalKrullDim` is correct. The `ih` parameter in recursive lemmas correctly requires `topologicalKrullDim Y < topologicalKrullDim X`.

## 4. Hypothesis Audit

Main theorem signature:
```lean
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

- `X : TopCat.{u}` — necessary
- `F : TopCat.Sheaf AddCommGrpCat.{u} X` — necessary. Could generalize to Grothendieck abelian categories (see §8)
- `[NoetherianSpace X]` — necessary (Hartshorne's hypothesis)
- `n : ℕ` — necessary
- `h : n > topologicalKrullDim X` — necessary (this IS the dimension bound)

All hypotheses are necessary. No issues.

## 5. Mathematical Correctness

All sorry'd statements are mathematically correct (they were previously proved and their proofs broke during heartbeat optimization). The proof strategy follows Hartshorne III.2.7 faithfully.

One concern: `zeroOutsideInt_vanishing` (line 76) has `(sorry : IsFlasqueSheaf S.X₂)` inline. `S.X₂` here is `zeroOutsideInt ⊤` which equals the constant sheaf (by `rfl`), which is flasque on irreducible spaces (proved in `ConstantSheafFlasque.lean`). The sorry should be closeable by providing the instance chain.

## 6. Code Quality

- **P0 — 16 sorry's** (was 19 last review, was 2 before regression). The formalization has regressed from 2 sorry's.
- **Heartbeat overrides**: 0 (good).
- **File sizes**: ZeroOutside.lean at 733 lines, FlasqueVanishing.lean at 616 lines, IrreducibleStep.lean at 603 lines — all near or over the 600-line guideline.
- **5 Mathlib linters disabled** in lakefile — unchanged.
- **`sheaf_mono_of_stalk_injective`** (line 219) is now proved (not sorry'd) — progress.
- **`cokernel_stalk_zero_of_stalk_surj`** (line 355) is now proved — progress.

## 7. Documentation Lies

- **CLAUDE.md "Remaining Work"**: Says "19 sorry's remain" — **STALE**, there are now 16.
- **IrreducibleStep.lean header comment** (line 9): Says "19 sorry's total" — **STALE**, there are 16.
- **GrothendieckVanishing.lean header** (line 8): Says "19 sorry's" — **STALE**.
- **IrreducibleStep.lean line 153**: Comment says "the other two remain sorry" — context unclear, may be stale.
- **GitHub Pages docs**: Broken (404).

## 8. Generalization Opportunities

1. **Generalize from AddCommGrpCat to Grothendieck abelian categories** (LOW feasibility). Major refactor touching all stalk arguments. Would make the theorem applicable to sheaves of modules, etc.
2. **Strengthen `Subsingleton` to `IsZero`** (MEDIUM feasibility). More useful for downstream consumers. `Subsingleton` says the type has ≤1 element; `IsZero` is the categorical zero which is stronger and more compositional.
3. **Extract FlasqueVanishing as standalone Mathlib PR** (HIGH feasibility). Self-contained package, heartbeat-clean.
4. **Extract `sheaf_isZero_of_zero_stalks`** (HIGH feasibility). Basic missing lemma, clean PR candidate.
5. **Extract `closedIncl_unit_stalk_isIso`** (MEDIUM feasibility). Useful infrastructure for closed immersion theory.

## 9. Mathlib Upstreamability

1. **Flasque sheaf package** — `FlasqueVanishing`, `epi_app_of_shortExact_flasque`, `isFlasque_X₃_of_shortExact`. Now heartbeat-clean.
2. **`sheaf_isZero_of_isEmpty`** — trivial PR.
3. **`closedIncl_unit_stalk_isIso`** — stalk of adjunction unit for closed immersion.
4. **`pushforward_stalk_zero_closedIncl`** — stalk of pushforward vanishes outside closed set.
5. **`subsingleton_ext_of_ses` / `subsingleton_ext_of_ses_third`** — LES vanishing lemmas for Ext.
6. **`cokernel_stalk_zero_of_stalk_surj`** — cokernel stalks vanish at surjective points. Clean, self-contained.

## Open Issues

| # | Priority | Issue | Status |
|---|----------|-------|--------|
| 1 | P0 | CI status unknown (in-progress, last completed run FAILED) | OPEN |
| 2 | P0 | 14 regressed sorry's in IrreducibleStep.lean | OPEN |
| 3 | P1 | 2 original sorry's (Mathlib API gaps: exists_good_section, filtered colimits) | OPEN |
| 4 | P1 | Docs deployment broken (404 on blueprint) | OPEN |
| 5 | P2 | CLAUDE.md and file headers claim "19 sorry's" — actually 16 | OPEN |
| 6 | P2 | ZeroOutside.lean (733 lines), FlasqueVanishing.lean (616 lines) over 600-line guideline | OPEN |
| 7 | P3 | 5 Mathlib linters disabled in lakefile | OPEN |

## Verdict: REVISE

The formalization has **regressed** from 2 sorry's to 16. CI has not confirmed green since the fix. The 14 regressed proofs need to be restored — they were working before, so the fix is to adapt them to the current (heartbeat-override-free) environment by providing explicit instances (`haveI`, `letI`, `inferInstanceAs`).

Conditions for CONDITIONAL ACCEPT:
1. CI confirmed GREEN
2. Restore all 14 regressed sorry's (bring count back to 2)
3. Fix documentation claims to match actual sorry count
4. Fix docs deployment (404)

Conditions for ACCEPT:
- All of the above, plus both original sorry's resolved
