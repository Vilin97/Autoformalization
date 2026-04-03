# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-03T19:10Z

## Status Summary
- **CI**: In progress (bb64f45). Previous run failed (d41f8f6, stale duplicates — now fixed).
- **Sorry count**: 2 (1 in SheafHom.lean:63, 1 in FiniteGeneratorReduction.lean:180+188)
- **Files**: 14 main files, ~5300 lines total (reduced from ~6000 by dedup)
- **Docs**: Blueprint 404 (deployed on main only)
- **Progress this session**: Closed sorry #3 (n'=0 dead case), deduplicated IrreducibleStep.lean (-670 lines)

## Active Multi-Cycle Strategies

1. **Close AB5 sorry (isSheaf_filtered_colimit_of_sheaves)**: Core mathematical gap. Filtered presheaf colimits of sheaves are sheaves on Noetherian spaces. File ready in `aristotle-in/isSheaf_filtered_colimit.lean` but API unreachable from HPC. Approach: use `Sheaf.ab5ofSize` + `IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono` or prove directly from Noetherian → finite covers.

2. **Restructure hQprov induction**: Sorry #2 (lines 180+188) has recursive structure. The key question: does the outer dimension induction provide what the inner Ext-degree induction needs? The hQprov at line 188 asks for vanishing on `cokernel(ι_j ≫ f)` at the same degree — this is a lateral step on a different object. Must show the caller's context (dimension < dim X) gives this via the dimension IH.

## This Cycle's Work Items

1. **[/prove] Attempt sorry #2 (hQprov) — line 180 specifically** (P1, immediate)
   The `by sorry` at line 180 needs `Subsingleton (Ext Z Q 0)` where Q = `Qcocone.pt` is the colimit point of the quotient diagram. Since `Ext^0 ≅ Hom`, this asks for `Subsingleton (Z ⟶ Q)`. The `hHom_univ` parameter already provides exactly this: Hom(Z,-) preserves filtered colimit vanishing. Use `hHom_univ` applied to the Qfun/Qcocone/hQcolim with per-j Hom vanishing derived from `hvan` + LES.

   Concrete plan:
   - Check that `hvan j : Subsingleton (Ext Z (Y.obj j) (n+1))` gives `Subsingleton (Hom(Z, Q_j))` via LES
   - Apply `hHom_univ Qfun Qcocone hQcolim` to get `Subsingleton (Hom(Z, Q))`
   - Convert via `Ext.homEquiv₀` to close the sorry

2. **[/prove] Attempt sorry #2 — line 188** (P1)
   The `:= sorry` asks for `∀ (n'': ℕ), n'+1 = n''+1 → ∀ ip' j, Subsingleton (Ext Z (cokernel(ι_j ≫ ip'.shortComplex.f)) n'')`. This simplifies to n'' = n'. Need `Ext^{n'}(Z, cokernel(ι_j ≫ f))` = 0.

   From the SES `0 → Y.obj j → I → Q_j → 0` (where Q_j = cokernel(ι_j ≫ f)):
   - `hvan j` gives `Ext^{n'+1}(Z, Y.obj j) = 0`
   - Need `Ext^{n'}(Z, I) = 0` — true if n' ≥ 1 since I is injective
   - Then `ext_sandwich` gives `Ext^{n'}(Z, Q_j) = 0`

   BUT: this is for the ORIGINAL diagram's Q_j, not for the recursive Qcocone.pt's quotients. The hQprov asks about a NEW injective presentation of Qcocone.pt. This may require the dimension induction.

3. **[/submit-aristotle] Submit isSheaf_filtered_colimit** (P1)
   Retry Aristotle API. File already prepared.

4. **[/simplify] No urgent code quality fixes this cycle** — IrreducibleStep.lean was just fixed (1264→595 lines). Remaining oversized files (ZeroOutside 733, SheafStalkAlgebra 688) are not severe.

## Backlog
- P1: Fix docs/blueprint 404 (needs merge to main or deploy workflow change)
- P3: ZeroOutside.lean (733), SheafStalkAlgebra.lean (688), FlasqueVanishing.lean (616) — over 600-line guideline
- P3: Clean up `finsetCoproductIncl` vs `finsetCoproductInclGen` naming
- P4: Upstream FlasqueVanishing, ext_sandwich, sheafH_vanishing_cascade to Mathlib
