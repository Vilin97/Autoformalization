# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-03T21:00Z

## Status Summary
- **CI**: Last green run at 37943bf. Pending run from latest push.
- **Sorry count**: 2 (SheafHom.lean:63, FiniteGeneratorReduction.lean:198)
- **Files**: 14 main files, ~5300 lines total
- **Docs**: Blueprint 404 (deployed on main only)
- **Progress last cycle**: Closed sorry at line 180 (n=0 Hom case), documented structural gap

## Active Multi-Cycle Strategies

1. **Close AB5 sorry (isSheaf_filtered_colimit_of_sheaves)**: Core mathematical gap. Filtered presheaf colimits of sheaves are sheaves on Noetherian spaces. File ready in `aristotle-in/isSheaf_filtered_colimit.lean` but Aristotle API unreachable from HPC. Approach: use `Sheaf.ab5ofSize` + Noetherian finite-cover machinery.

2. **Restructure hQprov to eliminate recursive quotient problem**: The sorry at line 198 asks for `Ext^{n'}(Z, cokernel(Qcocone.ι.app j ≫ ip'.f)) n'` — vanishing on Q-of-Q quotients. The Q-diagram's transitions are NOT mono (documented at lines 189-195), so ext_sandwich can't be applied recursively. Two fix strategies:
   - **(A) Strengthen hHom_univ to PreservesFilteredColimitsOfSize**: If coyoneda.obj(op Z) preserves filtered colimits, then hQprov can be derived internally for ALL depths of quotient. Search Mathlib for `PreservesFilteredColimits` on coyoneda + Grothendieck abelian.
   - **(B) Restructure to per-object injective embeddings (Hartshorne's approach)**: Embed each Y_j ↪ I_j separately, getting compatible system of SES. Quotient transitions inherit mono. Avoids Q-of-Q problem entirely, but requires functorial injective embeddings.

## This Cycle's Work Items

1. **[/prove] Search Mathlib for colimit preservation tools** (P1, immediate)
   - `lean_leansearch` / `lean_loogle` for:
     - `PreservesFilteredColimitsOfSize` instances for coyoneda
     - `IsGrothendieckAbelian` + filtered colimit preservation
     - Whether Noetherian sheaf categories have compact generators
   - If found: strengthen `hHom_univ` parameter and close hQprov

2. **[/prove] Attempt hQprov sorry — decompose if Mathlib tools insufficient** (P1)
   - If approach (A) works: rewrite ext_vanishing_of_colimit_aux to not need hQprov as parameter
   - If not: extract the n'=0 sub-case as a separate sorry'd lemma (the only truly hard case), prove n'≥1 case via injectivity + ext_sandwich
   - Concrete fallback: split hQprov into `hQprov_zero` (Hom-level, hard) and `hQprov_succ` (provable from injectivity + hvan)

3. **[/submit-aristotle] Retry AB5 submission** (P1)
   Attempt Aristotle API. If unreachable, skip.

4. **[/simplify] No urgent code quality fixes** (P3)
   ZeroOutside.lean (733), SheafStalkAlgebra.lean (688), FlasqueVanishing.lean (616) — over 600-line guideline but not severe. Focus on sorry closure this cycle.

## Backlog
- P1: Fix docs/blueprint 404 (needs merge to main or deploy workflow change)
- P3: ZeroOutside.lean (733), SheafStalkAlgebra.lean (688), FlasqueVanishing.lean (616) — over 600-line guideline
- P3: Clean up `finsetCoproductIncl` vs `finsetCoproductInclGen` naming
- P4: Upstream FlasqueVanishing, ext_sandwich, sheafH_vanishing_cascade to Mathlib
