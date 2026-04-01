# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-01T21:15Z

## Status Summary
- **CI**: IN PROGRESS (commit `663f12f`), last completed run FAILED (a3bef4a, fixed by 1c5420d)
- **Heartbeat overrides**: 0
- **Sorry count**: 16 in IrreducibleStep.lean (was 19 last cycle; 2 original + 14 regressed)
- **Files**: 15 files under `main/`, ~4000 lines
- **Pre-regression commit**: `e90c2f0` has working proofs for all 14 regressed sorry's

## Strategy: Restore from e90c2f0

All 14 regressed sorry's have working proofs at commit `e90c2f0`. The proofs broke when heartbeat overrides were removed. The fix for each is to extract the old proof and adapt it by:
- Adding explicit `haveI`/`letI` for expensive instance synthesis
- Fixing any API name changes (`image.ι` → `Limits.image.ι`, etc.)
- Fixing type elaboration issues (`.presheaf` → `.val`, `closedIncl` unfolding)

### Dependency order (bottom-up)

The sorry's form a dependency chain. Restore in this order:

**Tier 1 — No dependencies on other sorry'd theorems:**
1. `presheaf_stalk_surj_openHom` (line 88)
2. `isZero_zeroOutsideInt_bot` (line 198)
3. `stalk_zeroOutsideInt_zero_outside` (line 205)
4. `exists_nonzero_stalk_in_V` (line 216)
5. `presheaf_stalk_zeroOutside_eq_zsmul_generator` (line 246)

**Tier 2 — Depend on Tier 1:**
6. `sheaf_stalk_surj_openHom` (line 105) — depends on presheaf_stalk_surj_openHom
7. `stalk_zeroOutsideInt_eq_zsmul_generator` (line 257) — depends on presheaf version
8. `sheaf_stalk_bijective_openHom` (line 120) — depends on sheaf_stalk_surj_openHom

**Tier 3 — Depend on Tier 2:**
9. `cokernel_stalk_zero_V` (line 129) — depends on sheaf_stalk_bijective_openHom
10. `zeroOutsideInt_vanishing` (line 76) — needs `IsFlasqueSheaf (zeroOutsideInt ⊤)`

**Tier 4 — Complex proofs depending on Tiers 1-3:**
11. `cokernel_openHom_vanishing` (line 148) — largest proof, depends on cokernel_stalk_zero_V + IH
12. `zeroOutsideInt_cohomology_vanishing` (line 171) — depends on zeroOutsideInt_vanishing + cokernel_openHom_vanishing
13. `subsheaf_zeroOutsideInt_vanishing` (line 399) — depends on Tier 1-3 infrastructure
14. `epiImage_zeroOutsideInt_vanishing` (line 417) — depends on Steps 4+5+LES

## This Cycle's Work Items

### 1. [/prove] Restore Tier 1 sorry's (5 proofs)
Extract proofs from `e90c2f0`, adapt to current API. These are independent and self-contained:
- `presheaf_stalk_surj_openHom`: presheaf restriction + eqToHom argument
- `isZero_zeroOutsideInt_bot`: stalks vanish via ¬(W ≤ ⊥) + toSheafify iso
- `stalk_zeroOutsideInt_zero_outside`: similar stalk argument
- `exists_nonzero_stalk_in_V`: contrapositive + sheaf_isZero_of_zero_stalks
- `presheaf_stalk_zeroOutside_eq_zsmul_generator`: int_addSubgroup_eq_zmultiples + germ algebra

### 2. [/prove] Restore Tier 2 sorry's (3 proofs)
- `sheaf_stalk_surj_openHom`: transfer via toSheafify naturality
- `stalk_zeroOutsideInt_eq_zsmul_generator`: transfer via toSheafify
- `sheaf_stalk_bijective_openHom`: injectivity via PreservesMonomorphisms

### 3. [/prove] Restore `zeroOutsideInt_vanishing` (line 76)
The inline `sorry : IsFlasqueSheaf S.X₂` needs: `S.X₂ = zeroOutsideInt ⊤ = constantSheaf Z_X` (by rfl), which is flasque on irreducible spaces (proved in ConstantSheafFlasque.lean). Provide the instance chain explicitly.

## Backlog (future cycles)

- **Tier 3-4 sorry's**: `cokernel_stalk_zero_V`, `cokernel_openHom_vanishing`, `zeroOutsideInt_cohomology_vanishing`, `subsheaf_zeroOutsideInt_vanishing`, `epiImage_zeroOutsideInt_vanishing`
- **Original sorry's**: `exists_good_section`, `cohomology_vanishing_of_finitelyGenerated_vanishing` (genuine Mathlib gaps)
- **Docs deployment**: Fix 404 on blueprint pages
- **File sizes**: ZeroOutside.lean (733), FlasqueVanishing.lean (616) over guideline
- **Documentation**: Update sorry counts after each fix
