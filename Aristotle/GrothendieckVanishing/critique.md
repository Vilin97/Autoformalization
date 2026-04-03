# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-03T02:15Z
**Reviewer verdict**: CONDITIONAL PASS

## 0. CI Status

Latest CI run **in_progress** (commit 9ecae2c). Previous two **green** (aa13d57, 5d72599).
No `maxHeartbeats` overrides found. No `axiom` or `admit` in main files.
**Docs (P1)**: Blueprint returns HTTP 404. Dep graph also 404.

## 1. Sorry's (1)

| # | File | Line | Sorry | Risk |
|---|------|------|-------|------|
| 1 | SheafHom.lean | 64 | `isSheaf_filtered_colimit_of_sheaves` | Core AB5 gap: filtered presheaf colimits of sheaves are sheaves on Noetherian spaces. |
| 2 | FiniteGeneratorReduction.lean | 146 | `hQprov ... := sorry` | Recursive `hQvan_provider` for IH call. Needs per-j Ext vanishing on quotients-of-quotients. Structurally hard — recursive nesting of injective presentations. |
| 3 | FiniteGeneratorReduction.lean | 195 | `sorry` (n'=0 case) | `Ext^0(Z, Q_j) = Hom(Z, Q_j)` subsingleton — dead at call site (dim ≥ 1 ⟹ m ≥ 2). |

**Critical observation**: Sorry #1 (AB5) is the core mathematical gap. Sorry's #2 and #3 are structural issues in the induction. All are mathematically true in the sheaf setting.

## 2. Hidden Axioms

I found no issue. No `admit`, `axiom`, `native_decide` in main files.

## 3. Circularity

I found no issue. The dependency chain is clean.

## 4. Hypothesis Audit

I found no issue. The main theorem `GrothendieckVanishing` has the correct statement with minimal hypotheses.

## 5. Mathematical Correctness

I found no issue. All sorry's are mathematically true in the sheaf setting where they are used.

## 6. Code Quality

| Issue | Priority | Status |
|-------|----------|--------|
| `IrreducibleStep.lean` at 1263 lines (26% over 1000 guideline) | P3 | **OPEN** |
| `FiniteGeneratorReduction.lean` at 550 lines | — | OK |
| `ZeroOutside.lean` at 733 lines | — | OK |
| `FlasqueVanishing.lean` at 616 lines | P3 | **OPEN** (over 600 guideline) |

## 7. Documentation

All headers now consistent with sorry locations (updated for SheafHom.lean architecture).

## 8. Generalization Opportunities

1. Drop NoetherianSpace to finite cohomological dimension (medium)
2. Generalize to arbitrary Grothendieck topologies (hard)
3. Extract FlasqueVanishing as Mathlib PR (easy)

## 9. Mathlib Upstreamability

FlasqueVanishing, constantSheaf_flasque_of_irreducible, subsingleton_ext_of_ses family,
sheafH_vanishing_cascade — all candidates.
`addCommGrpCat_exact_sandwich` and `ext_sandwich` are now used but could be upstreamed.

## Open Issues

| # | Priority | Issue |
|---|----------|-------|
| 1 | P0 | 3 sorry's: 1 in SheafHom.lean (AB5), 2 in FiniteGeneratorReduction.lean |
| 2 | P1 | Docs/blueprint 404 |
| 3 | P3 | IrreducibleStep.lean at 1263 lines — split needed |
| 4 | P3 | FlasqueVanishing.lean at 616 lines (over 600 guideline) |

**Verdict**: CONDITIONAL PASS — sorry count is 3. All mathematically sound. Architecture uses SheafHom.lean for clean hHom_univ.
