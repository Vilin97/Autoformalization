# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-03T19:00Z
**Reviewer verdict**: REVISE

## 0. CI Status

Latest CI run **in_progress** (commit bb64f45, current push). Previous run **failed** (d41f8f6 — stale IrreducibleStep.lean duplicates, now fixed). The run before that was **green**.

No `maxHeartbeats` overrides. No `axiom` or `admit` in main files. Local `lake build` on all modified files passes.

**Docs (P1)**: Blueprint returns HTTP 404. Dependency graph also 404. Documentation is not deployed for the working branch. Public-facing docs are broken.

## 1. Sorry's (2)

| # | File | Line | Sorry | Risk |
|---|------|------|-------|------|
| 1 | SheafHom.lean | 63 | `isSheaf_filtered_colimit_of_sheaves` | Core AB5 gap: filtered presheaf colimits of sheaves are sheaves on Noetherian spaces. Mathematically true but non-trivial. Without this, the colimit-of-subsheaves argument is unsound. `Sheaf.ab5ofSize` exists in Mathlib but doesn't directly give what's needed. |
| 2 | FiniteGeneratorReduction.lean | 180,188 | `hQprov` (2 sorry keywords) | Recursive quotient-of-quotient vanishing. The `by sorry` at line 180 needs `Subsingleton (Ext Z Q 0)` = `Subsingleton (Hom(Z,Q))` where Q is a colimit point. The `:= sorry` at line 188 needs per-j vanishing on `cokernel(ι_j ≫ f)` at degree n'. These two sorry's are logically one gap — the recursive "provider" for the inner Ext-degree induction. |

**Risk assessment**: Sorry #1 (AB5) is a clean mathematical statement, likely provable from `Sheaf.ab5ofSize` + Noetherian finite-cover machinery. Sorry #2 (hQprov) is structurally harder — it requires showing the outer dimension induction provides what the inner Ext-degree induction needs. The hQprov at line 188 asks for vanishing on `cokernel(Qcocone.ι.app j ≫ ip'.shortComplex.f)` at the SAME degree n' — this is a lateral step, not a decrease. Well-foundedness depends on the dimension decreasing via the outer induction, but the sorry hides whether this connection is actually made.

## 2. Hidden Axioms

No `admit`, `axiom`, `native_decide`, or `set_option linter.all false` found in any main file.

I found no issue beyond the 2 sorry's.

## 3. Circularity

Dependency chain: `GrothendieckVanishing` → `grothendieck_vanishing_aux` (WF induction on dim) → `IrreduciblePosVanishing` → `directLimit_cohomology_vanishing` → `cohomology_vanishing_of_finitelyGenerated_vanishing` → `ext_comm_filtered_colimit_mono` → `ext_vanishing_of_colimit_aux`.

The well-founded induction on `topologicalKrullDim` is correct. No circular dependency.

**Concern**: `ext_vanishing_of_colimit_aux` uses strong induction on Ext degree `n`. The sorry'd `hQprov` at `succ n'` asks for vanishing at degree `n''` where `n' + 1 = n'' + 1`, i.e., `n'' = n'`. This is NOT a decrease — it's a lateral step on a different object (quotient of the colimit point). Correctness depends on the outer dimension induction providing this, but the sorry prevents verification.

## 4. Hypothesis Audit

```lean
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

- `TopCat.{u}`: universe-polymorphic. Fine.
- `NoetherianSpace X`: necessary for this proof strategy. Cannot weaken without a completely different approach.
- `n : ℕ`: correct — sheaf cohomology is defined for n ≥ 0.
- `h : n > topologicalKrullDim X`: correct formulation via `WithBot ℕ∞`.
- `Subsingleton (Sheaf.H F n)`: correct encoding of `H^n = 0`.

I found no unnecessary hypothesis.

## 5. Mathematical Correctness

The proof strategy follows Hartshorne III.2.7:
1. Reduce to irreducible X (ClosedOpenDecomposition) ✓
2. Dim 0 base case (DimZeroVanishing) ✓
3. Dim ≥ 1: write K as colimit of f.g. subsheaves, each has epi from ⊕ zeroOutsideInt, use SES + induction ✓
4. Cascade: vanishing at degree m₀ implies vanishing at all m ≥ m₀ ✓

**Divergence from Hartshorne**: Hartshorne's Lemma 2.9 uses that the category has enough injectives and a generator, so Hom(Z,-) commutes with filtered colimits. The formalization's `hQprov` pattern goes beyond this — it tries to prove Ext^n commutes with filtered colimits by induction on n, but each step creates new injective presentations and quotients. Hartshorne avoids this recursive nesting. The formalization may be doing unnecessary work, or it may be that the sorry hides a genuine gap in the proof strategy.

## 6. Code Quality

| Issue | Priority | Status |
|-------|----------|--------|
| `ZeroOutside.lean` at 733 lines — 22% over 600-line guideline | P3 | **OPEN** |
| `SheafStalkAlgebra.lean` at 688 lines — 15% over guideline | P3 | **OPEN** |
| `FlasqueVanishing.lean` at 616 lines — 3% over guideline | P3 | **OPEN** |
| `IrreducibleStep.lean` reduced from 1264 to 595 lines | — | **FIXED this cycle** |
| `finsetCoproductIncl` naming confusion in FiniteGeneratorReduction.lean | P3 | **OPEN** |
| Previous CI run (d41f8f6) failed due to stale duplicates | — | **FIXED this cycle** |

## 7. Documentation Lies

| Claim | Location | Reality |
|-------|----------|---------|
| "2 sorry's" | main.lean:7, CLAUDE.md:76 | Correct |
| SheafHom.lean:63 | main.lean:8, CLAUDE.md:77 | Correct |
| FiniteGeneratorReduction.lean:180,188 | main.lean:11, CLAUDE.md:78 | Correct |

Documentation is now accurate after this cycle's fixes.

## 8. Generalization Opportunities

1. **Replace `AddCommGrpCat` with arbitrary Grothendieck abelian category** (medium-hard): The theorem holds for `Sh(X, A)` where `A` is any Grothendieck abelian category. Currently hardcoded to `AddCommGrpCat.{u}` in ~15 files. Would make the result far more reusable.

2. **Extract the Ext-colimit machinery as standalone** (easy): `ext_vanishing_of_colimit_aux`, `ext_sandwich`, `ext_dimension_shift` are pure category theory. Currently buried in sheaf-specific files.

3. **Drop `NoetherianSpace` to finite cohomological dimension** (hard): The theorem holds for any topological space with `cd(X) < ∞`. Requires a completely different proof approach.

4. **Eliminate hQprov sorry by restructuring the induction** (medium): Rather than recursing into quotients of quotients, use the dimension induction to provide vanishing on all objects in the category at the right degree, then the inner Ext-degree induction becomes a simple consequence. This would also resolve the well-foundedness concern.

## 9. Mathlib Upstreamability

| Lemma | File | Upstreamable? | Changes needed |
|-------|------|---------------|----------------|
| `FlasqueVanishing` | FlasqueVanishing.lean | Yes | Most natural PR candidate. Clean statement. |
| `sheafH_vanishing_cascade` | GrothendieckVanishing.lean | Yes | Clean, well-typed |
| `ext_sandwich` | FiniteGeneratorReduction.lean | Yes | Already general over `C` |
| `ext_dimension_shift` | FiniteGeneratorReduction.lean | Yes | Already general |
| `addCommGrpCat_exact_sandwich` | FiniteGeneratorReduction.lean | Yes | Generalize to `ConcreteCategory` |
| `subsingleton_ext_of_ses` family | SheafStalkAlgebra.lean | Yes | Pure category theory |

## Open Issues

| # | Priority | Issue |
|---|----------|-------|
| 1 | P0 | 2 sorry's remain (AB5 + hQprov) |
| 2 | P1 | Docs/blueprint return 404 |
| 3 | P2 | hQprov sorry may hide a well-foundedness issue in the induction |
| 4 | P3 | ZeroOutside.lean (733), SheafStalkAlgebra.lean (688), FlasqueVanishing.lean (616) over 600-line guideline |
| 5 | P3 | `finsetCoproductIncl` naming confusion |

**Verdict**: REVISE — 2 sorry's remain, the most dangerous being hQprov which may hide a proof strategy error. The AB5 sorry is mathematically clean. Docs are broken. File sizes are over guideline in 3 files.
