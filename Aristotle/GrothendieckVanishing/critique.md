# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-03T09:00Z
**Reviewer verdict**: REVISE

## 0. CI Status

Latest CI run **in_progress** (commit d41f8f6). Previous two **green**.
No `maxHeartbeats` overrides. No `axiom` or `admit` in main files.

**Docs (P1)**: Blueprint returns HTTP 404. Dependency graph also 404. The `deploy.yml` workflow last ran on `main` branch (2026-03-28) and succeeded, but docs are not deployed for the working branch. This means the public documentation is broken or non-existent for the current state of the theorem.

## 1. Sorry's (3)

| # | File | Line | Sorry | Risk |
|---|------|------|-------|------|
| 1 | SheafHom.lean | 63 | `isSheaf_filtered_colimit_of_sheaves` | Core AB5 gap: filtered presheaf colimits of sheaves are sheaves on Noetherian spaces. Mathematically true (filtered colimits commute with finite limits, Noetherian ⟹ finite covers). But without this, the entire colimit-of-subsheaves argument is unsound. |
| 2 | FiniteGeneratorReduction.lean | 188 | `hQprov ... := sorry` | Recursive `hQvan_provider` for IH call at degree n'+1. Needs Ext vanishing on quotients-of-quotients. The induction structure is suspect — the sorry asks for vanishing on `cokernel(Qcocone.ι.app j ≫ ip'.shortComplex.f)`, which is a quotient of the colimit point of Qcocone, itself a cokernel. This double nesting may not terminate. |
| 3 | FiniteGeneratorReduction.lean | 237 | `sorry` (n'=0 case) | `Ext^0(Z, Q_j) = Hom(Z, Q_j)` subsingleton — claimed dead at call site (dim ≥ 1 ⟹ m ≥ 2 ⟹ n' ≥ 1). But the dead-code claim is NOT verified in Lean. A `by omega` or `absurd` would close it if truly dead; the sorry suggests the claim may be wrong or the context doesn't carry enough information to prove it. |

**Risk assessment**: Sorry #2 (hQprov) is the most dangerous. The induction may not be well-founded — the recursion goes: to prove Ext^{n+1}(Z, c.pt) = 0, embed c.pt → I → Q, need Ext^n(Z, Q) = 0, apply IH to Q's colimit decomposition, which needs per-j Ext^{n-1} on Q_j's quotients, etc. Each level introduces a NEW injective presentation and new quotients. The "provider" pattern hides whether this actually terminates.

**CLAUDE.md line number lies**: CLAUDE.md says sorry #2 is at line 146, actually at line 188. Says sorry #3 is at line 195, actually at line 237. main.lean also cites wrong line numbers (146, 195).

## 2. Hidden Axioms

`lean_verify` on `GrothendieckVanishing` returns empty axioms list (no axioms beyond the standard ones). No `admit`, `axiom`, or `native_decide` found.

I found no issue beyond the 3 sorry's.

## 3. Circularity

The dependency chain is: `GrothendieckVanishing` → `grothendieck_vanishing_aux` → `IrreduciblePosVanishing` → `directLimit_cohomology_vanishing` → `cohomology_vanishing_of_finitelyGenerated_vanishing` → `ext_comm_filtered_colimit_mono` → `ext_vanishing_of_colimit_aux`.

The well-founded induction is on `topologicalKrullDim`, which is correct. No circular dependency detected.

However: `ext_vanishing_of_colimit_aux` uses strong induction on `n` (the Ext degree). The sorry'd `hQprov` at the `succ n'` case asks for vanishing at degree `n''` where `n' + 1 = n'' + 1`, i.e., `n'' = n'`. This is NOT a decrease in the induction variable — it's a LATERAL step at the same degree on a DIFFERENT object. The well-foundedness depends on the outer dimension induction, not the inner Ext-degree induction. This is not circular but the sorry hides whether the outer induction actually provides what's needed.

## 4. Hypothesis Audit

Main theorem:
```lean
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

- `TopCat.{u}`: universe-polymorphic. Fine.
- `NoetherianSpace X`: necessary for Grothendieck vanishing. Cannot weaken.
- `n : ℕ`: uses natural numbers, not integers. Fine — sheaf cohomology is only defined for n ≥ 0.
- `h : n > topologicalKrullDim X`: correct. Uses `WithBot ℕ∞` coercion.
- `Subsingleton (Sheaf.H F n)`: encodes `H^n = 0` as subsingleton (one element, namely zero). This is the correct formulation for a zero object in `AddCommGrpCat`.

I found no unnecessary hypothesis.

## 5. Mathematical Correctness

The overall proof strategy follows Hartshorne III.2.7 faithfully:
1. Reduce to irreducible X (ClosedOpenDecomposition) ✓
2. Dim 0 base case (DimZeroVanishing) ✓
3. Dim ≥ 1: write K as colimit of f.g. subsheaves, each f.g. subsheaf has an epi from ⊕ zeroOutsideInt, use SES + induction ✓
4. Cascade: vanishing at degree m₀ implies vanishing at all m ≥ m₀ ✓

**Divergence**: The standard proof uses that filtered colimits of sheaves are sheaves (exact in the AB5 sense). The formalization delegates this to `isSheaf_filtered_colimit_of_sheaves` which is sorry'd. This is the correct mathematical fact but it's a non-trivial lemma — in Mathlib, `Sheaf.ab5ofSize` exists but doesn't directly give `PreservesColimit` for `sheafToPresheaf`. The workaround via `createsColimitOfIsSheaf` is clever but requires the sorry.

**Potential issue with hQprov**: In Hartshorne's proof, the colimit step (Lemma 2.9) is stated for a FIXED generator Z and uses that Hom(Z, -) commutes with filtered colimits. The formalization's recursive `hQprov` pattern goes beyond what Hartshorne does — it tries to prove Ext^n commutes with filtered colimits by induction on n, but each step creates new quotients that need their own colimit decomposition. Hartshorne avoids this by using that the category has enough injectives + generators directly, without recursing into quotients of quotients.

## 6. Code Quality

| Issue | Priority | Status |
|-------|----------|--------|
| `IrreducibleStep.lean` at 1264 lines — 2x the 600-line guideline | P2 | **OPEN** |
| `ZeroOutside.lean` at 733 lines — 22% over guideline | P3 | **OPEN** |
| `SheafStalkAlgebra.lean` at 688 lines — 15% over guideline | P3 | **OPEN** |
| `FlasqueVanishing.lean` at 616 lines — 3% over guideline | P3 | **OPEN** |
| Line number lies in CLAUDE.md and main.lean | P2 | **OPEN** |
| `finsetCoproductIncl` duplicated: exists in both FiniteGeneratorReduction.lean (line 253) and as `finsetCoproductInclGen` (line 253). The `finsetCoproductIncl` (line 382) in the FinsetGenerated section is a SEPARATE definition with slightly different types — this is confusing | P3 | **OPEN** |

## 7. Documentation Lies

| Claim | Location | Reality |
|-------|----------|---------|
| sorry #2 at line 146 | CLAUDE.md:78 | Actually at line 188 |
| sorry #3 at line 195 | CLAUDE.md:79 | Actually at line 237 |
| sorry #2 at line 146 | main.lean:11 | Actually at line 188 |
| sorry #3 at line 195 | main.lean:12 | Actually at line 237 |
| "3 sorry's" | critique.md old | Line count correct but line numbers stale |

## 8. Generalization Opportunities

1. **Drop `NoetherianSpace` to finite cohomological dimension** (medium): The theorem holds for any topological space with `cd(X) < ∞`. The Noetherian condition is used for: (a) finite covers in sheaf condition, (b) well-founded induction on Krull dim, (c) every subsheaf of a finitely generated sheaf is finitely generated. Dropping it requires a completely different proof strategy.

2. **Replace `AddCommGrpCat` with arbitrary Grothendieck abelian category** (medium-hard): The theorem should hold for `Sh(X, A)` where `A` is any Grothendieck abelian category. Currently hardcoded to `AddCommGrpCat.{u}` throughout. Would require parameterizing ~15 files.

3. **Extract the Ext-colimit machinery as standalone** (easy): `ext_vanishing_of_colimit_aux` and `ext_comm_filtered_colimit_mono` are pure category theory — they work in any Grothendieck abelian category. Currently buried in `FiniteGeneratorReduction.lean` with sheaf-specific imports.

4. **Close sorry #3 with `absurd`/`omega`** (easy): If the n'=0 case is truly dead at the call site, add a hypothesis `hn : n' ≥ 1` or `n' ≠ 0` and close with `omega`. The current sorry is lazy.

## 9. Mathlib Upstreamability

| Lemma | File | Upstreamable? | Changes needed |
|-------|------|---------------|----------------|
| `addCommGrpCat_exact_sandwich` | FiniteGeneratorReduction.lean | Yes | Generalize to arbitrary concrete abelian categories |
| `ext_dimension_shift` | FiniteGeneratorReduction.lean | Yes | Already general over `C'` |
| `ext_sandwich` | FiniteGeneratorReduction.lean | Yes | Already general |
| `sheafH_vanishing_cascade` | GrothendieckVanishing.lean | Yes | Clean, well-typed |
| `addCommGrpCat_colimit_subsingleton_of_pieces` | SheafHom.lean | Yes | Generalize to `ConcreteCategory` |
| `constantSheaf_hom_preserves_filtered_colimit_vanishing` | SheafHom.lean | Blocked | Depends on sorry |
| `FlasqueVanishing` | FlasqueVanishing.lean | Yes | Most natural PR candidate |

## Open Issues

| # | Priority | Issue |
|---|----------|-------|
| 1 | P0 | 3 sorry's remain |
| 2 | P1 | Docs/blueprint return 404 |
| 3 | P2 | CLAUDE.md and main.lean cite wrong line numbers for sorry's #2 and #3 |
| 4 | P2 | IrreducibleStep.lean at 1264 lines — needs splitting |
| 5 | P2 | hQprov sorry may hide a well-foundedness issue in the induction |
| 6 | P3 | sorry #3 (n'=0 dead case) could be closed with `absurd`/`omega` if truly dead |
| 7 | P3 | ZeroOutside.lean (733), SheafStalkAlgebra.lean (688), FlasqueVanishing.lean (616) over 600-line guideline |
| 8 | P3 | `finsetCoproductIncl` vs `finsetCoproductInclGen` naming confusion |

**Verdict**: REVISE — documentation lies (#3) are inexcusable. Sorry #3 (#6) should be closeable or provably dead. The hQprov induction structure (#5) needs mathematical justification that it terminates. File sizes (#4, #7) are technical debt accumulating beyond guidelines.
