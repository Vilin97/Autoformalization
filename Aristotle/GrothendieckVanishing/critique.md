# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-03T21:05Z
**Reviewer verdict**: REVISE

---

## 0. CI Status

- Latest 3 CI runs on `wip/grothendieck-vanishing`: **all green** (success).
- Local `lake build`: no errors, only sorry warnings.
- **Blueprint/docs: HTTP 404.** Both `https://vilin97.github.io/aristotle/blueprint/` and `dep_graph_document.html` return 404. No deploy workflow exists separate from CI. Docs have been broken for 6+ days.

**Open issues:**
- [ ] P1: Blueprint and dependency graph return 404.

## 1. Sorry's

Three `sorry` keywords in `FiniteGeneratorReduction.lean`, all downstream of one logical gap:

| Location | Statement | Risk |
|---|---|---|
| L202 | `isSheaf_presheaf_filtered_colimit` — presheaf filtered colimit is sheaf on Noetherian | True (Stacks 009E). Partially scaffolded (finite subcover obtained at L200). |
| L230 | Base case n=0 of `sheafH_filtered_colimit_aux` | Requires `createsFilteredColimit` which depends on L202. |
| L249 | `hQ` — cokernel has vanishing H^n in inductive step | Needs cokernel colimit diagram + IH. Structurally sound, depends on L202. |

All three collapse to one gap: proving the presheaf-level filtered colimit of sheaves on a Noetherian space is a sheaf.

**`lean_verify` inconsistency**: `lean_verify GrothendieckVanishing` reports `{"axioms":[]}` (no axioms at all), while `lean_verify sheafH_preserves_filtered_colimits` correctly reports `sorryAx`. Tool appears buggy for some theorem names. Code analysis confirms the sorry propagates to the main theorem via: `GrothendieckVanishing` → `IrreduciblePosVanishing` → `directLimit_cohomology_vanishing` → `sheafH_preserves_filtered_colimits` → sorry. **The main theorem is NOT sorry-free.**

**Open issues:**
- [ ] P1: Close `isSheaf_presheaf_filtered_colimit` (all 3 sorry's collapse to this)

## 2. Hidden Axioms

No `admit`, `axiom`, `native_decide`, or `Decidable.decide` in any main file. No `set_option linter` overrides. No `maxHeartbeats` overrides. Beyond the known sorry, I found no issue.

## 3. Circularity

- Main theorem: well-founded induction on `topologicalKrullDim X : WithBot ℕ∞`.
- Filtered colimit step: plain `ℕ`-induction on cohomological degree, independent of spatial dimension.
- `IrreduciblePosVanishing` receives `ih` quantified over strictly smaller dimension. No self-reference.
- Degree cascade takes `hbase` as hypothesis, not from conclusion.
- I found no circularity.

## 4. Hypothesis Audit

```lean
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

| Hypothesis | Necessary? | Weakness |
|---|---|---|
| `X : TopCat.{u}` | Yes | Could generalize to abstract Noetherian site |
| `[NoetherianSpace X]` | Yes — finite subcover, Krull dim finiteness | Cannot weaken |
| `F : Sheaf AddCommGrpCat.{u} X` | Yes | Could generalize to `ModuleCat R` |
| `n : ℕ` | Yes | Standard convention |
| `h : n > topologicalKrullDim X` | Yes | Exactly Hartshorne's bound |

- [ ] P3: Stated for `AddCommGrpCat` only; `ModuleCat R` generalization would be more useful.

## 5. Mathematical Correctness

Follows Hartshorne III.2.7 faithfully. The remaining sorry (`isSheaf_presheaf_filtered_colimit`) is a standard result (Stacks 009E). Scaffolding at L197-201 correctly obtains Noetherian finite subcover; gap is connecting finite subcover → finite limit → `colimitLimitIso`. I found no divergence.

## 6. Code Quality

| Issue | File | Severity |
|---|---|---|
| 616 lines | FlasqueVanishing.lean | P3 — over 600-line threshold |
| `createsFilteredColimit` defined but never called | FiniteGeneratorReduction.lean:205 | P3 — dead code |
| `ext_sandwich` defined but never called | FiniteGeneratorReduction.lean:58 | P3 — dead code |
| `addCommGrpCat_exact_sandwich` only used by dead `ext_sandwich` | FiniteGeneratorReduction.lean:29 | P3 — dead code |
| `subsingleton_ext_of_ses` duplicates private `ext_dimension_shift` | SheafStalkAlgebra.lean:23 vs FiniteGeneratorReduction.lean:45 | P3 — duplication |
| `subsingleton_ext_of_ses_middle` never called outside its file | SheafStalkAlgebra.lean:39 | P3 — dead code |
| 3 files use blanket `import Mathlib` | Auxiliary.lean, FlasqueVanishing.lean, ZeroOutside.lean | P4 — build perf, upstreamability |

No `maxHeartbeats` overrides. No `set_option linter` overrides.

**Open issues:**
- [ ] P3: FlasqueVanishing.lean over 600 lines — split
- [ ] P3: Delete dead code: `createsFilteredColimit`, `ext_sandwich`, `addCommGrpCat_exact_sandwich`
- [ ] P3: Delete or consolidate duplicate `subsingleton_ext_of_ses`
- [ ] P3: Delete unused `subsingleton_ext_of_ses_middle`
- [ ] P4: Replace blanket `import Mathlib` with specific imports

## 7. Documentation Lies

| Claim | Location | Reality | Verdict |
|---|---|---|---|
| "SetupCore.lean: category instances, FlasqueVanishing, ..." | main.lean:12 | Category instances and FlasqueVanishing are in FlasqueVanishing.lean, not SetupCore | **STALE** |
| "Ext LES lemmas (subsingleton_ext_of_ses, ext_dimension_shift, ext_sandwich)" | SheafStalkAlgebra.lean:5 | `ext_dimension_shift` and `ext_sandwich` are in FiniteGeneratorReduction.lean | **LIE** |
| "ext_sandwich, addCommGrpCat_exact_sandwich" as key results | FiniteGeneratorReduction.lean:5 | `ext_sandwich` is dead code (never called) | **MISLEADING** |

Previously flagged lies (GrothendieckVanishing.lean:8, IrreducibleStep.lean:9, SheafStalkAlgebra.lean:319) have been **FIXED** since last critique.

**Open issues:**
- [ ] P3: Fix main.lean:12 docstring (SetupCore doesn't contain FlasqueVanishing or category instances)
- [ ] P3: Fix SheafStalkAlgebra.lean:5 docstring (remove ext_dimension_shift, ext_sandwich references)
- [ ] P3: Fix FiniteGeneratorReduction.lean:5 docstring (ext_sandwich is dead code)

## 8. Generalization Opportunities

1. **`AddCommGrpCat` → `ModuleCat R`**: Entire proof should work for module categories. Sheaves of R-modules on Noetherian space form Grothendieck abelian category. Feasibility: moderate. Impact: high.

2. **Extract `isSheaf_presheaf_filtered_colimit` as standalone Mathlib result**: "Filtered colimits of sheaves are sheaves on a Noetherian site" is independently valuable. Feasibility: moderate (scaffolding exists). Impact: high.

3. **`Subsingleton` → `IsZero`**: Currently `Subsingleton (Sheaf.H F n)`. An `IsZero` formulation composes better with categorical API. Feasibility: easy. Impact: low.

4. **Weaken `TopCat` to locally Noetherian ringed space**: Standard algebraic geometry setting. Feasibility: hard. Impact: high.

5. **Sheaf cohomology via derived categories**: Current approach uses `Ext`. Derived category formulation more flexible. Feasibility: depends on Mathlib maturity. Impact: medium.

## 9. Mathlib Upstreamability

| Candidate | Status | Blocker |
|---|---|---|
| `isSheaf_presheaf_filtered_colimit` | Needs proof | Sorry |
| `constantSheaf_flasque_of_irreducible` | Clean, self-contained | None — ready to PR |
| `FlasqueVanishing` | Clean statement | File too large, needs splitting |
| `topologicalKrullDim_lt_of_isIrreducible_of_isClosed` | Standalone topology lemma | None — ready to PR |
| `subsingleton_sheafH_of_shortExact_middle` | LES for sheaf cohomology | None — high value |
| `sheafH_dimension_shift_ses` | Dimension shifting | None — ready to PR |
| `GrothendieckVanishing` | Main theorem | Sorry in dependency |

## Verdict: REVISE

### Conditions for CONDITIONAL ACCEPT:
1. Close the 1 remaining sorry (`isSheaf_presheaf_filtered_colimit`)
2. Fix blueprint 404

### Conditions for full ACCEPT:
All of the above, plus:
3. Delete all dead code (5 dead theorems/definitions identified)
4. Fix all 3 stale/lying docstrings
5. Split FlasqueVanishing.lean below 600 lines
