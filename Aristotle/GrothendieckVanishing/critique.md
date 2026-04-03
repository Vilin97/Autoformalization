# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-03T20:15Z
**Reviewer verdict**: REVISE

## 0. CI Status

- Latest CI run (`e610f53`): **in_progress** at time of check. Previous two: success.
- Local `lake build`: **no errors**, only sorry warnings.
- **Blueprint/docs: HTTP 404.** Both `https://vilin97.github.io/aristotle/blueprint/` and `dep_graph_document.html` return 404. Deploy workflow last ran on `main` (2026-03-28); active branch `wip/grothendieck-vanishing` never triggers deploy. Docs stale 6 days.

**Open issues:**
- [ ] P1: Blueprint and dependency graph return 404.

## 1. Sorry's

Three `sorry` keywords in `FiniteGeneratorReduction.lean`, all downstream of one logical gap:

| Location | Statement | Risk |
|---|---|---|
| L197 | `isSheaf_presheaf_filtered_colimit` — presheaf colimit is sheaf on Noetherian | True (Stacks 009E). Low. |
| L225 | Base case n=0 of `sheafH_filtered_colimit_aux` | Follows from L197. |
| L244 | `hQ` — cokernel has vanishing H^n | Needs cokernel colimit diagram + AB5 + IH. True but hard. |

**Open issues:**
- [ ] P1: Close `isSheaf_presheaf_filtered_colimit`
- [ ] P1: Close `hQ` (cokernel colimit construction)
- [ ] P2: Close base case n=0

## 2. Hidden Axioms

`lean_verify GrothendieckVanishing`: `propext`, **`sorryAx`**, `Classical.choice`, `Quot.sound`.
`lean_verify FlasqueVanishing`: clean (no `sorryAx`).
No `admit`, `axiom`, `native_decide` in main files. I found no issue beyond the known sorry.

## 3. Circularity

Well-founded induction on `topologicalKrullDim` (`WithBot ℕ∞`). The colimit step is independent of the main induction. The `ih` in `sheafH_filtered_colimit_aux` quantifies over ALL diagrams at degree `n`, applied to the cokernel diagram — valid `ℕ` induction. I found no circularity.

## 4. Hypothesis Audit

| Hypothesis | Necessary? | Could weaken? |
|---|---|---|
| `X : TopCat.{u}` | Yes | Could generalize to Noetherian site |
| `[NoetherianSpace X]` | Yes | No |
| `F : Sheaf AddCommGrpCat X` | Yes | Could generalize to `ModuleCat R` |
| `n : ℕ` | Yes | Correct convention |
| `h : n > topologicalKrullDim X` | Yes | Exactly Hartshorne's bound |

- [ ] P3: Theorem stated for `AddCommGrpCat` only; `ModuleCat R` would be more useful.

## 5. Mathematical Correctness

Follows Hartshorne III.2.7 faithfully. Dimension shifting via injective embedding is standard. `isSheaf_presheaf_filtered_colimit` is Stacks 009E / SGA4 VII. I found no divergence.

## 6. Code Quality

| Issue | File | Severity |
|---|---|---|
| 616 lines | FlasqueVanishing.lean | P3 — over 600-line threshold |
| `createsFilteredColimit` defined but never used | FiniteGeneratorReduction.lean:200 | P3 — dead code |
| Inconsistent `haveI` vs `letI` in two induction cases | FiniteGeneratorReduction.lean:224,229 | P4 |

No `maxHeartbeats` overrides. No `set_option linter` overrides.

- [ ] P3: FlasqueVanishing.lean over 600 lines
- [ ] P3: Dead code `createsFilteredColimit`
- [ ] P4: Inconsistent instance handling

## 7. Documentation Lies

| Claim | Location | Reality | Verdict |
|---|---|---|---|
| "modulo 2 sorry's: 1 AB5 in SheafHom.lean" | GrothendieckVanishing.lean:8 | **SheafHom.lean does not exist.** 1 sorry, not 2. | **LIE** |
| "2 sorry's: 1 in SheafHom.lean (AB5)" | IrreducibleStep.lean:9 | Same — SheafHom.lean was deleted. | **LIE** |
| "`ext_vanishing_of_colimit_aux` have 2 sorry's" | SheafStalkAlgebra.lean:319 | Neither theorem exists anymore. | **LIE** |
| "1 sorry remains" | CLAUDE.md:76 | 1 logical gap, 3 sorry keywords. | Acceptable |

- [ ] P2: Fix GrothendieckVanishing.lean:8 stale docstring (SheafHom.lean, 2 sorry's)
- [ ] P2: Fix IrreducibleStep.lean:9 stale docstring
- [ ] P2: Fix SheafStalkAlgebra.lean:319 stale comment

## 8. Generalization Opportunities

1. **`AddCommGrpCat` → `ModuleCat R`**: All constructions should work for module categories. Feasibility: moderate. Impact: high.
2. **`TopCat` → abstract Noetherian site**: Feasibility: hard. Impact: medium.
3. **`Subsingleton` → explicit iso to zero**: Feasibility: easy. Impact: low.
4. **Extract `isSheaf_presheaf_filtered_colimit` as standalone Mathlib result**: Feasibility: requires proving it. Impact: high.

## 9. Mathlib Upstreamability

| Candidate | Status |
|---|---|
| `isSheaf_presheaf_filtered_colimit` | Needs proof first. High value. |
| `constantSheaf_flasque_of_irreducible` | Clean. Ready to upstream. |
| `topologicalKrullDim_lt_of_isIrreducible_of_isClosed` | Clean standalone lemma. |
| `subsingleton_sheafH_of_shortExact_middle` | LES for sheaf cohomology. High value. |
| `FlasqueVanishing` | Needs splitting for Mathlib style. |

## Verdict: REVISE

**Conditions for acceptance:**
1. Close `isSheaf_presheaf_filtered_colimit` (P1)
2. Close `hQ` in the inductive step (P1)
3. Fix all stale docstrings referencing SheafHom.lean / nonexistent theorems (P2)
4. Fix blueprint/docs 404 (P1)
5. Reduce FlasqueVanishing.lean below 600 lines (P3)
6. Remove or use dead code `createsFilteredColimit` (P3)
