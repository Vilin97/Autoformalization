# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-04T21:57Z
**Verdict**: **REVISE** — 1 sorry remains, blueprint 404

---

## 0. CI Status

- **Build CI**: All 3 recent runs PASS on `wip/grothendieck-vanishing`. No build failures.
- **Blueprint/Docs (P1)**: `https://vilin97.github.io/aristotle/blueprint/` returns **HTTP 404**. `dep_graph_document.html` also **404**. No deployment workflow found. The documentation is completely broken/non-existent. This is a P1 issue — the project claims to have docs but they don't exist.

## 1. Sorry's

**Documentation claims 1 sorry. There are actually 2.**

| # | File:Line | Statement | True? | Risk |
|---|-----------|-----------|-------|------|
| 1 | `FiniteGeneratorReduction.lean:43` | `gabriel_injective_of_filtered_colimit` — filtered colimits of injectives are injective on Noetherian spaces | TRUE (Gabriel's theorem) | Medium: standard result but not in Mathlib |
| 2 | `FiniteGeneratorReduction.lean:223` | `hmono_transitions : ∀ ⦃j j'⦄ (φ : j ⟶ j'), Mono (Y'.map φ)` — mono transitions for arbitrary filtered diagram | **FALSE in general** | **HIGH**: This is asserted for ALL filtered diagrams but is only true at the call site. The recursive IH call on the quotient diagram Q makes this sorry false (Q.map φ is epi, not mono, by the snake lemma). The sorry is "load-bearing false" — it's used at every induction level. |

**Worst-case scenario for sorry #2**: The sorry is provably FALSE at the recursive level. By the snake lemma, `ker(Q.map φ) ≅ coker(Y'.map φ) ≠ 0` when `Y'.map φ` is a proper mono. This means the induction "works" only because `sorry` accepts false statements. The mathematical theorem IS true (Ext preserves filtered colimits in Grothendieck abelian categories), but the current proof strategy (dimension shifting with a common injective) fundamentally cannot work without mono coprojections at every recursive level.

**Documentation lie**: The docstring at line 36 says "This is the SOLE sorry in the formalization." There are 2 sorry's. `CLAUDE.md` says "1 sorry remains" — also wrong.

## 2. Hidden Axioms

`#print axioms GrothendieckVanishing` reports: `[propext, sorryAx, Classical.choice, Quot.sound]`

- **`sorryAx`**: present due to the sorry's. This is the critical issue.
- `propext`, `Classical.choice`, `Quot.sound`: standard Lean axioms, acceptable.
- No `admit`, `axiom`, `native_decide` found. Clean on that front.

## 3. Circularity

- `gabriel_injective_of_filtered_colimit` (sorry #1) is DEAD CODE — defined at line 37 but never referenced anywhere. It's not used by `sheafH_filtered_colimit_aux` or any other declaration. It appears to be a "planned" approach that was never connected.
- The `hmono_transitions` sorry at line 223 is genuinely circular in the recursion: the IH at degree n requires the same sorry for the quotient diagram Q, where the statement is false. The proof "terminates" only because sorry accepts anything.
- No hypothesis-conclusion circularity in the main theorem itself.

## 4. Hypothesis Audit

**Main theorem** `GrothendieckVanishing`:
```
(X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
[NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X)
```

- `NoetherianSpace X`: necessary and standard.
- `n > topologicalKrullDim X`: necessary, matches Hartshorne.
- `AddCommGrpCat.{u}`: could potentially be generalized to other coefficient categories (e.g., `ModuleCat R`), but this matches Hartshorne's statement.
- Universe `u`: all universes are `u`, which is the right choice.
- No unnecessary hypotheses detected at the top level.

## 5. Mathematical Correctness

- The overall proof structure (induction on Krull dimension, closed-open decomposition, irreducible step) is correct and follows Hartshorne III.2.7.
- **The sorry gap is mathematically real**: the dimension-shifting proof cannot handle non-mono coprojections. Alternative approaches (Čech cohomology, universal δ-functor, Gabriel's theorem) are mathematically valid but require infrastructure not yet in Mathlib.
- The `gabriel_injective_of_filtered_colimit` theorem is correctly stated but appears to be part of an incomplete alternative approach.

## 6. Code Quality

- **No `maxHeartbeats` overrides**: clean.
- **No linter suppressions**: clean.
- **File sizes**: largest is `IrreducibleStep.lean` at 589 lines, all under 600. Acceptable.
- **Dead code**: `gabriel_injective_of_filtered_colimit` (line 37-43) is defined but never used. Should be deleted or connected to the proof.
- **Stale aristotle-in files**: `sheafH_colim.lean` doesn't compile (errors with `constantSheaf` calling convention). Should be cleaned up.

## 7. Documentation Lies

| Claim | Location | Reality |
|-------|----------|---------|
| "1 sorry remains" | `CLAUDE.md:76` | **2 sorry's** (gabriel + hmono_transitions) |
| "This is the SOLE sorry" | `FiniteGeneratorReduction.lean:36` | False — there are 2 |
| "1 sorry in FiniteGeneratorReduction.lean: hmono_transitions" | `main.lean:7` | Misses gabriel_injective_of_filtered_colimit |
| "The IH call on Q is clean (no mono needed)" | `main.lean:11` | **Misleading**: the IH call on Q re-introduces the same (false) sorry at each level |

## 8. Generalization Opportunities

1. **Coefficient category** (feasibility: medium): Generalize from `AddCommGrpCat` to `ModuleCat R` or any Grothendieck abelian category. The proof structure would be the same; the main work is ensuring Mathlib instances exist.

2. **Drop NoetherianSpace** (feasibility: hard): Grothendieck vanishing holds for paracompact spaces of finite covering dimension with soft sheaves. This would require entirely different proof methods.

3. **Effective bounds** (feasibility: easy): The current theorem gives `Subsingleton` (existence of at most one element). Could strengthen to `IsZero (Sheaf.H F n)` or provide an explicit isomorphism `Sheaf.H F n ≅ 0`.

4. **Higher direct images** (feasibility: medium): Extend to `R^n f_* F = 0` for `f : X → Y` with fibers of dimension < n. This is Grothendieck's theorem in the relative setting.

## 9. Mathlib Upstreamability

1. **`PresheafFilteredColimit.lean`** (494 lines): The theorem that presheaf colimits are sheaves on Noetherian spaces (`isSheaf_presheaf_filtered_colimit`, `createsFilteredColimit`) is fully proved and of independent interest. Could be PR'd to Mathlib under `Mathlib.Topology.Sheaves.FilteredColimit` or similar.

2. **`FlasqueVanishing.lean` / `FlasqueCohomology.lean`**: Flasque sheaf theory and cohomological vanishing for flasque sheaves. These are standard results that Mathlib currently lacks.

3. **`ConstantSheafFlasque.lean`**: The constant sheaf on an irreducible space is flasque. Clean, self-contained, upstream-ready.

4. **`gabriel_injective_of_filtered_colimit`**: IF proved, this would be a valuable Mathlib contribution. Currently it's just a sorry.

---

## Open Issues (must fix)

- ~~**P0-1**: Close or remove `gabriel_injective_of_filtered_colimit` sorry~~ DONE (deleted in c2543f6)
- **P0-2**: Close `hmono_transitions` sorry (the REAL gap — requires a fundamentally different proof approach)
- **P1-1**: Fix blueprint deployment (404 on both URLs)
- ~~**P1-2**: Fix all documentation lies~~ DONE (fixed in c2543f6)
- ~~**P2-1**: Delete stale `aristotle-in/sheafH_colim.lean`~~ DONE (was untracked)
- ~~**P2-2**: Remove dead code `gabriel_injective_of_filtered_colimit`~~ DONE (deleted in c2543f6)

**Verdict: REVISE** — 1 sorry remains (`hmono_transitions`). The dimension-shifting proof is fundamentally blocked at recursive levels. Aristotle job `6ecc7b79` is in progress.
