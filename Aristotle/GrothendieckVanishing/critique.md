# Critique — Grothendieck Vanishing Formalization
**Date**: 2026-03-27T18:45:00Z
**Verdict**: REVISE

---

## 0. CI Status

- `lake build`: passes locally (all 7 files).
- CI on branch `grothendieck-vanishing`: last 2 runs PASSED.
- **Blueprint**: `https://vilin97.github.io/aristotle/blueprint/` returns **HTTP 404**. The blueprint is broken or not configured for this project. **P1** — if this project is meant to have a blueprint, it must be fixed. If not, remove any references.
- No new CI run has been triggered since the GrothendieckVanishing files were created — the code on GitHub is stale vs. local. Not a build failure, but a discrepancy.

## 1. Sorry's

Three `admit` calls in the codebase:

| File | Line | Theorem | Assessment |
|------|------|---------|------------|
| `Setup.lean` | 38 | `FlasqueVanishing` | Intentional axiom. Statement is mathematically correct (Hartshorne Prop 2.5). **Acceptable.** |
| `ClosedOpenDecomposition.lean` | 39 | `grothendieck_vanishing_of_irreducible` | **HIGH RISK.** This is Hartshorne Step 1. The statement requires infrastructure not in Mathlib (extension by zero, Lemma 2.10). The statement itself is plausible but the callback signature (`ih_irred` with `dim Y ≤ dim X`) may be too weak — in Hartshorne's proof, the closure of X \ Y₁ is NOT an irreducible space but a general Noetherian space with fewer components. The callback only provides vanishing for *irreducible* Y, not general Y. This means the sorry'd proof must also handle the INNER induction on irreducible components, not just pass it to the caller. This is a design concern — the sorry might be unfillable as stated if the inner induction requires the callback to also provide vanishing for non-irreducible spaces. |
| `IrreducibleStep.lean` | 41 | `grothendieck_vanishing_irreducible_pos` | **VERY HIGH RISK.** This bundles Steps 3–5 of Hartshorne: Prop 2.9 (direct limits), subsheaf reduction, Z_U → Z → Z_Y SES, and FlasqueVanishing for constant sheaf. Each of these steps requires substantial infrastructure not in Mathlib. Prop 2.9 alone is a major theorem. The constant sheaf being flasque on irreducible spaces also needs proof. This sorry carries 80%+ of the mathematical content. |

**Assessment**: The formalization proves ~10% of the actual mathematical content. The well-founded induction skeleton and the dim 0 base case are proved, but the two hard steps (reduction to irreducible + irreducible positive dim) are fully sorry'd. Calling this "proved modulo sorry's" is technically accurate but misleading about progress.

## 2. Hidden Axioms

- `lean_verify` on `GrothendieckVanishing`: `[propext, sorryAx, Classical.choice, Quot.sound]`
- `lean_verify` on `grothendieck_vanishing_dim_zero`: `[propext, sorryAx, Classical.choice, Quot.sound]`
- `lean_verify` on `opens_eq_bot_or_top_of_irreducibleSpace_dim_zero`: `[propext, Classical.choice, Quot.sound]` — **clean**, no sorry.

The `sorryAx` in `grothendieck_vanishing_dim_zero` is inherited from `FlasqueVanishing` (admitted). This is expected but means even the "proved" dim 0 case depends on an admitted axiom.

The only truly sorry-free results are in `Auxiliary.lean`.

## 3. Circularity

I found no circularity in the dependency chain. The well-founded induction is structurally sound:
- `grothendieck_vanishing_aux` calls `grothendieck_vanishing_of_irreducible` (sorry), then dispatches dim ≤ 0 and dim > 0 cases.
- The dim > 0 case calls `grothendieck_vanishing_irreducible_pos` (sorry) with a callback that invokes the wf IH at strictly smaller dimension.

However: **the callback in `grothendieck_vanishing_of_irreducible` provides vanishing only for irreducible Y**. In Hartshorne's proof, the closure Ū = cl(X \ Y₁) is in general NOT irreducible — it's a union of the remaining irreducible components. The proof needs vanishing for Ū (a non-irreducible space) to proceed. This is handled by an inner induction on the number of components, but that inner induction needs the callback to also cover non-irreducible spaces. **The current `ih_irred` signature may be insufficient for the intended proof.**

## 4. Hypothesis Audit

**`GrothendieckVanishing`:**
| Hypothesis | Necessary? | Could weaken? |
|---|---|---|
| `X : TopCat.{u}` | Yes | Could use `Type*` with `[TopologicalSpace X]` instead of bundled `TopCat` |
| `F : TopCat.Sheaf AddCommGrpCat.{u} X` | Yes | Universe-polymorphic would be more general |
| `[NoetherianSpace X]` | Yes | Cannot weaken — used in the induction and in sorry'd lemmas |
| `n : ℕ` | Yes | — |
| `h : n > topologicalKrullDim X` | Yes | — |

**`FlasqueVanishing`:**
| Hypothesis | Necessary? | Could weaken? |
|---|---|---|
| `[NoetherianSpace X]` is **not** in the signature | N/A | But it IS passed implicitly via `TopCat.Sheaf`. This is fine. |
| The flasque condition `∀ {U V} (i : U ⟶ V), Epi (F.val.map i.op)` | Correct | Standard definition. |

**`sheaf_restriction_epi_of_irreducible_dim_zero`:**
- Does NOT require `[NoetherianSpace X]`. This is good — the result is purely about the topology, not about Noetherian properties.

## 5. Mathematical Correctness

- **Dim 0 case is correct**: On an irreducible space of dim 0, every point is dense ⟹ only opens are ∅ and X ⟹ every sheaf is flasque. This is Hartshorne's Step 2 and the proof is clean.

- **The `topologicalKrullDim_nonneg_of_irreducible` lemma is correct**: an irreducible space has at least one irreducible closed subset (itself), so dim ≥ 0.

- **Potential issue with empty spaces**: If X is empty, `topologicalKrullDim X = ⊥`. The hypothesis `n > ⊥` holds for all n. But `Sheaf.H F n` should be trivially subsingleton for an empty space. The proof handles this: `grothendieck_vanishing_of_irreducible` is applied, and its sorry'd proof must handle the empty case. But does it? If X is empty, there are no irreducible spaces Y to reduce to, so the callback is vacuously satisfied. The sorry'd proof needs to directly handle empty X. This could be a gap.

- **Divergence from Hartshorne**: Hartshorne proves the theorem by induction on dim X, with an inner induction on the number of irreducible components. The formalization does the outer induction on dim correctly but pushes the inner induction entirely into the sorry'd `grothendieck_vanishing_of_irreducible`. This is a valid decomposition but puts enormous load on a single sorry.

## 6. Code Quality

- **No `maxHeartbeats` overrides**: clean.
- **No linter disabling**: clean.
- **File sizes**: all under 80 lines, good modularity.
- **`import Mathlib`** in `Auxiliary.lean` and `Setup.lean`: this is a coarse import. Better practice is to import specific Mathlib modules. Not a correctness issue but poor style for eventual upstreaming.
- **`isTerminal_sheaf_bot` is a `def` not a `theorem`**: it returns data (`IsTerminal`), which is fine, but the name follows `theorem` convention (snake_case predicate). Minor.
- **Aristotle-in files duplicate Setup.lean instances**: `aristotle-in/ClosedOpenDecomposition.lean` and `aristotle-in/IrreducibleStep.lean` both copy the `HasSeparator`, `IsGrothendieckAbelian`, `Abelian`, instances. This is necessary for standalone submission but creates maintenance burden. Not blocking.

## 7. Documentation Lies

- `main.lean` line 13: "GrothendieckVanishing.lean: PROVED (modulo sorry's)". The word "PROVED" is misleading. The main theorem depends on `sorryAx`. It should say "STRUCTURED (modulo sorry's)" or "ASSEMBLED (modulo sorry's)".
- `DimZeroVanishing.lean` docstring says "all higher cohomology vanishes". Technically correct but only for the admitted `FlasqueVanishing`. The file's own contribution is that all sheaves have epi restriction maps; the vanishing itself is from the axiom.
- `aristotle-jobs.json` shows `"jobs": [], "completed": []` — the Aristotle submissions are not tracked here. The two jobs submitted (`fca6885d` and `bc3176de`) are not recorded.

## 8. Generalization Opportunities

1. **Drop `TopCat` bundling**: The theorem could be stated for `(X : Type*) [TopologicalSpace X]` instead of `X : TopCat`. This would be more general and more natural for users who don't work with `TopCat`. The current formulation forces users to bundle their spaces. **Feasibility: medium** — requires changing all signatures.

2. **Universe polymorphism**: Currently everything is at universe `u`. The sheaf category `TopCat.Sheaf AddCommGrpCat.{u} X` forces the sheaf values to live in the same universe as the space. A more general formulation would allow `AddCommGrpCat.{v}` for a separate universe `v`. **Feasibility: low** — Mathlib's sheaf cohomology API has specific universe constraints.

3. **Generalize from `AddCommGrpCat` to arbitrary Grothendieck abelian categories**: The theorem holds for any abelian category satisfying AB5. The current formalization is specific to `AddCommGrpCat`. **Feasibility: very low** — would require reworking the entire approach; Mathlib's `Sheaf.H` is specific to `AddCommGrpCat`.

4. **Weaken `NoetherianSpace` to `CompactSpace` + finite-dimensional**: For some applications, the Noetherian hypothesis could be weakened. But this changes the mathematical content significantly. **Feasibility: not applicable** — different theorem.

5. **Extract the dim 0 irreducible opens characterization**: `opens_eq_bot_or_top_of_irreducibleSpace_dim_zero` is a clean, sorry-free result about irreducible spaces of dimension 0. This could be upstreamed to Mathlib independently. **Feasibility: high**.

## 9. Mathlib Upstreamability

1. **`epi_of_isTerminal_tgt`** (Auxiliary.lean:18): "In an abelian category, any morphism to a terminal object is epi." This is a basic fact. Could be PR'd. Needs: rename to follow Mathlib conventions (`Abelian.epi_of_isTerminal` or similar), add `@[simp]` or appropriate attributes.

2. **`isTerminal_sheaf_bot`** (Auxiliary.lean:33): "F(⊥) is terminal for any sheaf." This may already exist in Mathlib in some form via `Sheaf.isTerminalOfBotCover`. The wrapper is thin enough that it might not be worth upstreaming as-is, but the pattern is useful.

3. **`opens_eq_bot_or_top_of_irreducibleSpace_dim_zero`** (Auxiliary.lean:61): Clean characterization of opens on irreducible dim-0 spaces. Good candidate. Needs: generalize the name, possibly merge with existing `IrreducibleSpace` API in Mathlib.

4. **`topologicalKrullDim_nonneg_of_irreducible`** (GrothendieckVanishing.lean:22): `dim X ≥ 0` for irreducible X. Simple and useful. Good candidate.

5. **The `HasSeparator AddCommGrpCat` instance** (Setup.lean:13): If this isn't already in Mathlib, it should be. The proof is clever (using `ULift ℤ` as separator).

---

## Open Issues (Ordered by Priority)

| # | Priority | Issue | File |
|---|----------|-------|------|
| 1 | **P0** | `grothendieck_vanishing_of_irreducible` callback may be too weak — only provides vanishing for irreducible Y, but Hartshorne's inner induction needs vanishing for non-irreducible closures | `ClosedOpenDecomposition.lean` |
| 2 | **P0** | `grothendieck_vanishing_irreducible_pos` carries 80%+ of the math content as a single sorry | `IrreducibleStep.lean` |
| 3 | **P1** | Blueprint returns 404 | CI/deployment |
| 4 | **P1** | Aristotle jobs not tracked in `aristotle-jobs.json` | project tracking |
| 5 | **P1** | Empty space case: `grothendieck_vanishing_of_irreducible` must handle empty X where no irreducible Y exists | `ClosedOpenDecomposition.lean` |
| 6 | **P2** | `import Mathlib` is coarse; should import specific modules | `Auxiliary.lean`, `Setup.lean` |
| 7 | **P2** | `main.lean` says "PROVED" which is misleading given sorry dependency | `main.lean` |
| 8 | **P3** | `topologicalKrullDim_nonneg_of_irreducible` should be in `Auxiliary.lean`, not `GrothendieckVanishing.lean` | code organization |
| 9 | **P3** | Consider unbundling `TopCat` for more natural API | all files |

## Verdict: REVISE

The formalization has a clean skeleton with correct well-founded induction and a nicely proved dim 0 base case. However:

1. Two sorry's carry essentially all the mathematical content (P0).
2. The `grothendieck_vanishing_of_irreducible` callback signature may be incorrect — it must be verified that the sorry is actually fillable with only irreducible-space vanishing in the callback (P0).
3. The blueprint is broken (P1).

**Conditions for CONDITIONAL ACCEPT**: Fix P0 issues (verify callback correctness or fix it), track Aristotle jobs, and make progress on at least one of the two sorry's. The dim 0 case alone is insufficient mathematical content for acceptance.
