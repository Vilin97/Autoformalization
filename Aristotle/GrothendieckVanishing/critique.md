# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-05T01:15Z
**Reviewer**: Hostile

---

## 0. CI Status

- **Build CI**: Last commit on `wip/grothendieck-vanishing` — 2 runs in progress, last completed run **PASSED**.
- **Blueprint**: `curl -Is https://vilin97.github.io/aristotle/blueprint/` returns **HTTP 404**. The `deploy.yml` workflow has never run on `grothendieck-vanishing` — it only triggers on `main`. The blueprint infrastructure was just added but is not deployed. **P1: Blueprint is not live.**
- **Dependency graph**: `curl -Is https://vilin97.github.io/aristotle/blueprint/dep_graph_document.html` returns **404**. Same root cause.
- The `deploy.yml` on this branch has been updated to trigger on `grothendieck-vanishing`, but the deploy job condition (`github.ref == 'refs/heads/grothendieck-vanishing'`) means it will only deploy when changes land on `grothendieck-vanishing` itself (not on `wip/grothendieck-vanishing`). This is by design (wip branch merges into protected branch), but **the blueprint will not go live until the next merge**.

## 1. Sorry's

**I found no issue.** 0 sorry's in proof terms across all 20 `.lean` files. The word "sorry" appears only in comments/docstrings referencing past state. `lean_verify` confirms clean axioms.

## 2. Hidden Axioms

`lean_verify GrothendieckVanishing` returns `axioms: [propext, Classical.choice, Quot.sound]` — the standard three. `lean_verify FlasqueVanishing` — same. No `admit`, `native_decide`, `axiom` keywords found. Clean.

## 3. Circularity

**I found no issue.** The main induction is well-founded on `WithBot ℕ∞` via `IsWellFounded.wf`. No hypothesis is equivalent to the conclusion. The induction hypothesis provides vanishing for strictly smaller Krull dimension, and the step uses only dimension shifting + the irreducible/reducible case split.

## 4. Hypothesis Audit

The main theorem:
```lean
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

- `X : TopCat.{u}` — necessary (domain)
- `F : TopCat.Sheaf AddCommGrpCat.{u} X` — necessary; but could generalize coefficient category (see §8)
- `[NoetherianSpace X]` — necessary (used for finite irreducible decomposition and filtered colimit sheaf property)
- `n : ℕ` — the degree is `ℕ` not `ℤ` which is correct since negative cohomology vanishes trivially
- `h : n > topologicalKrullDim X` — necessary; standard Hartshorne hypothesis

All hypotheses are necessary and standard. No issue.

## 5. Mathematical Correctness

**I found no issue.** The approach matches Hartshorne III.2.7 with one notable innovation: replacing Gabriel's theorem (filtered colimits of injectives are injective) with `isFlasque_filtered_colimit` (filtered colimits of flasque sheaves are flasque on Noetherian spaces). This is mathematically correct because injective ⟹ flasque, and the proof only needs vanishing cohomology of the colimit (not injectivity itself).

## 6. Code Quality

| Issue | Severity | Details |
|-------|----------|---------|
| **FiniteGeneratorReduction.lean: 624 lines** | P3 | Exceeds the 600-line soft limit in CLAUDE.md. Should be split. |
| **IrreducibleStep.lean: 588 lines** | P4 | Approaching the limit. |
| **3 blanket `import Mathlib` statements** | P3 | `FlasqueVanishing.lean`, `Auxiliary.lean`, `ZeroOutside.lean` all use `import Mathlib` instead of targeted imports. This slows compilation and hides actual dependencies. |
| **CohomologyIso.lean is dead code** | P3 | Not imported by any file in the project. Not imported by `main.lean`. Contains `cohomologyPresheafTopEquiv` which is defined but never referenced. The whole file appears to be vestigial. |
| **Stale Aristotle job tracking** | P4 | `aristotle-jobs.json` still has a completed job entry. Should be cleaned. |
| **closedIncl_counit_isIso: ~200 lines** | P4 | Single proof spanning ~200 lines in `ClosedImmersion.lean`. Could benefit from extraction of intermediate lemmas. |

## 7. Documentation Lies

| Claim | Source | Reality | Verdict |
|-------|--------|---------|---------|
| "Mathlib v4.24.0" | MEMORY.md | `lakefile.toml` says `v4.28.0` | **STALE** |
| "0 sorry's, 0 axioms, 0 admits" | CLAUDE.md, main.lean | Verified correct | OK |
| "File structure" in CLAUDE.md | CLAUDE.md | Lists `SheafStalkAlgebra.lean`, `StalkGeneratorAlgebra.lean`, `PresheafFilteredColimit.lean`, `ZeroOutsideFinset.lean` which are present | OK |
| Previous critique says "ACCEPT" | critique.md | Previous critique did not flag blueprint 404, blanket imports, dead code, or file size limits | **Too lenient** |

## 8. Generalization Opportunities

1. **Coefficient category generalization** (medium feasibility): The theorem is stated for `AddCommGrpCat` but should hold for any Grothendieck abelian category with enough injectives. The proof strategy (flasque sheaves, dimension shifting) works in this generality. Would require abstracting `IsFlasqueSheaf` and the constant sheaf arguments.

2. **Higher direct images** (medium): Extend to `R^n f_* F = 0` for a morphism `f : X → Y` with fibers of bounded dimension. The current proof machinery (dimension shifting, closed immersion SES) already supports the essential steps.

3. **`Subsingleton` → `IsZero`** (easy): The conclusion `Subsingleton (Sheaf.H F n)` could be strengthened to `IsZero (Sheaf.H F n)` which carries more categorical information. Since `Sheaf.H` lives in `AddCommGrpCat`, subsingleton implies zero, but `IsZero` is the standard categorical statement.

4. **Drop `NoetherianSpace` from `FlasqueVanishing`** (easy, already done): `FlasqueVanishing` doesn't actually need `NoetherianSpace` — it works for any topological space. Confirmed: the statement already has no `NoetherianSpace` hypothesis. But `isFlasque_filtered_colimit` does need it, and that's correct.

## 9. Mathlib Upstreamability

1. **`FlasqueVanishing` + `IsFlasqueSheaf`** — flasque sheaf cohomological vanishing. Brian Nugent's PR #35790 covers similar material. Could be contributed as a complement or merge.

2. **`isFlasque_filtered_colimit`** — filtered colimits of flasque sheaves are flasque on Noetherian spaces. Novel result not in Mathlib. Would need to be made non-private first.

3. **`PresheafFilteredColimit.lean`** — presheaf colimits are sheaves on Noetherian spaces + `createsFilteredColimit`. Useful for anyone working with sheaf cohomology on Noetherian spaces.

4. **`ConstantSheafFlasque.lean`** — constant sheaf on irreducible space is flasque. Standard result missing from Mathlib.

5. **Auxiliary topology lemmas** — `opens_eq_bot_or_top_of_irreducibleSpace_dim_zero`, `topologicalKrullDim_lt_of_isIrreducible_of_isClosed` are useful independently.

All would need: removal of `private` modifiers, targeted imports (no `import Mathlib`), and Mathlib-style docstrings.

---

## Open Issues

| Priority | Issue | Status |
|----------|-------|--------|
| P1 | Blueprint returns 404 (not deployed yet) | OPEN — will resolve on next merge to `grothendieck-vanishing` |
| P3 | `FiniteGeneratorReduction.lean` exceeds 600-line limit (624 lines) | OPEN |
| P3 | 3 files use blanket `import Mathlib` | OPEN |
| P3 | `CohomologyIso.lean` is dead code (not imported anywhere) | OPEN |
| P4 | MEMORY.md says Mathlib v4.24.0 but actual is v4.28.0 | OPEN |
| P4 | Stale `aristotle-jobs.json` entry | OPEN |
| P4 | Generalize coefficient category from `AddCommGrpCat` | Backlog |
| P4 | Strengthen `Subsingleton` to `IsZero` | Backlog |

**Verdict: CONDITIONAL ACCEPT** — Formalization is mathematically complete and correct (0 sorry's, 0 axioms), but has code quality issues (dead code, blanket imports, file size violation) and the blueprint is not yet deployed. Fix P1 and P3 issues for unconditional acceptance.
