# Adversarial Critique -- Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-03T21:15Z
**Reviewer**: Hostile referee (default: REJECT)

---

## 0. CI Status

**Latest CI run**: PASSING (run 23948214266, commit from `prove: close sorry at line 180`). The previous run (23940023096) FAILED due to a build error in the `refactor: extract SheafHom.lean` commit. The run before that (23946993561) was green.

**Local build**: Not independently verified during this review (would require a full `lake build` on HPC).

**Docs (P1 -- BROKEN)**:
- `curl -Is https://vilin97.github.io/aristotle/blueprint/ | head -n 1` returns **HTTP 404**.
- `curl -Is https://vilin97.github.io/aristotle/blueprint/dep_graph_document.html | head -n 1` returns **HTTP 404**.
- The deploy workflow only triggers on pushes to `main`. The working branch `wip/grothendieck-vanishing` never deploys docs. This means there is **no publicly accessible documentation** for the formalization in its current state. The README presumably links to a 404. This is a P1 issue: a formalization that cannot be inspected by the public is not a finished product.

**Verdict on CI**: The build passes, but the documentation infrastructure is non-functional. One CI run ago it was broken. Fragile.

---

## 1. Sorry's

There are exactly **2 sorry's** in the proof term (not in comments):

| # | File | Line | Declaration | Statement |
|---|------|------|------------|-----------|
| 1 | `SheafHom.lean` | 63 | `isSheaf_filtered_colimit_of_sheaves` | Filtered presheaf colimits of sheaves are sheaves on a Noetherian space |
| 2 | `FiniteGeneratorReduction.lean` | 198 | `hQprov` (local `have` inside `ext_vanishing_of_colimit_aux`) | `∀ n'' ip' j, Subsingleton (Ext Z (cokernel (Qcocone.ι.app j ≫ ip'.shortComplex.f)) n'')` |

**Assessment of sorry #1 (`isSheaf_filtered_colimit_of_sheaves`)**: This is mathematically true -- it is the AB5 property for sheaves on a Noetherian space. On a Noetherian space, every cover has a finite subcover, so the sheaf condition is a finite limit; filtered colimits commute with finite limits in AB5 categories (and `AddCommGrpCat` is AB5). However, the Mathlib API does not appear to directly expose this fact in the form needed. The statement has been sitting in `aristotle-in/` since 2026-04-03 without being submitted (Aristotle API unreachable from HPC). This sorry is **blocking but not mathematically dangerous**: the statement is standard.

**Assessment of sorry #2 (`hQprov`)**: This is the harder sorry. The proof attempts to establish Ext vanishing for quotients of quotients in a recursive call, but the Q-diagram's transition maps are **not mono** (the comments at lines 189-195 acknowledge this explicitly). This means the inductive scheme used in `ext_vanishing_of_colimit_aux` is structurally broken at the recursive step: the code constructs a quotient functor `Qfun` whose transitions are `cokernel.map`, but `cokernel.map` preserves neither monomorphicity nor epimorphicity in general. The approach diverges from Hartshorne's proof, which uses per-object injective resolutions rather than a single global injective presentation. The comments identify two fix strategies (strengthen `hHom_univ` to `PreservesFilteredColimits`, or restructure to per-Y_j presentations), but neither has been implemented.

**Worst-case scenario**: Sorry #2 could hide a genuine proof gap if the `ext_vanishing_of_colimit_aux` theorem as stated requires hypotheses that are not actually satisfiable in the recursive call. The `hQprov` parameter asks for vanishing at *all* injective presentations `ip'` of `Qcocone.pt` and *all* indices `j`, which is extremely strong. However, the statement itself is mathematically true (it follows from the full AB5 property + Hartshorne 2.9), so the sorry does not hide a false claim -- only a proof-engineering failure.

**The main theorem `GrothendieckVanishing` depends on `sorryAx`** (confirmed via `#print axioms`). This formalization is INCOMPLETE.

---

## 2. Hidden Axioms

- No `admit`, `native_decide`, `Decidable.decide`, `set_option linter.all false`, or custom `axiom` declarations found in any `.lean` file under `Aristotle/GrothendieckVanishing/`.
- `#print axioms GrothendieckVanishing` returns: `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`.
- The first three (minus `sorryAx`) are standard Lean 4 axioms. `sorryAx` is the problem.
- `lean_verify` on `IrreduciblePosVanishing` returns empty axioms (no `sorryAx`), confirming the sorry contamination flows through the `FiniteGeneratorReduction.lean` path, not through the irreducible step assembly itself.

**I found no hidden axioms beyond the acknowledged sorry's.**

---

## 3. Circularity

The proof proceeds by well-founded induction on `topologicalKrullDim X` (type `WithBot ENatInfty`), using `IsWellFounded.wf`. The induction hypothesis is:

```
ih : ∀ d' < d, ∀ (X : TopCat) [NoetherianSpace X] (n : ℕ) (F : Sheaf X),
     topologicalKrullDim X = d' → n > d' → Subsingleton (Sheaf.H F n)
```

The dependency chain is:
1. `GrothendieckVanishing` calls `grothendieck_vanishing_aux` via WF induction
2. `grothendieck_vanishing_aux` calls `grothendieck_vanishing_of_irreducible` (reducible case) and either `grothendieck_vanishing_dim_zero` (dim 0) or `IrreduciblePosVanishing` (dim >= 1)
3. `IrreduciblePosVanishing` calls `irreduciblePos_kernel_subsingleton` which calls `directLimit_cohomology_vanishing`
4. `directLimit_cohomology_vanishing` calls `cohomology_vanishing_of_finitelyGenerated_vanishing` which calls `ext_comm_filtered_colimit_mono`
5. `ext_comm_filtered_colimit_mono` calls `ext_vanishing_of_colimit_aux` (contains sorry)

No hypothesis is equivalent to the conclusion. The IH is invoked only on spaces `Y` with `topologicalKrullDim Y < topologicalKrullDim X`, which is structurally correct for well-founded induction. The `ReducibleVanishing` path decomposes into irreducible components via `Finset.induction`, each of which has `topologicalKrullDim Y ≤ topologicalKrullDim X`, and the IH is invoked at the same `n` but on irreducible subspaces (not at a larger `n`).

**I found no circularity.**

---

## 4. Hypothesis Audit

The main theorem signature:

```lean
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

**Hypotheses:**

1. **`X : TopCat.{u}`** -- Correct. Hartshorne states the theorem for topological spaces. `TopCat.{u}` is the bundled category of topological spaces in universe `u`.

2. **`F : TopCat.Sheaf AddCommGrpCat.{u} X`** -- Correct. Hartshorne states it for sheaves of abelian groups. `AddCommGrpCat` is the category of abelian groups.

3. **`[NoetherianSpace X]`** -- Correct. This is the exact hypothesis in Hartshorne III.2.7.

4. **`(n : ℕ)`** -- Minor issue: `n` is a natural number, but the comparison `n > topologicalKrullDim X` coerces `n` to `WithBot ENatInfty`. This is fine for finite-dimensional spaces, but note that if `topologicalKrullDim X = ⊤` (infinite dimension), then `n > ⊤` is `False`, so the theorem is vacuously true. This is correct behavior -- Hartshorne's theorem says "for all i > n" where n is the finite dimension. If the dimension is infinite, there is nothing to prove.

5. **`h : n > topologicalKrullDim X`** -- Correct strict inequality.

6. **Conclusion `Subsingleton (Sheaf.H F n)`** -- This encodes `H^n(X, F) = 0` as "the cohomology group is a subsingleton (has at most one element)." For abelian groups, subsingleton is equivalent to being the zero group. This is the correct encoding.

**Missing hypothesis check**: Hartshorne does NOT require `X` to be sober or to have a structure sheaf. The topological Krull dimension (supremum of lengths of chains of irreducible closed subsets) is purely topological. The formalization correctly avoids scheme-theoretic hypotheses.

**Could hypotheses be weakened?** The `NoetherianSpace` hypothesis is necessary -- without it, the theorem fails (e.g., infinite-dimensional spaces have non-vanishing cohomology in arbitrarily high degree). The theorem is already stated at maximum generality for abelian sheaves on Noetherian spaces.

**I found no issue with the hypotheses.** They match Hartshorne exactly.

---

## 5. Mathematical Correctness

The proof follows Hartshorne III.2.7 closely:

- **Step 1 (Dimension cascade)**: `sheafH_vanishing_cascade` -- once vanishing holds at degree `m_0`, it holds at all higher degrees via dimension shifting with injective presentations. Correct.

- **Step 2 (Irreducible dim 0)**: `grothendieck_vanishing_dim_zero` -- on an irreducible space of dimension 0, the only opens are empty set and the whole space, so every sheaf is flasque. Correct.

- **Step 3 (Reducible case)**: `ReducibleVanishing'` via `Finset.induction` on irreducible components, using closed immersion SES. Correct.

- **Step 4 (Irreducible, dim >= 1)**: `IrreduciblePosVanishing` -- closed immersion SES on a proper closed subset `Z` of strictly smaller dimension, push-forward vanishing by IH, kernel vanishing by the colimit argument. Correct in structure.

- **Step 5 (Colimit step)**: `directLimit_cohomology_vanishing` -- write any sheaf as a filtered colimit of finitely generated subsheaves, prove vanishing for each, transfer to the colimit. This follows Hartshorne's Lemma 2.9. **This is where the sorry's live.**

**Divergence from Hartshorne**: The formalization uses a single global injective presentation of the colimit object `c.pt` (line 100 of `FiniteGeneratorReduction.lean`), then forms the quotient functor `j ↦ cokernel(c.ι.app j ≫ ι)`. Hartshorne's proof instead uses individual injective resolutions. This divergence is the root cause of sorry #2: the quotient transitions `cokernel.map` are not mono in general, breaking the inductive structure. The code acknowledges this explicitly at lines 189-195. This is a real mathematical architecture problem, not just a Lean API gap.

**Other correctness concerns**: The `exists_section_generating_stalks` proof (the "Noetherian shrinking" step) uses `Nat.find` to select a point `x_0` with minimal image subgroup generator. This is correct -- it relies on the fact that subgroups of `Z` are cyclic (hence determined by a positive generator), and the Noetherian property ensures the stalks are finitely generated. The proof that the generator is constant on a neighborhood is done by germ comparison, which is sound.

---

## 6. Code Quality

**File sizes exceeding 600 lines:**

| File | Lines | Issue |
|------|-------|-------|
| `ZeroOutside.lean` | 733 | Extension-by-zero machinery. Contains both presheaf and sheaf constructions. Should be split. |
| `SheafStalkAlgebra.lean` | 688 | Stalk algebra + 7 distinct theorem clusters. Should be split into 2-3 files. |
| `FlasqueVanishing.lean` | 616 | Flasque sheaf theory. Borderline but acceptable since it contains a coherent proof thread. |
| `IrreducibleStep.lean` | 595 | Just under threshold after deduplication. Acceptable. |
| `FiniteGeneratorReduction.lean` | 527 | Acceptable. |

**`maxHeartbeats` overrides**: NONE. This is commendable -- the CLAUDE.md discipline of 200000 is enforced.

**`set_option linter.all false`**: NONE.

**`import Mathlib`**: Two files (`ZeroOutside.lean`, `FlasqueVanishing.lean`, `Auxiliary.lean`) use bare `import Mathlib` rather than granular imports. This is bad practice: it imports the entire Mathlib (~4M LOC) and makes compilation slower and more fragile against Mathlib API changes. `ClosedImmersion.lean` has granular imports -- this should be the standard.

**Dead code / stale comments**: `main.lean` line 11 says `hQprov (FiniteGeneratorReduction.lean:180,188)` but the sorry is at line 198. The old line references are stale from before the n=0 case was proved. Similarly, CLAUDE.md line 78 says `(FiniteGeneratorReduction.lean:180,188)` -- also stale.

---

## 7. Documentation Lies

| Claim | Source | Reality | Discrepancy? |
|-------|--------|---------|--------------|
| "2 sorry's remain" | CLAUDE.md, plan.md, main.lean | 2 sorry proof terms (`SheafHom.lean:63`, `FiniteGeneratorReduction.lean:198`) | **Count correct** |
| "hQprov at line 180,188" | CLAUDE.md line 78, main.lean line 11 | Sorry is at line 198. Lines 180-182 are now proved code. | **STALE LINE NUMBERS** |
| "ext_vanishing_of_colimit_aux (FiniteGeneratorReduction.lean:180,188)" | CLAUDE.md line 78 | The sorry is inside `ext_vanishing_of_colimit_aux` but at line 198, not 180/188. | **WRONG** |
| "ext_comm_filtered_colimit_mono ... 1 sorry" | main.lean line 25 | `ext_comm_filtered_colimit_mono` is sorry-free. The sorry is in `ext_vanishing_of_colimit_aux`. | **MISLEADING** -- the sorry is upstream |
| "hQprov (FiniteGeneratorReduction.lean:196)" | LOG.md line 5 | Actually at line 198 now | **WRONG LINE NUMBER** |
| "3 sorry's remain" at CLAUDE.md header | CLAUDE.md title comment | Says "2 sorry's remain" -- but initially was "3 sorry's remain" per commit history | **Potentially stale depending on edit timing** |
| "Setup.lean: Wrapper theorems (contains IrreduciblePosVanishing sorry)" | CLAUDE.md code structure tree | `Setup.lean` has NO sorry. `IrreduciblePosVanishing` is in `IrreducibleStep.lean`. | **WRONG file attribution** |
| Blueprint docs at vilin97.github.io | CLAUDE.md mentions "GitHub Pages" deployment | Both blueprint URLs return 404 | **BROKEN** |
| "~5300 lines total" | plan.md line 8 | `wc -l` gives 5318 lines total | **Close enough** |

**Summary**: Multiple stale line-number references across CLAUDE.md, main.lean, and LOG.md. The sorry count of 2 is accurate, but the locations are consistently wrong. The code structure tree in CLAUDE.md attributes `IrreduciblePosVanishing` sorry to `Setup.lean` when it lives in `IrreducibleStep.lean` and is sorry-free at the theorem level (the sorry is deeper in `FiniteGeneratorReduction.lean`).

---

## 8. Generalization Opportunities

### 8.1 Weaken the coefficient category (Feasibility: MEDIUM)

The theorem is stated for `AddCommGrpCat.{u}` (abelian groups). Grothendieck's vanishing theorem holds more generally for any Grothendieck abelian category `A` as coefficient category, not just abelian groups. The formalization already has `IsGrothendieckAbelian` instances. Generalizing the main theorem from `AddCommGrpCat` to an arbitrary `A` with `[IsGrothendieckAbelian A]` would be a significant strengthening. The main obstacle is the `HasSeparator` instance (currently hard-coded for `AddCommGrpCat` via `ULift Z`).

### 8.2 Drop `NoetherianSpace` to `finite cohomological dimension` (Feasibility: LOW)

The Noetherian hypothesis is used in two ways: (1) every open cover has a finite subcover (for AB5/sheaf condition), and (2) the Krull dimension is well-behaved (well-founded induction on chains of irreducible closeds). A more general version would assume `cd(X) < ∞` (finite cohomological dimension) directly, but this would require a completely different proof architecture.

### 8.3 Strengthen the conclusion to an isomorphism (Feasibility: MEDIUM)

The conclusion `Subsingleton (Sheaf.H F n)` says the cohomology group is zero. A stronger statement would provide an explicit isomorphism `Sheaf.H F n ≅ 0` in `AddCommGrpCat`, which would be more composable in downstream proofs. Currently, downstream code must use `Subsingleton.elim` to derive equalities, rather than functorial zeroing.

### 8.4 Universe polymorphism (Feasibility: LOW-MEDIUM)

The theorem is stated in a single universe `u`. Mathlib's `Sheaf.H` supports multi-universe setups (`w'`, `w`, `v`, `u`). A universe-polymorphic version would be more reusable.

### 8.5 Remove the cascade (Feasibility: HIGH)

`sheafH_vanishing_cascade` is redundant: the main theorem already proves vanishing at all `n > dim X` by WF induction. The cascade was historically needed when the colimit step only worked at a single degree, but now it is dead code -- `GrothendieckVanishing` never calls it. It should be removed or clearly marked as a bonus lemma.

---

## 9. Mathlib Upstreamability

### 9.1 `FlasqueVanishing` and flasque sheaf infrastructure (HIGH priority)

`IsFlasqueSheaf`, `epi_app_of_shortExact_flasque`, `isFlasque_X₃_of_shortExact`, `isFlasque_of_injective`, and `FlasqueVanishing` are self-contained, general-purpose theorems about sheaves on topological spaces. These are adapted from Brian Nugent's Mathlib PR #35790. They should be upstreamed. To make them acceptable:
- Remove the hard-coded `AddCommGrpCat` and generalize to any abelian category with enough injectives
- Use Mathlib naming conventions (`Sheaf.isFlasque` instead of `IsFlasqueSheaf`)
- Add proper docstrings with `@[simp]` lemmas where appropriate

### 9.2 `sheafH_dimension_shift_ses` and `subsingleton_sheafH_of_shortExact_middle` (MEDIUM priority)

These LES-based vanishing transfer lemmas are standard homological algebra and should be in Mathlib's `SheafCohomology` module.

### 9.3 `PushforwardHVanishing` (MEDIUM priority)

The statement "pushforward along a closed immersion preserves cohomological vanishing" is a standard fact. The proof (by induction on degree, using flasque vanishing + LES) is clean and self-contained.

### 9.4 `cohomologyPresheafTopEquiv` in `CohomologyIso.lean` (HIGH priority)

This resolves a literal `TODO` in Mathlib's `SheafCohomology/Basic.lean` (line 29-30). It proves `H'(top, F, n) ≅ H(F, n)`. This should be upstreamed immediately.

### 9.5 `ulift_int_projective` (LOW priority)

`ULift Z` is projective in `AddCommGrpCat`. This is a basic fact that should be in Mathlib.

### 9.6 `epi_unit_of_closedImmersion` and `ClosedImmersionSES` (MEDIUM priority)

The adjunction unit for a closed immersion being epi, and the resulting short exact sequence, are standard facts in sheaf theory.

---

## Open Issues Summary

| # | Severity | Issue | Condition for resolution |
|---|----------|-------|-------------------------|
| 1 | **P0** | Main theorem depends on `sorryAx` (2 sorry's) | Close both sorry's |
| 2 | **P0** | Sorry #2 (`hQprov`) reflects a structural proof architecture problem, not just an API gap | Restructure `ext_vanishing_of_colimit_aux` to use per-object injective presentations (Hartshorne's approach) or prove `PreservesFilteredColimits` for coyoneda |
| 3 | **P1** | Documentation (blueprint, dep graph) returns HTTP 404 | Fix deployment or merge to main |
| 4 | **P2** | Stale line numbers in CLAUDE.md, main.lean, LOG.md | Update all references to line 198 |
| 5 | **P2** | CLAUDE.md code structure tree incorrectly attributes `IrreduciblePosVanishing sorry` to `Setup.lean` | Fix attribution |
| 6 | **P3** | `ZeroOutside.lean` (733 lines) and `SheafStalkAlgebra.lean` (688 lines) exceed 600-line guideline | Split into smaller files |
| 7 | **P3** | Three files use bare `import Mathlib` instead of granular imports | Replace with specific imports |
| 8 | **P3** | `sheafH_vanishing_cascade` appears to be dead code (never called by main theorem) | Remove or document as bonus |
| 9 | **P4** | `cohomologyPresheafTopEquiv` resolves a Mathlib TODO -- should be upstreamed | PR to Mathlib |

---

## Verdict: **REJECT**

The formalization is incomplete. The main theorem `GrothendieckVanishing` depends on `sorryAx`. There are 2 sorry's, and one of them (sorry #2, `hQprov`) reflects a genuine structural problem in the proof architecture: the quotient functor's transitions are not mono, breaking the inductive scheme. The code acknowledges this problem in comments but has not resolved it.

The sorry-free portions are impressive: flasque vanishing, pushforward vanishing, the reducible case, the irreducible dim-0 case, the closed-open decomposition, the stalk algebra, and the Noetherian shrinking step are all fully proved. The proof architecture for the colimit step (Hartshorne 2.9) is 90% complete. But "90% of a formal proof" is not a formal proof.

**Conditions for CONDITIONAL ACCEPT:**
1. Close sorry #1 (`isSheaf_filtered_colimit_of_sheaves`) -- this is a standard fact
2. Close sorry #2 (`hQprov`) by restructuring the colimit induction, OR prove it using `PreservesFilteredColimits` for coyoneda
3. Verify `#print axioms GrothendieckVanishing` returns only `propext`, `Classical.choice`, `Quot.sound`
4. Fix all stale line-number references in documentation
5. Fix or acknowledge the broken blueprint deployment
