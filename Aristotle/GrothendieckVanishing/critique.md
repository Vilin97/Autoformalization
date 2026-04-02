# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-04-02T22:35Z
**Reviewer verdict**: CONDITIONAL PASS

## 0. CI Status

Latest CI run (23925073144) is **in_progress** for the most recent commit. Previous two
runs are **green**.

**Docs Check (P1)**: Both `https://vilin97.github.io/aristotle/blueprint/` and
`https://vilin97.github.io/aristotle/blueprint/dep_graph_document.html` return **HTTP 404**.
Blueprint/docs are broken and not deployed.

No `admit`, `axiom`, `native_decide`, heartbeat overrides, or `set_option linter` found.

## 1. Sorry's (1)

**`FiniteGeneratorReduction.lean:95`**: `exact @Subsingleton.elim _ (by sorry) ca cb`

The sorry provides `Subsingleton (Abelian.Ext Z ip.shortComplex.X₃ n)` — vanishing
of Ext^n on the cokernel Q = I/c.pt of an injective embedding.

**Is the statement true?** Yes. This is Hartshorne III Lemma 2.9 (filtered colimit
commutes with cohomology). Mathematically uncontroversial.

**Could Aristotle prove the negation?** No. The statement is true, and a counterexample
would require producing a non-zero Ext^n element on a filtered colimit where all pieces
have zero Ext^n. No such object exists in a Grothendieck abelian category.

**Worst case**: The sorry propagates through `ext_comm_filtered_colimit_mono` →
`cohomology_vanishing_of_finitelyGenerated_vanishing` → `directLimit_cohomology_vanishing`
→ `irreduciblePos_kernel_subsingleton` → `IrreduciblePosVanishing` →
`grothendieck_vanishing_aux` → `GrothendieckVanishing`. The main theorem depends on it.

**What's proved around the sorry**: The dimension shift via `InjectivePresentation` +
`Ext.covariant_sequence_exact₁` + `Ext.eq_zero_of_injective` is fully proved. The sorry
is precisely isolated: `Subsingleton (Ext Z Q n)` where Q is the cokernel.

## 2. Hidden Axioms

`lean_verify` on `GrothendieckVanishing`, `sheafH_vanishing_cascade`, and
`ext_comm_filtered_colimit_mono` reports **no axioms** beyond the standard Lean kernel
axioms (propext, Classical.choice, Quot.sound). No `admit`, `native_decide`, or unsafe
`Decidable.decide`. I found no issue beyond the sorry itself.

## 3. Circularity

The main theorem `GrothendieckVanishing` uses well-founded induction on
`topologicalKrullDim X`. The IH provides vanishing for strictly lower-dimensional spaces.
There is no self-reference: the sorry is in `ext_comm_filtered_colimit_mono` which is a
separate (non-recursive) theorem about abstract Grothendieck abelian categories. The
IH for `grothendieck_vanishing_aux` only passes through spaces of strictly smaller dimension.
I found no circularity.

## 4. Hypothesis Audit

Main theorem: `GrothendieckVanishing (X : TopCat.{u}) (F : Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X)`

- `X : TopCat.{u}`: Required. Cannot weaken beyond topological spaces.
- `F : Sheaf AddCommGrpCat.{u} X`: Required. The theorem is about sheaves of abelian groups.
- `[NoetherianSpace X]`: Required. Counterexamples exist for non-Noetherian spaces.
- `n : ℕ`: Could be generalized to `ℤ` or `ℕ∞`, but `ℕ` is standard for Hartshorne.
- `h : n > topologicalKrullDim X`: Required. The comparison `n > d` where d is WithBot ℕ∞
  is correct — if dim = ⊤, no n satisfies this, so the theorem is vacuous for
  infinite-dimensional spaces.

**Possible weakness**: The theorem uses `topologicalKrullDim` which is the Krull dimension
of the topological space, not the Krull dimension of a scheme. For non-scheme topological
spaces, this may differ from the classical notion. This is standard for Hartshorne III.2.7
but could be made more explicit.

## 5. Mathematical Correctness

The proof follows Hartshorne III.2.7 faithfully:
- WF induction on dimension
- Irreducible case: closed-open decomposition + SES
- Dim 0: constant sheaf flasque
- Dim ≥ 1: kernel vanishing via zeroOutsideInt + filtered diagram

The sorry is at the correct step (Hartshorne III Lemma 2.9, filtered colimit commutes
with cohomology). The dimension shift decomposition (Ext LES + injective vanishing)
is mathematically correct.

I found no divergence from the standard proof.

## 6. Code Quality

| File | Lines | Status |
|------|-------|--------|
| IrreducibleStep.lean | 1263 | **26% over 1000-line guideline** |
| ZeroOutside.lean | 733 | OK |
| FlasqueVanishing.lean | 616 | Slightly over 600 |
| FiniteGeneratorReduction.lean | 519 | OK |
| All others | ≤ 517 | OK |

- `IrreducibleStep.lean` at 1263 lines is the largest file. It was already split once
  (from 1604 lines). A further split into `IrreducibleStep.lean` + `EpiImageVanishing.lean`
  would bring both under 700 lines.
- No heartbeat overrides.
- No `set_option` usage at all.
- The sorry is well-isolated with clear comments explaining the gap.

## 7. Documentation Lies

- `main.lean` header says "1 sorry" — correct.
- `GrothendieckVanishing.lean` header says "1 sorry: ext_comm_filtered_colimit_mono n≥1
  case — Mathlib API gap" — accurate but the sorry is now more precisely at the
  `Subsingleton (Ext Z Q n)` subgoal after dimension shifting. The header could be updated
  to reflect this decomposition.
- `FiniteGeneratorReduction.lean` header: accurately describes the sorry location.
- `plan.md` says "1 sorry" — correct.
- `plan.md` says "~5100 lines" — actual is 5183. Close enough.

## 8. Generalization Opportunities

1. **Drop NoetherianSpace to finite cohomological dimension** (feasibility: medium):
   The theorem holds for any topological space of finite cohomological dimension,
   not just Noetherian spaces. This would require replacing the Noetherian induction
   with a direct cohomological dimension argument.

2. **Generalize to arbitrary Grothendieck topologies** (feasibility: hard):
   The theorem holds for sheaves on any site with finite cohomological dimension,
   not just topological spaces. The proof uses stalk arguments specific to topological
   spaces in several places.

3. **Extract `FlasqueVanishing` as standalone Mathlib PR** (feasibility: easy):
   The flasque sheaf cohomological vanishing theorem (`FlasqueVanishing`) is
   self-contained and useful independently of Grothendieck vanishing.

## 9. Mathlib Upstreamability

1. **`FlasqueVanishing`** (FlasqueVanishing.lean): Flasque sheaves have vanishing higher
   cohomology. Self-contained, ~616 lines. Would need universe polymorphism cleanup.

2. **`constantSheaf_flasque_of_irreducible`** (ConstantSheafFlasque.lean): The constant
   sheaf on an irreducible space is flasque. ~224 lines, clean.

3. **`subsingleton_ext_of_ses` / `subsingleton_ext_of_ses_middle` / `subsingleton_ext_of_ses_third`**
   (IrreducibleStep.lean): General-purpose Ext vanishing lemmas from short exact sequences.
   These are missing from Mathlib and useful for any Ext computation.

4. **`sheafH_vanishing_cascade`** (GrothendieckVanishing.lean): Vanishing cascades from
   one degree to all higher degrees. General-purpose.

## Verdict: CONDITIONAL PASS

Conditions:
1. **P0**: Wait for CI run 23925073144 to complete green.
2. **P1**: Fix docs/blueprint 404 (or document that it's not yet set up).
3. **P1**: The 1 sorry in `ext_comm_filtered_colimit_mono` is a genuine Mathlib gap.
   Acceptable for a formalization that honestly documents it.
4. **P2**: Consider splitting `IrreducibleStep.lean` (1263 lines) further.
5. **P3**: Update `GrothendieckVanishing.lean` header to reflect the dimension-shift
   decomposition of the sorry.
