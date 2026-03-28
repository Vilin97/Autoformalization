# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-03-28T08:15Z
**Reviewer verdict**: REVISE

---

## 0. CI Status

Two CI runs in progress at time of review; the most recent successful run passed. `lake build` locally produces **zero errors** but many warnings (see Code Quality). Blueprint and dep graph both return HTTP 200.

**Issue (P2)**: `set_option synthInstance.maxHeartbeats 80000` in Setup.lean:37 and ClosedOpenDecomposition.lean:22 triggers "Unscoped option ... is not allowed" warnings. These will likely become errors in a future Mathlib bump.

---

## 1. Sorry's / Admits

Three `admit`s in `Setup.lean`, zero `sorry`s elsewhere. All three flow into `GrothendieckVanishing` (verified: `lean_verify` returns `sorryAx`).

| Axiom | File:Line | Statement true? | Risk |
|---|---|---|---|
| `FlasqueVanishing` | Setup.lean:46 | Yes (standard) | Low — provable via Godement resolution when Mathlib has it |
| `ReducibleVanishing` | Setup.lean:65 | Yes (standard, needs j\_!) | **Medium** — the statement encodes the full reducible case. If the closed-open SES has a subtle formulation error (e.g. wrong universe, wrong notion of restriction), this axiom hides it. |
| `IrreduciblePosVanishing` | Setup.lean:84 | Yes (Hartshorne Steps 3-5) | **Medium** — same concern: the IH in the axiom signature expects `∀ Y [NoetherianSpace Y] G ...` without `[IrreducibleSpace Y]`. If the actual proof needs the IH applied to reducible Y, this is fine; but the claim "needs j\_!" is predicated on a specific proof strategy. Alternative strategies (generic stalk, skyscraper sheaf) might not need the exact same IH shape. |

**Worst-case scenario**: `ReducibleVanishing` and `IrreduciblePosVanishing` are effectively `sorry`'d full-strength lemmas whose STATEMENTS might be subtly wrong (e.g., missing a finiteness condition on dim X, or needing the IH to quantify over a different collection of spaces). Because the axioms are `admit`'d, Lean's kernel cannot catch such errors.

---

## 2. Hidden Axioms

`lean_verify GrothendieckVanishing` returns: `propext, sorryAx, Classical.choice, Quot.sound`.

- `sorryAx` is present — the theorem is NOT fully proven.
- `constantSheaf_flasque_of_irreducible` is clean: `propext, Classical.choice, Quot.sound` only.
- `constantSheaf_cohomology_vanishing` inherits `sorryAx` from `FlasqueVanishing`.
- `grothendieck_vanishing_dim_zero` inherits `sorryAx` from `FlasqueVanishing`.

**Issue (P1)**: The main theorem depends on `sorryAx`. Any claim of "proof complete" must be qualified as "structurally complete modulo 3 axioms".

---

## 3. Circularity

I found no circularity in the proof structure. The induction on `WithBot ℕ∞` via `WellFounded.induction` is correct. The IH in `grothendieck_vanishing_aux` quantifies over `d' < d`, and the callback correctly passes `lt_of_lt_of_le hlt (hd ▸ hle)` to prove the strict inequality. The dim 0 case does not invoke the IH. The axioms do not use the conclusion as input.

However: `ReducibleVanishing` takes `ih_irred` quantified over irreducible Y with `dim Y ≤ dim X` (not `<`). This means the axiom's internal proof would need to reduce to STRICTLY lower dimension or use a different induction (e.g., on component count). The `≤` vs `<` is intentional (the main induction handles the `<` part), but a reviewer who only reads the axiom statement might question it.

---

## 4. Hypothesis Audit

Main theorem:
```
GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n)
```

| Hypothesis | Necessary? | Could weaken? |
|---|---|---|
| `TopCat.{u}` | Necessary (Mathlib API) | Could generalize to any site |
| `AddCommGrpCat.{u}` | Necessary for this formulation | Could generalize to any Grothendieck abelian category |
| `[NoetherianSpace X]` | **Necessary** | No — the theorem fails without Noetherian |
| `n : ℕ` | Sufficient | `n = 0` gives trivially true statement. Could use `n + 1` to avoid vacuous cases |
| `n > topologicalKrullDim X` | Correct | If `dim X = ⊤`, hypothesis is vacuously false — correct but subtle |
| `Subsingleton (Sheaf.H F n)` | Correct formulation of "= 0" | Could strengthen to `IsZero` |

**Issue (P3)**: The theorem is stated for `AddCommGrpCat` only. Hartshorne's result applies to sheaves of abelian groups on any ringed space.

---

## 5. Mathematical Correctness

The proof structure faithfully follows Hartshorne III.2.7. I found no divergence.

**Issue (P2)**: `constantSheaf_flasque_of_irreducible` only shows the constant sheaf with value `ULift ℤ` is flasque. It does NOT show the constant sheaf with an arbitrary abelian group value is flasque. This suffices for the theorem but the name is misleading.

---

## 6. Code Quality

| Issue | Severity | Location |
|---|---|---|
| `maxHeartbeats 1600000` | **P1** | ConstantSheafFlasque.lean:108 — 4x default. Decompose. |
| Unscoped `synthInstance.maxHeartbeats 80000` | **P1** | Setup.lean:37, ClosedOpenDecomposition.lean:22 |
| Unused simp argument | P3 | ConstantSheafFlasque.lean:97 |
| `simp` instead of `simp only` | P3 | Multiple locations |
| `change` for Meq API mismatch | P2 | ConstantSheafFlasque.lean:129-132 — fragile |

---

## 7. Documentation Lies

**8 stale documentation claims** — every docstring mentioning "sorry" when the code now uses axioms or is proved:

1. IrreducibleStep.lean:9 — "constantSheaf_flasque_of_irreducible: sorry" (PROVED)
2. IrreducibleStep.lean:11 — "grothendieck_vanishing_irreducible_pos: sorry" (uses axiom)
3. GrothendieckVanishing.lean:10 — "IrreducibleStep: sorry"
4. GrothendieckVanishing.lean:11 — "ClosedOpenDecomposition: sorry"
5. GrothendieckVanishing.lean:25 — "Combines ClosedOpenDecomposition (sorry)"
6. ClosedOpenDecomposition.lean:91-95 — "sorry — blocked" + stale H'≅H claim
7. main.lean:12 — "SORRY — reduction to irreducible"
8. main.lean:13 — "SORRY — irreducible dim ≥ 1"

---

## 8. Generalization Opportunities

1. **(Feasible)** Generalize `constantSheaf_flasque_of_irreducible` from `ULift ℤ` to any abelian group `A`.
2. **(Moderate)** PR `subsingleton_ext_of_ses` and `CohomologyIso` to Mathlib.
3. **(Hard)** Build j\_! to eliminate the 2 non-FlasqueVanishing axioms.
4. **(Hard)** Generalize theorem from `AddCommGrpCat` to `ModuleCat R`.

---

## 9. Mathlib Upstreamability

| Candidate | Feasibility |
|---|---|
| `CohomologyIso.lean` (H'(⊤) ≅ H) — resolves explicit Mathlib TODO | **High** |
| `subsingleton_ext_of_ses` — generic Ext LES vanishing | **High** |
| `plusObj_bot_subsingleton` — generalize to arbitrary sites | Medium |
| Dimension inequality lemmas in Auxiliary.lean | Medium |

---

## Verdict: REVISE

### Conditions for CONDITIONAL ACCEPT:

1. Fix all 8 stale documentation claims (P1).
2. Fix unscoped `synthInstance.maxHeartbeats` (P1). Use `set_option ... in` scoped form.
3. Reduce `maxHeartbeats 1600000` (P1). Decompose `toPlus_surjective_of_firstPlus`.
4. Remove unused simp argument at ConstantSheafFlasque.lean:97.
5. Acknowledge axioms honestly in main.lean. Replace "SORRY" with "AXIOM (needs j\_!)".

### Conditions for ACCEPT (no sorryAx):

6. Build j\_! to eliminate `ReducibleVanishing` and `IrreduciblePosVanishing`.
7. Prove `FlasqueVanishing`.
