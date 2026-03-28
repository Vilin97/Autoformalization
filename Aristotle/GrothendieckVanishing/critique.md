# Adversarial Critique — Grothendieck Vanishing Formalization

**Timestamp**: 2026-03-28T08:20Z
**Reviewer verdict**: REVISE

---

## 0. CI Status

Latest CI run (23681059730) in progress. Previous two runs passed. `lake build` not yet verified this cycle. Blueprint and dep graph both return HTTP 200.

**Issue (P1)**: `admit` used instead of `sorry` in Setup.lean:44, 75, 95. User explicitly mandates: "NEVER make an axiom. Any statement you can't prove immediately needs to be a sorry." Convert all `admit` to `sorry`.

**Issue (P2)**: `set_option synthInstance.maxHeartbeats 80000` in Setup.lean:37,46,57,77 uses unscoped form. Will become errors in future Mathlib bumps.

---

## 1. Sorry's / Admits

3 `admit`s in `Setup.lean`, 0 `sorry`s elsewhere. All three flow into `GrothendieckVanishing`.

| Axiom | File:Line | Statement true? | Risk |
|---|---|---|---|
| `flasque_injective` | Setup.lean:44 | Yes (Bredon's theorem) | **Medium** — requires Zorn's lemma argument on partial extensions. Aristotle job 99a8a5d6 at 5%. |
| `ReducibleVanishing` | Setup.lean:75 | Yes (standard, needs j\_!) | **High** — needs extension by zero infrastructure. No Aristotle job currently targeting this. |
| `IrreduciblePosVanishing` | Setup.lean:95 | Yes (Hartshorne Steps 3-5) | **High** — needs j\_! or closed-open SES. No Aristotle job targeting this. |

**Critical**: All 3 must be converted from `admit` to `sorry` per user instruction.

---

## 2. Hidden Axioms

The `admit` keyword in Lean 4 introduces `sorryAx` but suppresses the warning. This hides the incompleteness. Converting to `sorry` will make the gaps visible.

- `constantSheaf_flasque_of_irreducible` is clean (sorry-free).
- `FlasqueVanishing` depends on `flasque_injective` (admit).
- `ReducibleVanishing` and `IrreduciblePosVanishing` are directly admit'd.

---

## 3. Circularity

No circularity found. The induction on `WithBot ℕ∞` via `WellFounded.induction` is correct. The IH in `grothendieck_vanishing_aux` quantifies over `d' < d`.

`ReducibleVanishing` takes `ih_irred` with `dim Y ≤ dim X` (not `<`). This is intentional — the outer induction handles the strict decrease.

---

## 4. Hypothesis Audit

| Hypothesis | Necessary? | Could weaken? |
|---|---|---|
| `TopCat.{u}` | Necessary (Mathlib API) | Could generalize to any site |
| `AddCommGrpCat.{u}` | Necessary | Could generalize to any Grothendieck abelian |
| `[NoetherianSpace X]` | **Necessary** | No |
| `n : ℕ` | Sufficient | Could use `n + 1` to avoid vacuous `n = 0` |
| `n > topologicalKrullDim X` | Correct | dim X = ⊤ makes hypothesis vacuously false — correct |
| `Subsingleton (Sheaf.H F n)` | Correct | Could strengthen to `IsZero` |

---

## 5. Mathematical Correctness

The proof structure faithfully follows Hartshorne III.2.7. No divergence found.

---

## 6. Code Quality

| Issue | Severity | Location |
|---|---|---|
| `admit` instead of `sorry` | **P0** | Setup.lean:44,75,95 |
| `maxHeartbeats 1600000` | **P1** | ConstantSheafFlasque.lean:108 — 4× default |
| Unscoped `synthInstance.maxHeartbeats 80000` | **P2** | Setup.lean:37,46,57,77 |
| `maxHeartbeats 800000` | P3 | ConstantSheafFlasque.lean:152, CohomologyIso.lean:55 |
| `maxHeartbeats 400000` | P3 | ConstantSheafFlasque.lean:18,27,68,86 |
| Stale docstrings | P2 | See §7 |

---

## 7. Documentation Lies

| Location | Claim | Reality |
|---|---|---|
| Setup.lean:2 | "axioms for Grothendieck vanishing" | Should say "sorry'd lemmas" per user instruction |
| Setup.lean:40 | "DO NOT PROVE — use as axiom" | User says prove everything |
| Setup.lean:64 | "DO NOT PROVE — use as axiom" | User says prove everything |
| Setup.lean:84 | "DO NOT PROVE — use as axiom" | User says prove everything |
| main.lean:8 | "FlasqueVanishing axiom" | FlasqueVanishing is proved (from flasque_injective) |
| main.lean:11-12 | "axiom — reduction/irreducible" | Should say "sorry" |
| main.lean:19 | "DO NOT PROVE FlasqueVanishing" | Contradicts user instruction |
| GrothendieckVanishing.lean:10-11 | "axiom — needs j\_!" | Should say "sorry" |
| GrothendieckVanishing.lean:25 | "Combines ... (axiom)" | Should say "(sorry)" |
| IrreducibleStep.lean:11 | "uses IrreduciblePosVanishing axiom" | Should say "sorry" |

---

## 8. Generalization Opportunities

1. **(Feasible)** Generalize `constantSheaf_flasque_of_irreducible` from `ULift ℤ` to arbitrary abelian group A.
2. **(Feasible)** PR `subsingleton_ext_of_ses` and `CohomologyIso` to Mathlib.
3. **(Hard)** Build j\_! (extension by zero) to prove `ReducibleVanishing` and `IrreduciblePosVanishing`.
4. **(Hard)** Prove `flasque_injective` (Bredon's theorem) via Zorn's lemma.
5. **(Hard)** Generalize from `AddCommGrpCat` to `ModuleCat R`.

---

## 9. Mathlib Upstreamability

| Candidate | Feasibility |
|---|---|
| `CohomologyIso.lean` (H'(⊤) ≅ H) | **High** |
| `subsingleton_ext_of_ses` | **High** |
| `plusObj_bot_subsingleton` | Medium |
| Dimension inequality lemmas in Auxiliary.lean | Medium |

---

## Verdict: REVISE

### Immediate actions (this cycle):
1. Convert all 3 `admit`s to `sorry` (P0).
2. Fix all stale documentation (P2).
3. Check Aristotle jobs for completed proofs.

### Next cycles:
4. Prove `flasque_injective` (Bredon's theorem).
5. Build j\_! infrastructure for ReducibleVanishing and IrreduciblePosVanishing.
6. Reduce `maxHeartbeats 1600000`.
