# Adversarial Critique — 2026-03-10 UTC (Cycle 69)

## Verdict: CONDITIONAL ACCEPT

---

## 0. Errors

`lake build` — **clean, no errors.**

---

## 1. Sorry's

**1 sorry** in `CoulombConcreteTheorem42_nonvacuous`:

| Line | Goal | Statement | Risk |
|------|------|-----------|------|
| ~704 | (10) hVlasov | `0 = ν * LandauOperator coulombKernel eM` | **High** — requires Maxwellian in kernel of Landau operator |

This is the last sorry. It asserts that the equilibrium Maxwellian is in the null space of the Landau collision operator. This is a well-known physics result but the formal proof requires showing that the Landau operator vanishes on Maxwellians — essentially that collisions preserve the equilibrium distribution.

**Worst-case scenario:** If `LandauOperator` is defined in a way that doesn't match the standard physics definition, the non-vacuousness claim is false. The sorry hides both the mathematical argument AND the definition-matching verification.

---

## 2. Hidden Axioms

`lean_verify` on both main theorems: zero axioms beyond the standard three (`propext`, `Classical.choice`, `Quot.sound`). No `admit`, `axiom`, `native_decide`, or linter suppression found.

I found no issue.

---

## 3. Circularity

With 10 of 10 non-trivial goals addressed (9 proved, 1 sorry'd), the non-vacuousness defense is nearly complete. The only gap is sorry (10) — the Vlasov equation. Since this is the only remaining sorry, any hidden circularity would have to be in the definitions themselves, not in proved lemmas.

---

## 4. Hypothesis Audit

No change from cycle 68. All 13 hypotheses are independent and necessary.

---

## 5. Mathematical Correctness

I found no divergence. The main theorems are kernel-verified. The new `quadratic_iteratedFDeriv_bound` proof correctly handles all three cases (i=1, i=2, i≥3) of iterated derivatives of the quadratic form -normSq/(2T).

---

## 6. Code Quality

### 6a. maxHeartbeats overrides: 1 total

`synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean. Acceptable.

### 6b. Files over 600 lines (6 files)

| File | Lines |
|------|-------|
| TorusInstance.lean | 816 |
| Defs.lean | 785 |
| CoulombConcreteTheorem42.lean | 720 |
| CoulombPSD.lean | 703 |
| CoulombSpatialTransport.lean | 662 |
| Section3Helpers.lean | 625 |

CoulombConcreteTheorem42.lean grew from ~460 to 720 lines after adding the derivative bound helpers. The general helper lemmas (`iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm`) could be extracted to a shared file or Section3Helpers.

### 6c. Long lines

No lines over 100 characters found.

---

## 7. Documentation Lies

MEMORY.md updated in cycle 68: sorry count (1), line count (~720 for CoulombConcreteTheorem42). Accurate.

I found no issue.

---

## 8. Generalization Opportunities

### 8a. Close remaining sorry (10) hVlasov (HARD)

The Landau operator nullspace property for Maxwellians. This requires:
1. Showing the score difference ∇log(eM(v)) - ∇log(eM(w)) is proportional to (v-w)
2. Showing the Landau matrix applied to (v-w) gives a specific tensor structure
3. Showing the resulting integral vanishes by symmetry

### 8b. Extract general helper lemmas to shared file (EASY)

`iteratedFDeriv_clm_zero` and `norm_iteratedFDeriv_one_clm` are general Lean/Mathlib facts, not specific to the Coulomb formalization. Moving them to a shared helpers file would reduce CoulombConcreteTheorem42.lean by ~20 lines and make them reusable.

### 8c. Weaken spatial smoothness: C^∞ → C^2 (DEFERRED)

### 8d. Generalize beyond T³ (HARD)

### 8e. Extract Mathlib-upstreamable lemmas (MEDIUM)

`iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm`, and `norm_iteratedFDeriv_proj_sq_le` are candidates for Mathlib PRs.

---

## 9. Mathlib Upstreamability

The new helper lemmas from cycle 68 are the most PR-ready:
- `iteratedFDeriv_clm_zero`: iteratedFDeriv of a CLM vanishes at order ≥ 2
- `norm_iteratedFDeriv_one_clm`: ‖iteratedFDeriv 1 f x‖ = ‖f‖ for CLM f

These are clean, general facts missing from Mathlib.

---

## 10. Summary Table

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 6b | 6 files over 600 lines (TorusInstance 816, Defs 785, CoulombConcreteTheorem42 720) | Minor | Open |
| 8a | Non-vacuousness theorem has 1 sorry (hVlasov) | Epistemic | Open |
| 8b | General helper lemmas in wrong file | Minor | Open |

### Conditions for ACCEPT

Close sorry (10) hVlasov OR provide a convincing decomposition into well-defined sub-lemmas with clear mathematical justification for each. No new sorry's should be introduced.
