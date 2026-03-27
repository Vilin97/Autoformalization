# Log — Grothendieck Vanishing

## 2026-03-27T19:15Z — Cycle 2: Decompose IrreducibleStep

**Sorry count: 3 mathematical + 1 axiom (FlasqueVanishing)**
(sorry count increased from 2 to 3 by decomposition — this is progress)

### Accomplished
- Decomposed `IrreducibleStep.lean` from 1 opaque sorry into 3 named sub-lemmas:
  - `constantSheaf_flasque_of_irreducible` (sorry) — Z has epi restrictions on irreducible X
  - `constantSheaf_cohomology_vanishing` (**proved**) — H^{n+1}(X, Z) = 0, from flasque + FlasqueVanishing
  - `grothendieck_vanishing_irreducible_pos` (sorry) — main step with detailed proof sketch
- Added callback sufficiency documentation to `ClosedOpenDecomposition.lean`
- Added Prop 2.9 placeholder (`cohomology_direct_limit_noetherian`)

### Aristotle status
- `fca6885d`: ClosedOpenDecomposition — 21%
- `bc3176de`: IrreducibleStep — 15%

### Remaining sorry's
1. `ClosedOpenDecomposition.lean` — `grothendieck_vanishing_of_irreducible` (reduce to irreducible)
2. `IrreducibleStep.lean:29` — `constantSheaf_flasque_of_irreducible` (Z flasque on irreducible)
3. `IrreducibleStep.lean:63` — `grothendieck_vanishing_irreducible_pos` (irreducible dim ≥ 1)
4. `Setup.lean:38` — `FlasqueVanishing` (axiom, do not prove)

## 2026-03-27T18:55Z — Cycle 1: Initial build + babysit

**Sorry count: 2 mathematical + 1 axiom (FlasqueVanishing)**

### Accomplished
- Built the full proof skeleton for Grothendieck's vanishing theorem (Hartshorne III.2.7)
- **7 files**, 331 lines total, clean `lake build`
- **Proved** (sorry-free modulo FlasqueVanishing axiom):
  - `Auxiliary.lean`: `epi_of_isTerminal_tgt`, `isTerminal_sheaf_bot`, `opens_eq_bot_or_top_of_irreducibleSpace_dim_zero`, `closure_singleton_eq_univ_of_dim_zero`, `irreducibleCloseds_unique_of_dim_zero`, `topologicalKrullDim_nonneg_of_irreducible`
  - `DimZeroVanishing.lean`: `sheaf_restriction_epi_of_irreducible_dim_zero`, `grothendieck_vanishing_dim_zero` (Hartshorne Step 2: all sheaves on irreducible dim-0 spaces are flasque)
  - `GrothendieckVanishing.lean`: main theorem assembled by well-founded induction on `topologicalKrullDim`
- Ran `/critique` — verdict REVISE, flagged callback signature concern (P0) and sorry load (P0)
- Moved `topologicalKrullDim_nonneg_of_irreducible` to `Auxiliary.lean` for better organization
- Fixed documentation: "PROVED" → "assembled" in `main.lean`

### Submitted to Aristotle
- `fca6885d`: `grothendieck_vanishing_of_irreducible` (ClosedOpenDecomposition, Step 1) — 16%
- `bc3176de`: `grothendieck_vanishing_irreducible_pos` (IrreducibleStep, Steps 3–5) — 8%

### Remaining sorry's
1. `ClosedOpenDecomposition.lean:39` — `grothendieck_vanishing_of_irreducible` (reduce to irreducible, needs extension by zero + Lemma 2.10)
2. `IrreducibleStep.lean:41` — `grothendieck_vanishing_irreducible_pos` (irreducible dim ≥ 1, needs Prop 2.9 + Z_U SES)
3. `Setup.lean:38` — `FlasqueVanishing` (intentional axiom, do not prove)
