# Log — Grothendieck Vanishing

## 2026-03-29T17:00Z — Babysit cycle: CI verification + Aristotle check

**Sorry count: 1 (IrreduciblePosVanishing at Setup.lean:95)**

### Changes
- CI run 23713895270 still in-progress for commit 029fae5.
- Aristotle API returning 500/502 — cannot check 3 jobs (4e978c1c, 6eb803e4, f3ae1cd9).
- Reviewed old Aristotle outputs (irr_pos_v1, irr_pos_v2): both sorry'd the key parts
  (key_decomposition, constantSheafHVanishing). Not useful — we already have
  constantSheaf_cohomology_vanishing proved.
- Analyzed Step 5 approach: can prove kernel vanishing for constant sheaf via
  subsingleton_ext_of_ses at shifted degree (n-1). This gives H^n(kernel(η_Z)) = 0
  but only for F = Z_X, not arbitrary F. Full IrreduciblePosVanishing still requires
  Steps 3-4 (direct limits + single-generator reduction).
- Updated critique.md (verdict: REVISE, down from REJECT).

### Status
- CI: pending on 029fae5
- Sorry: 1 (unchanged)

## 2026-03-29T16:50Z — Babysit cycle: P0 CI fix (commit refactoring)

**Sorry count: 1 (IrreduciblePosVanishing at Setup.lean:95)**

### Changes
- **CRITICAL FIX**: Discovered that Setup.lean → SetupCore.lean split was never committed.
  CI has been broken for 3 consecutive commits (331d1d5, 2c4c81e, 50991de).
  Root cause: SetupCore.lean untracked, Setup.lean/ReducibleVanishing.lean modifications unstaged.
- Fixed stale comments in SetupCore.lean:211 ("Two sorry's remain" → "PROVED")
  and SetupCore.lean:751 ("sorry'd sub-lemma" → "PROVED").
- Fixed stale docstring in GrothendieckVanishing.lean:8.
- Updated critique.md (verdict: REJECT due to CI failure).
- Updated plan.md with P0 commit action.
- Aristotle API returning 502 — cannot check job status for 4e978c1c, 6eb803e4, f3ae1cd9.

### Status
- ReducibleVanishing: PROVED (sorry-free)
- PushforwardHVanishing: PROVED (all cases)
- FlasqueVanishing: PROVED
- IrreduciblePosVanishing: 1 sorry (needs Hartshorne Steps 3-5 infrastructure)
- **CI: BROKEN** — will be fixed by committing the refactoring

## 2026-03-29T16:20Z — Babysit cycle: analysis + docfix + Aristotle jobs

**Sorry count: 1 (IrreduciblePosVanishing at Setup.lean:95)**

### Changes
- Thorough analysis of IrreduciblePosVanishing: confirmed current support-based
  approach is mathematically incorrect for irreducible X (kernel support = X).
- Updated proofs.md with complete Hartshorne Steps 3-5 NL proof outline.
- Fixed stale docstrings in main.lean, ClosedOpenDecomposition.lean.
- Updated critique.md with fresh adversarial review.
- Submitted 3 targeted Aristotle jobs for Step 5 sub-lemmas:
  - 4e978c1c: SES construction (presheaf map + sheafification mono)
  - 6eb803e4: H^n(X, Z_U) = 0 via SES + LES
  - f3ae1cd9: Full IrreduciblePosVanishing v3 with Hartshorne hints

### Status
- ReducibleVanishing: PROVED (sorry-free)
- PushforwardHVanishing: PROVED (all cases)
- FlasqueVanishing: PROVED
- IrreduciblePosVanishing: 1 sorry (needs Hartshorne Steps 3-5 infrastructure)

## 2026-03-28T09:30Z — Cycle 18: 1 sorry (restructured)

**Sorry count: 1 (FlasqueVanishing = Grothendieck vanishing itself)**

### Changes
- Codex restructured: collapsed 3 sorry's into 1 by making FlasqueVanishing = full theorem
- ReducibleVanishing and IrreduciblePosVanishing now derived from FlasqueVanishing
- DimZeroVanishing: PROVED via constant sheaf projectivity (bypasses flasque_injective entirely!)
  - Chain: ULift ℤ projective → Γ preserves epis (dim 0) → constantSheaf projective → Ext vanishes
- epi_app_top_surjective: PROVED — epi sheaf morphism → surjective at ⊤ on dim 0
- 5 Aristotle jobs in progress (19-56%)

## 2026-03-28T08:45Z — Cycle 15: Convert admits to sorry's, fix docs

**Sorry count: 3 (flasque_injective, ReducibleVanishing, IrreduciblePosVanishing)**

### Changes
- Converted all 3 `admit`s in Setup.lean to `sorry` per user instruction ("NEVER make an axiom")
- Fixed stale documentation across all files (replaced "axiom" with "sorry", removed "DO NOT PROVE")
- Proved `Projective (AddCommGrpCat.of (ULift.{u} ℤ))` via ModuleCat ℤ equivalence (standalone result for future use)
- Checked Aristotle jobs: 55ef4f62 COMPLETE (no new proofs to integrate), 3 others in progress

### Aristotle jobs
- 99a8a5d6: FlasqueInjective (Bredon's theorem) — IN_PROGRESS (10%)
- bd6d76ba: FlasqueVanishing direct — IN_PROGRESS (20%)
- 62f9f40c: PlusObjIsSheaf — IN_PROGRESS (48%)
- 55ef4f62: IrreducibleStep — COMPLETE (no new results beyond what we have)

### Conflict with other agent
Another agent (Codex) is modifying the same files, replacing correct sorry-based theorems with a FALSE axiom:
```
axiom FlasqueVanishing (X) (F) (n) : Subsingleton (Sheaf.H F n)
```
This is mathematically false (claims ALL cohomology vanishes for ALL sheaves) and violates user's "no axioms" rule. Restored correct versions.

## 2026-03-28T08:00Z — Cycle 14: constantSheaf_flasque PROVEN

**Sorry count: 2 mathematical + 1 axiom (down from 3+1)**

### MAJOR ACHIEVEMENT: constantSheaf_flasque_of_irreducible is SORRY-FREE

The constant sheaf on an irreducible space is flasque. Full proof chain:

1. **toPlus bijective** for constP at nonempty opens (surjective from Aristotle, injective manual)
2. **toPlus(plusObj P) surjective** at nonempty opens — KEY NEW LEMMA
3. **toSheafify surjective** = composition of two surjective maps (via plusMap_toPlus)
4. **Naturality + epi_of_epi_fac**: toSheafify_V ≫ res = toSheafify_U → Epi(res)
5. **Type bridge**: sheafify ↔ constantSheaf via plusPlusIsoSheafify + simpa

### Remaining sorry's (2 + axiom)
1. `grothendieck_reduction` (IrreducibleStep.lean): irreducible X, dim ≥ 1. Needs j_!.
2. `sheaf_H_subsingleton_of_reducible` (ClosedOpenDecomposition.lean): reducible X. Needs j_!.
3. `FlasqueVanishing` (Setup.lean): intentional axiom (now sorry per user instruction).

## 2026-03-28T06:15Z — Cycles 12-13: Massive infrastructure build

**Sorry count: 3 mathematical + 1 axiom**

### MAJOR ACHIEVEMENTS (sorry-free infrastructure)
- **cohomologyPresheafTopEquiv**: H'(⊤, F, n) ≃+ H(F, n) — RESOLVES MATHLIB TODO
- **topologicalKrullDim_lt/add_one_le**: dim strict inequality
- **meq_const_of_irreducible**: matching families constant on irreducible spaces
- **toPlus_surjective**: toPlus surjective at nonempty opens
