# Log — Grothendieck Vanishing

## 2026-03-30 — PERF: decompose 12.8M heartbeat proof (CI timeout fix)

**Sorry count: 2** (unchanged)

- **Split `epi_app_of_shortExact_flasque`** (12.8M heartbeats → no override):
  Extracted `IsPartialLift` predicate, `partialLift_chain_ub` (chain upper bound),
  `partialLift_maximal_eq_U` (contradiction argument). Main theorem is thin Zorn wrapper.
- **Split `PushforwardHVanishing`** (3.2M monolith → 3 case lemmas):
  `PushforwardHVanishing_zero` (n=0), `PushforwardHVanishing_one` (n=1),
  `PushforwardHVanishing_succ` (n≥2). Each gets focused heartbeat budget.
- **Peak maxHeartbeats**: 12,800,000 → 3,200,000 (75% reduction).
- **Aristotle**: Both `subsheaf_contains_zeroOutsideInt` jobs (v1 & v2) returned
  COMPLETE_WITH_ERRORS. Aristotle cannot solve the stalk classification problem.
- 2 sorry's remain (both in IrreducibleStep.lean):
  1. `subsheaf_contains_zeroOutsideInt` — Step 4 subsheaf structure
  2. `cohomology_vanishing_of_finitelyGenerated_vanishing` — Hartshorne 2.9

## 2026-03-30 — PROVE imageIncl_cokernel_epi (3→2 sorry's)

**Sorry count: 2** (was 3)

- **PROVED `imageIncl_cokernel_epi`**: the σ₀-component maps epi onto the cokernel of
  imageIncl. Uses biproduct projection (HasBiproduct from Abelian + Fintype) to factor
  factorThruImage ≫ cokernel.π through the σ₀-component, then epi_of_epi_fac.
  S'-components vanish via imageIncl ≫ cokernel.π = 0.
- Reverted SetupCore.lean to pre-perf state (cascading CI failures from optimization).
- 2 sorry's remain (both Mathlib gaps):
  1. `subsheaf_contains_zeroOutsideInt` — needs toSheafify_stalk_isIso for AddCommGrpCat
  2. `cohomology_vanishing_of_finitelyGenerated_vanishing` — Hartshorne 2.9 colimit

## 2026-03-30 — PROVE finsetGeneratedSheaf_vanishing (Steps 3B-3C, modulo epi)

**Sorry count: 3** (restructured)

- **PROVED `finsetGeneratedSheaf_vanishing`** via Finset.induction:
  - Empty: image = 0 (image of zero morphism from empty coproduct).
  - Insert σ₀: build mono image(S') → image(insert σ₀ S') via `image.lift`,
    SES 0 → old → new → cokernel → 0, cokernel is epi image of Z_{σ₀.1},
    middle-term LES gives vanishing.
- New helper constructions: `finsetCoproductIncl`, `imageIncl`, `imageIncl_mono`
- Remaining sorry: `imageIncl_cokernel_epi` (σ₀ component maps epi onto cokernel)
- 3 sorry's remain:
  1. `subsheaf_contains_zeroOutsideInt` — Aristotle at 75%
  2. `cohomology_vanishing_of_finitelyGenerated_vanishing` — Hartshorne 2.9
  3. `imageIncl_cokernel_epi` — σ₀ epi onto cokernel (replaces old finsetGenerated sorry)

## 2026-03-30 — Aristotle results: directLimit needs missing Mathlib infrastructure

**Sorry count: 3**

- Aristotle (b46c7418) COMPLETE_WITH_ERRORS for `directLimit_cohomology_vanishing`:
  Confirmed that Hartshorne 2.9 (cohomology commutes with filtered colimits) requires
  Mathlib infrastructure that doesn't exist: LES for right derived functors,
  filtered colimit commutativity for Ext. The theorem is a genuine Mathlib gap.
- Aristotle (159d3b74) `subsheaf_contains_zeroOutsideInt` at 57% — still working.
- `finsetGeneratedSheaf_vanishing` needs `Finset.subtypeInsertEquivOption` to connect
  Finset induction to the ⊕ Unit indexing in FiniteGeneratorReduction.lean.
- Fixed CI syntax error (stray paren).

## 2026-03-30 — Decompose directLimit_cohomology_vanishing

**Sorry count: 3** (was 2 — decomposed Step 3A)

- **PROVED `directLimit_cohomology_vanishing`** from two sub-lemmas:
  1. `finsetGeneratedSheaf_vanishing` — Steps 3B-3C: finite generator induction
  2. `cohomology_vanishing_of_finitelyGenerated_vanishing` — Hartshorne 2.9 core colimit step
- 3 sorry's remain:
  1. `subsheaf_contains_zeroOutsideInt` — Step 4 structure
  2. `cohomology_vanishing_of_finitelyGenerated_vanishing` — Hartshorne 2.9 colimit
  3. `finsetGeneratedSheaf_vanishing` — Steps 3B-3C finite case

## 2026-03-30 — Submit last 2 sorry's to Aristotle

**Sorry count: 2**

- Submitted `subsheaf_contains_zeroOutsideInt` to Aristotle (159d3b74)
- Submitted `directLimit_cohomology_vanishing` to Aristotle (b46c7418)
- Both are hard — Aristotle will attempt, we work in parallel

## 2026-03-30 — PROVE cokernel_stalk_zero_of_stalk_surj (3→2 sorry's)

**Sorry count: 2** (was 3)

- **PROVED `cokernel_stalk_zero_of_stalk_surj`**: cokernel stalks vanish at stalk-surjective
  points. Proof: get germ, use local surjectivity of cokernel.π (epi → locally surjective),
  lift through surjective stalk map, apply cokernel.condition (f ≫ cokernel.π = 0).
- 2 sorry's remain:
  1. `subsheaf_contains_zeroOutsideInt` — structure: nonzero R ⊆ Z_V contains Z_{V'}
  2. `directLimit_cohomology_vanishing` — Step 3A: reduce to finitely generated

## 2026-03-30 — PROVE subsheaf_zeroOutsideInt_vanishing (Step 4 glue)

**Sorry count: 3** (was 2 — decomposed Step 4 into 2 focused sub-lemmas)

- **PROVED `subsheaf_zeroOutsideInt_vanishing`** (Step 4 outer proof):
  For mono R → Z_V, H^m(R) = 0. Proof: find V' ⊆ V with Z_{V'} ↪ R (stalk-iso),
  SES 0 → Z_{V'} → R → cokernel → 0, cokernel supported on (V')^c (dim < dim X),
  middle-term LES gives H^m(R) = 0.
- Stated `subsheaf_contains_zeroOutsideInt` (sorry): nonzero R ⊆ Z_V contains Z_{V'}
- Stated `cokernel_stalk_zero_of_stalk_surj` (sorry): cokernel stalks vanish at surjective points
- 3 sorry's remain but all are more focused than before:
  1. `subsheaf_contains_zeroOutsideInt` — pure sheaf structure (stalks of Z_V)
  2. `cokernel_stalk_zero_of_stalk_surj` — exactness of stalk functor
  3. `directLimit_cohomology_vanishing` — Step 3A (Hartshorne 2.8-2.9)

## 2026-03-30 — PROVE isZero_zeroOutsideInt_bot

**Sorry count: 2** (was 3)

- PROVED `isZero_zeroOutsideInt_bot`: Z_⊥ is the zero sheaf. Proof transfers
  from sheaf stalk to presheaf stalk via `toSheafify`, then uses `¬(W ≤ ⊥)`
  for any W containing x to show the presheaf value is zero.
- 2 sorry's remain:
  1. `subsheaf_zeroOutsideInt_vanishing` — Step 4 (subsheaf structure of Z_V)
  2. `directLimit_cohomology_vanishing` — Step 3A (cohomology/colimit commutation)

## 2026-03-30 — PROVE epiImage_zeroOutsideInt_vanishing (Steps 3C+LES)

**Sorry count: 3** (was 2 — decomposed further)

- Added third-term LES: `subsingleton_sheafH_of_shortExact_third` (PROVED)
  For 0→X₁→X₂→X₃→0: H^n(X₂)=0 ∧ H^{n+1}(X₁)=0 ⟹ H^n(X₃)=0.
- **PROVED `epiImage_zeroOutsideInt_vanishing`**: for epi Z_V→G, H^m(G)=0.
  Uses third-term LES + Step 5 + Step 4 (subsheaf vanishing).
- Stated `isZero_zeroOutsideInt_bot` (sorry, small technical lemma)
- Stated `subsheaf_zeroOutsideInt_vanishing` (sorry, Step 4)
- 3 sorry's remain:
  1. `isZero_zeroOutsideInt_bot` — Z_⊥ is zero sheaf (small)
  2. `subsheaf_zeroOutsideInt_vanishing` — Step 4 (hard)
  3. `directLimit_cohomology_vanishing` — Step 3A (hard)

## 2026-03-30 — PROVE zeroOutsideInt_cohomology_vanishing (Step 5) + restructure

**Sorry count: 2** (was 3)

- Moved sorry lemmas + `IrreduciblePosVanishing` from Setup.lean to IrreducibleStep.lean
  to resolve circular dependency (sorry proofs need IrreducibleStep tools).
- **PROVED `zeroOutsideInt_cohomology_vanishing`** (Hartshorne Step 5):
  H^m(Z_V) = 0 for m > dim X on irreducible Noetherian X with dim > 0.
  Proof: write m = m'+1, apply `zeroOutsideInt_vanishing`, prove cokernel vanishing
  at degree m' via ClosedImmersionSES on V^c + PushforwardHVanishing + degree-universal IH.
- Setup.lean is now sorry-free (only helpers + ReducibleVanishing wrapper).
- 2 sorry's remain in IrreducibleStep.lean:
  1. `epiImage_zeroOutsideInt_vanishing` (Steps 3C+4+LES)
  2. `directLimit_cohomology_vanishing` (Step 3A)

## 2026-03-30 — Decompose IrreduciblePosVanishing into 3 sorry sub-lemmas

**Sorry count: 3 (was 1 — decomposed into sub-lemmas)**

Key changes:
1. **Generalized IH to degree-universal**: Changed the induction hypothesis in
   `IrreduciblePosVanishing`, `cokernel_openHom_vanishing`, and 6 other theorems
   from fixed degree `n` to universal `(m : ℕ)`. This is necessary because
   Hartshorne's proof needs vanishing at ALL degrees above `dim X` simultaneously
   (the LES argument shifts degree by +1).
2. **Decomposed `irreduciblePos_kernel_subsingleton`** into 3 sub-lemmas:
   - `zeroOutsideInt_cohomology_vanishing` — Step 5: H^m(Z_V) = 0
   - `epiImage_zeroOutsideInt_vanishing` — Steps 3C+4+LES: epi images of Z_V vanish
   - `directLimit_cohomology_vanishing` — Step 3A: reduce to finitely generated
3. **Closed the main sorry** using the assembly:
   `directLimit_cohomology_vanishing S.X₁ n (fun f hf => epiImage_zeroOutsideInt_vanishing X ih hpos _ f hf n hn)`

Files changed: Setup.lean (3 sorry lemmas + kernel filled), IrreducibleStep.lean,
ClosedOpenDecomposition.lean, GrothendieckVanishing.lean (all IH generalization).

**Architecture note**: The 3 sorry lemmas are in Setup.lean but their proofs will
need tools from IrreducibleStep.lean. A future cycle should move them to
IrreducibleStep.lean to resolve the circular dependency.

## 2026-03-29T18:40Z — Babysit cycle: root-cause CI fix

**Sorry count: 1 (IrreduciblePosVanishing at Setup.lean:95)**

### Changes
- **ROOT CAUSE FOUND**: CI failures since commit 331d1d5 were caused by
  `synthInstance.maxHeartbeats 160000` being too low for `Localization.HasSmallLocalizedHom`
  synthesis in PushforwardHVanishing proof (on derived categories of sheaves on closed subspaces).
  The proof was written after b8a1821 but never compiled by CI (was sorry'd in b8a1821).
  Increased to 400000. Also increased for closedIncl_pushforward_shortExact.
- All previous "fix" commits (congr_arg, Subsingleton) were SECONDARY errors caused
  by the cascading failure from this synthesis timeout.

### Status
- CI: 688b28b pushed with heartbeat fix, awaiting result
- Sorry: 1 (unchanged)

## 2026-03-29T18:20Z — Babysit cycle: CI fixes + Step 5 theorem

**Sorry count: 1 (IrreduciblePosVanishing at Setup.lean:95)**

### Changes
- Fixed CI build errors in SetupCore.lean:
  - 78f7fe4: `congr_arg (· (ULift.up 1))` → explicit lambda
  - 2178710: explicit `@Subsingleton.elim` instances in `subsingleton_sheafH_of_shortExact_middle`
- **NEW THEOREM**: `constantSheaf_kernel_vanishing` (IrreducibleStep.lean) — Step 5 of Hartshorne.
  Proves kernel of Z_X → i_*(i^*Z_X) has vanishing cohomology using flasque vanishing +
  PushforwardHVanishing + subsingleton_ext_of_ses at shifted degree.
- Discovered extensive Step 3B infrastructure in ZeroOutside.lean (500+ lines) and
  FiniteGeneratorReduction.lean — `adjoinGeneratorShortComplex`, `familyGeneratedSheaf`,
  `subsingleton_of_adjoinGenerator_of_zeroOutside`. The finite-generator induction framework
  is essentially complete.
- CI runs for fixes + Step 5 in-progress.
- Aristotle API still down (500).

- **KEY DISCOVERY**: `zeroOutsideInt ⊤ = constantSheaf Z_X` by `rfl`! This means
  `openHom(le_top) : zeroOutsideInt V → Z_X` is literally a mono into the constant sheaf.
  The composite η ∘ openHom(le_top) = 0 (since W ≤ V → W ∩ Z = ∅ → target is 0),
  so openHom factors through kernel(η), and the factoring map is an iso.
  This connects `constantSheaf_kernel_vanishing` to `zeroOutsideInt V` vanishing.

### Status
- CI: 2178710 FAILED (same commit had both fixes but only included Subsingleton one).
  2ab3391 and da0ba5b in-progress (should pass).
- Sorry: 1 (unchanged, but Step 5 + rfl identity make the path to closure clearer)

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
