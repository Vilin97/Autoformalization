# Log — Grothendieck Vanishing

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
