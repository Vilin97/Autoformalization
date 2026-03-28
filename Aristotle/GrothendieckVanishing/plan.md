# Work Plan — Grothendieck Vanishing

**Updated**: 2026-03-28T08:20Z

## Status Summary

- **Sorry count**: 3 (`admit`s in Setup.lean — must convert to `sorry`)
- **Files**: 9 in `main/`, all compiling
- **Aristotle jobs**: 6 in progress (flasque_injective at 5%, FlasqueVanishing at 12%, PlusObjIsSheaf at 48%, IrreducibleStep at 56%)
- **CI**: Latest run in progress, previous 2 passed

## This Cycle's Work Items

### 1. (P0) Convert `admit` → `sorry` in Setup.lean [/prove]
User mandates no axioms/admits. Convert all 3 admits to sorry. Fix docstrings.

### 2. (P2) Fix all stale documentation [/prove]
Update docstrings in Setup.lean, main.lean, GrothendieckVanishing.lean, IrreducibleStep.lean to replace "axiom" with "sorry" and remove "DO NOT PROVE" instructions.

### 3. (P1) Work on `flasque_injective` [/prove]
Bredon's theorem: flasque → injective in sheaf category. Aristotle job 99a8a5d6 at 5%.
**Strategy**: Try to prove directly using `injective_iff_subsingleton_ext_one`. If a flasque sheaf F has `Ext¹(Y, F) = 0` for all Y, then F is injective. This might be provable via the abstract Ext LES + flasque = Γ-acyclic approach.

### 4. Check Aristotle jobs [/check-aristotle]
6 jobs in progress. Priority: 55ef4f62 (IrreducibleStep, 56%) and 62f9f40c (PlusObjIsSheaf, 48%).

## Active Multi-Cycle Strategies

1. **Prove flasque_injective**: Hard Zorn argument OR injective_iff_subsingleton_ext_one approach. Aristotle backup.
2. **Build j_! infrastructure**: Needed for ReducibleVanishing and IrreduciblePosVanishing. No Aristotle job for this yet — consider decomposing and submitting.
3. **Reduce heartbeats**: toPlus_surjective_of_firstPlus at 1600000 needs decomposition.

## Backlog

- Generalize constantSheaf_flasque from ULift ℤ to arbitrary A
- PR CohomologyIso and subsingleton_ext_of_ses to Mathlib
- Generalize from AddCommGrpCat to ModuleCat R
