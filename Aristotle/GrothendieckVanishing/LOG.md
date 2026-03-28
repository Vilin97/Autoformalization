# Log — Grothendieck Vanishing

## 2026-03-28T08:00Z — Cycle 14: constantSheaf_flasque PROVEN

**Sorry count: 2 mathematical + 1 axiom (down from 3+1)**

### MAJOR ACHIEVEMENT: constantSheaf_flasque_of_irreducible is SORRY-FREE

The constant sheaf on an irreducible space is flasque. Full proof chain:

1. **toPlus bijective** for constP at nonempty opens (surjective from Aristotle, injective manual)
2. **toPlus(plusObj P) surjective** at nonempty opens — KEY NEW LEMMA:
   - For each arrow I in a cover, x(I) = toPlus_{I.Y}(a) for a universal a
   - Proved via: Meq condition + naturality + injectivity at intersection (irreducible → nonempty)
   - Empty arrows handled by plusObj_bot_subsingleton
3. **toSheafify surjective** = composition of two surjective maps (via plusMap_toPlus)
4. **Naturality + epi_of_epi_fac**: toSheafify_V ≫ res = toSheafify_U → Epi(res)
5. **Type bridge**: sheafify ↔ constantSheaf via plusPlusIsoSheafify + simpa

Technical challenges overcome:
- `ConcreteCategory.hom` vs `FunLike.coe` coercion mismatches in rewrite tactics
- `S.shape.fst R` not reducing to `R.fst` (needed `change` tactic)
- `constantSheaf.val ≠ sheafify` definitionally (used `plusPlusIsoSheafify` iso bridge)

### Remaining sorry's (2 + axiom)
1. `grothendieck_reduction` (IrreducibleStep.lean:63): irreducible X, dim ≥ 1.
   Needs extension by zero (j_!) or closed-open SES + pushforward cohomology.
2. `sheaf_H_subsingleton_of_reducible` (ClosedOpenDecomposition.lean:112): reducible X.
   Needs j_! for decomposition into irreducible components.
3. `FlasqueVanishing` (Setup.lean:38): intentional axiom, NOT a sorry.

Both sorry's are blocked on j_! (extension by zero for open embeddings), which is NOT in Mathlib v4.28.

### Aristotle jobs
- b29fab4f: ReducibleCase — COMPLETE, documented j_! blocker
- 55ef4f62: IrreducibleStep — IN_PROGRESS (55%)
- 17b9bce9: ToSheafifySurjective — COMPLETE, integrated
- a60dddad: MeqConstant — COMPLETE, integrated

## 2026-03-28T06:15Z — Cycles 12-13: Massive infrastructure build

**Sorry count: 3 mathematical + 1 axiom**

### MAJOR ACHIEVEMENTS (sorry-free infrastructure)
Built by hand:
- **yonedaTopFreeIsoConst**: natural iso yoneda.obj ⊤ ⋙ free ≅ const(ULift ℤ)
- **freeAbSheafTopIsoConstantSheaf**: sheaf iso via presheafToSheaf.mapIso
- **extAddEquivOfIso**: Ext transport along sheaf iso via extFunctor
- **cohomologyPresheafTopEquiv**: H'(⊤, F, n) ≃+ H(F, n) — **RESOLVES MATHLIB TODO**
- **isIrreducible_of_nonempty_open**: nonempty opens in irreducible space are irreducible

From Aristotle:
- **topologicalKrullDim_lt** + **topologicalKrullDim_add_one_le**: dim strict inequality
- **meq_const_of_irreducible** / **meq_const_values_eq**: matching families constant
- **toPlus_surjective**: toPlus surjective at nonempty opens on irreducible X
- **cover_arrows_related**: all arrows in a cover are related (including empty!)

### Key mathematical insight
Empty arrows in covers DON'T break the matching family argument: for I with I.Y = ⊥
and any nonempty J, a relation through Z = ⊥ (initial) forces x(I) = x(J) by the
Meq condition + constant presheaf identity maps.
