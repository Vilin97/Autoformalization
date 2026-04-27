# Cycle 17 Results

## What was done

Deleted the unused `TopCat.Sheaf.*` convenience wrappers in
`Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean`, leaving the
still-used `TopCat.Presheaf.*` generated-subsheaf API intact.

Confirmed before editing that there were no external source references with:

```bash
rg -n 'TopCat\.Sheaf\.(SectionIndex|allSectionMap|allSectionMap_epi|finsetGeneratedSheaf|finsetGeneratorMap)\b' Aristotle/GrothendieckVanishing/main --glob '!GeneratedSubsheaf.lean'
```

## What changed

Deleted these declarations:

- `TopCat.Sheaf.SectionIndex`
- `TopCat.Sheaf.finsetGeneratorMap`
- `TopCat.Sheaf.finsetGeneratedSheaf`
- `TopCat.Sheaf.allSectionMap`
- `TopCat.Sheaf.allSectionMap_epi`

Also adjusted the module header comment so it no longer advertises the deleted
sheaf-level wrappers.

No downstream call-site rewrites were needed.

## Verification performed

```bash
lake env lean Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
lake env lean Aristotle/GrothendieckVanishing/main/ZeroOutsideFinset.lean
lake env lean Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean
lake build
```

All verification commands passed. `lake build` emitted only unrelated existing
linter warnings in other files.

## LOC

Normalized LOC from `python3.9 scripts/normalized_loc.py --per-file --raw`:

- Before: 5216
- After: 5185
- Delta: -31

Raw `wc -l Aristotle/GrothendieckVanishing/main/*.lean`:

- Before: 6174
- After: 6127
- Delta: -47

## What remains

Nothing remains for this cycle. The scoped unused sheaf-wrapper cluster was
removed, and the presheaf API plus `familyMap`/`familyImage` declarations were
left untouched.
