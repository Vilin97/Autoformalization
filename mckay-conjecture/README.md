# The McKay Conjecture

This Lean 4 package formalizes the statement of the McKay conjecture for
ordinary irreducible complex characters.

For a finite group `G`, a prime `p`, and a Sylow `p`-subgroup `P`, let
`Irr_{p'}(G)` be the irreducible complex characters of `G` whose degrees are not
divisible by `p`. The conjecture asserts

```text
|Irr_{p'}(G)| = |Irr_{p'}(N_G(P))|.
```

The package is pinned to mathlib commit
`9cebae57f419f984d008f357605b2621a1d9f13b` (Lean `v4.33.0-rc1`), which was the
tip of mathlib's `master` branch when the project was created on 2026-07-25.

## Layout

- `McKayConjecture/IrreducibleCharacter.lean` defines ordinary irreducible
  complex characters and the `p'`-degree condition.
- `McKayConjecture/Statement.lean` defines the Sylow normalizer and the
  proposition `McKayConjecture.Statement`.

## Build

```bash
lake exe cache get
lake build
```

The first milestone contains only the audited proposition; it does not assume
the conjecture as an axiom or hide an unfinished proof behind `sorry`.
