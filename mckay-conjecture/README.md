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
`12ab8e82f8447fa639dabe9ffeda74436b72be31` (Lean `v4.33.0-rc1`), which was the
tip of mathlib's `master` branch when the dependency pin was refreshed on
2026-07-29.

## Layout

- `McKayConjecture/IrreducibleCharacter.lean` defines ordinary irreducible
  complex characters and the `p'`-degree condition.
- `McKayConjecture/Statement.lean` defines the Sylow normalizer and the
  proposition `McKayConjecture.Statement`.
- `docs/mckay_proof.tex` gives a detailed natural-language proof certificate,
  including the exact reduction and final type-`D` theorem chain.
- `docs/formalization_blueprint.tex` audits existing Lean coverage and divides
  the complete formalization into named modules and compilation gates.
- `docs/references.bib` records the primary mathematical and Lean sources.

## Build

```bash
lake exe cache get
lake build
```

To build the documents:

```bash
cd docs
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../output/pdf mckay_proof.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../output/pdf formalization_blueprint.tex
```

The package now contains the ordinary-character infrastructure, numerical
normalizer induction, a conditional central-scalar Rossi reduction, and
substantial finite computations including the complete ordinary table of the
canonical sixfold cover of `A₆`. It does not yet export an unconditional proof
of the general theorem. The optimized proof-facing boundary keeps the ordinary
fixed-character count
`CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis`
separate from the automatic prime-to-`q` degree theorem
`CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis`. Their
checked composition supplies
`CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis` and the
existing conditional final reduction. The remaining per-parameter count,
automatic-degree proof, and CFSG family inputs stay explicit rather than being
hidden behind axioms or unfinished proofs.
