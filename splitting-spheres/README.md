# Splitting spheres for unlinked 2-spheres in S4

This project formalizes Alison Tatsuoka's paper
[*Splitting spheres for unlinked S2's in S4*](https://arxiv.org/abs/2502.01817).

The frozen main proposition is [`SplittingSpheres.MainTheorem`](SplittingSpheres/Statement.lean).
It uses an explicit coordinate representative of the two-component `2`-sphere unlink in the
unit `4`-sphere and asserts an infinite family of smooth splitting `3`-spheres that are pairwise
non-isotopic in the unlink complement. Two independent adversarial reviews checked the topology,
smooth category, parameterization invariance, non-vacuity, and the relevant Mathlib APIs before
the statement was frozen.

The proof formalization is in progress. The statement checkpoint contains no project-local
`sorry`, axioms, or proof placeholders.

## Build

From this directory:

```bash
lake build
```

The project pins its Lean toolchain and its TauCeti dependency in `lean-toolchain` and
`lake-manifest.json`.
