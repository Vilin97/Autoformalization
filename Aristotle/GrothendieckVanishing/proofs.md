# Natural-Language Guide for the Remaining `sorry`s

This file is meant to guide the prover work on the *current* live development in
`Aristotle/GrothendieckVanishing/main/`.

It is based on:
- the actual remaining `sorry`s in `main/Setup.lean` after the `SetupCore` split,
- Hartshorne III.2, especially Theorem 2.7 and the proof on textbook pages 210-211
  in `context/Hartshorne_3_2.pdf`,
- the infrastructure already present in this repo, in particular
  `ClosedImmersion.lean`, `ZeroOutside.lean`, and `ReducibleVanishing.lean`.

## Current Status

As of the live source checked on 2026-03-29, there is only **one** actual
`sorry` left in the main development:

1. `Setup.lean:95`

The reducible-case duplicate that used to live in `Setup.lean` has been removed.
The file split is now:

- `SetupCore.lean`: the shared core (`FlasqueVanishing`,
  `PushforwardHVanishing`, `ClosedImmersionSES`, instances, etc.),
- `ReducibleVanishing.lean`: the finished reducible-case proof,
- `Setup.lean`: a thin wrapper that re-exports `ReducibleVanishing` and keeps
  only the genuine remaining gap `IrreduciblePosVanishing`.

There is **no remaining `sorry` in `FlasqueVanishing`** or
`PushforwardHVanishing`, and there are no longer any fake reducible-case
`sorry`s in `Setup.lean`.

## Hartshorne's Proof Skeleton

The reference is Hartshorne, Chapter III, Section 2:

- Proposition 2.5: flasque sheaves are acyclic.
- Lemma 2.8: on a noetherian space, direct limits of flasque sheaves are flasque.
- Proposition 2.9: on a noetherian space, cohomology commutes with direct limits.
- Lemma 2.10: if `j : Y ↪ X` is a closed immersion, then `H^i(Y,F) = H^i(X,j_*F)`.
- Theorem 2.7: if `dim X = n`, then `H^i(X,F)=0` for all `i > n`.

Hartshorne proves Theorem 2.7 by three reductions:

1. Reducible `X`: peel off irreducible components one at a time.
2. Irreducible `X` with `dim X = 0`: the only nonempty open is `X`, so global
   sections are exact and higher cohomology vanishes.
3. Irreducible `X` with `dim X > 0`: use finitely generated subsheaves,
   reduce to a quotient of `Z_U`, then reduce subsheaves of `Z_U` to smaller
   closed subsets.

The live formalization already has:

- the dimension-0 case,
- the closed-immersion pushforward vanishing tool
  `PushforwardHVanishing`,
- the constant-sheaf flasque result on irreducible spaces,
- `zeroOutsideInt U`, which is the formal stand-in for Hartshorne's `Z_U`.

What is still missing is the actual formal execution of Hartshorne's Steps 3-5.

## The Old Reducible-Case `sorry`s

Historically, `Setup.lean` contained three local reducible-case `sorry`s.
Those no longer exist in the live file, but it is still useful to record why
they were routine and why the correct home for them is
`main/ReducibleVanishing.lean`.

### 1. `Setup.lean:1083`

This is the base case of the induction on the finite set of irreducible
components:

> if a sheaf `G` has zero stalks at every point of `X`, then `H^n(X,G)=0`.

This is already proved in `ReducibleVanishing.lean` in two steps:

1. `sheaf_isZero_of_zero_stalks`
2. `subsingleton_sheafH_of_isZero'`

The natural-language proof is:

- If every stalk of `G` is zero, then every section is locally zero.
- By stalkwise extensionality for sheaves of abelian groups, every section over
  every open set is zero.
- Hence every object `G(U)` is a subsingleton, so `G` is the zero sheaf,
  i.e. `IsZero G`.
- Ext groups into an `IsZero` object are zero, hence `Sheaf.H G n` is a
  subsingleton.

This is completely standard and already formalized. The right move is not to
re-prove it again in `Setup.lean`, but to reuse or inline the finished proof
from `ReducibleVanishing.lean`.

### 2. `Setup.lean:1103`

This is the branch `x ∈ Z` inside the reducible case.

The short exact sequence is

`0 → K → G → i_* i^* G → 0`

coming from the adjunction unit for the closed immersion `i : Z ↪ X`.

At a point `x ∈ Z`, the stalk map

`G_x → (i_* i^* G)_x`

is an isomorphism. This is exactly
`TopCat.closedIncl_unit_stalk_isIso`.

Therefore:

- the composite `K_x → G_x → (i_* i^* G)_x` is zero because `K` is the kernel,
- the second map is an isomorphism, hence in particular a monomorphism,
- so `K_x → G_x` is zero,
- but `K_x → G_x` is also mono because stalk functors preserve monos,
- therefore `K_x = 0`.

The local formal helper for exactly this argument is already present:

- `stalk_zero_of_ses_g_iso` in `ReducibleVanishing.lean`.

So the correct implementation is just the existing proof pattern from
`ReducibleVanishing'.lean`.

### 3. `Setup.lean:1105`

This is the branch `x ∉ Z` and also outside the union of the remaining
components.

The hypothesis of the outer induction gives `G_x = 0` there. Since

`K_x → G_x`

is mono, and the target is zero, the source must be zero.

Again, this is already done in `ReducibleVanishing.lean`. The proof is:

- convert the stalk of `G` into an `IsZero` object using the hypothesis,
- use that the stalk functor preserves monos,
- a monomorphism into a zero object forces the source to be zero.

So the three reducible-case `sorry`s are not mathematically open problems.
They should be replaced by the existing proof in `ReducibleVanishing'.lean`,
or the theorem in `Setup.lean` should simply delegate to that file.

## The Real Remaining Problem: `IrreduciblePosVanishing`

The serious gap is `Setup.lean:1185`.

The current comments in `Setup.lean` try to argue as follows:

- choose a proper closed subset `Z ⊊ X`,
- form `0 → K → F → i_* i^*F → 0`,
- note that `K` has zero stalks on `Z`,
- conclude that `supp(K) ⊊ X`,
- then apply the induction hypothesis to `supp(K)`.

This is **not correct**.

### Why the Current Support Argument Fails

From `K_x = 0` for `x ∈ Z`, one only gets

`supp(K) ⊆ X \ Z`.

But when `X` is irreducible and `Z ⊊ X` is closed, the open set `X \ Z` is
typically dense and has the **same** dimension as `X`. So one cannot conclude:

- `supp(K)` is a proper closed subset of `X`, or
- `dim supp(K) < dim X`.

In fact, the closure of `supp(K)` may well be all of `X`.

So this branch cannot be finished by "support of the kernel is smaller" alone.
That is exactly why Hartshorne does **not** prove the irreducible case by the
same closed-immersion kernel argument used in the reducible case.

## Correct Proof of the Irreducible Positive-Dimensional Case

Here is the right argument, following Hartshorne III.2.7, Steps 3-5.

To avoid clashing notation with the fixed Lean parameter `n`, write:

- `d := dim X`
- `m` for the cohomological degree, with `m > d`

The goal is: for irreducible noetherian `X` with `d > 0`,
show `H^m(X,F)=0` for every sheaf `F`.

### Step 3A: Reduce to finitely generated subsheaves

Let

- `B := ⋃_{U open} F(U)`, the set of all local sections of `F`,
- `A :=` the set of finite subsets of `B`.

For each finite subset `α ⊆ B`, let `F_α` be the subsheaf of `F` generated by
the sections in `α`.

Then:

- the family `(F_α)` is directed under inclusion,
- `F = colim F_α` as a sheaf,
- by Hartshorne Proposition 2.9,
  `H^m(X,F) ≅ colim H^m(X,F_α)`.

Therefore it is enough to prove vanishing for each `F_α`, i.e. for sheaves
generated by finitely many sections.

This is the first major missing formal ingredient. It requires the direct-limit
machinery from Hartshorne 2.8-2.9, not just the current closed-immersion tools.

### Step 3B: Reduce from finitely many generators to one generator

Now assume `F` is generated by finitely many sections.
Induct on the number of generators.

If `α` is nonempty and `x ∈ α`, let `F_x` be the subsheaf generated by the single
section `x`, and let `F'` be the subsheaf generated by `α \ {x}`.
Then there is an exact sequence

`0 → F' → F → F/F' → 0`

and `F/F'` is generated by the image of the single section `x`.

So by the long exact sequence, if one can prove vanishing for:

- sheaves generated by fewer sections, and
- sheaves generated by one section,

then one gets vanishing for `F`.

Thus the problem reduces to the case where `F` is generated by a single section
`s ∈ F(U)` on some open set `U`.

### Step 3C: A singly generated sheaf is a quotient of `Z_U`

Assume `F` is generated by one section `s ∈ F(U)`.
Let `Z_U` denote the constant sheaf `Z` on `U`, extended by zero outside `U`.

In this repo, the correct formal object is

- `TopCat.Sheaf.zeroOutsideInt U`.

The section `s` defines a morphism

`Z_U → F`

using the universal property of the sheaf generated by one local section. In the
current repo, the obvious formal candidate is

- `TopCat.Sheaf.zeroOutsideInt.sHom s`.

If `F` is *the subsheaf generated by `s`*, then this map is an epimorphism.
Let `R` be its kernel. Then we have an exact sequence

`0 → R → Z_U → F → 0`.

By the long exact sequence, to prove `H^m(X,F)=0` it is enough to prove:

- `H^m(X,Z_U)=0`,
- `H^m(X,R)=0`.

This is exactly Hartshorne's reduction.

### Step 4: Subsheaaves of `Z_U`

Now let `R` be any subsheaf of `Z_U`.
Hartshorne proves that vanishing for `R` can be reduced to vanishing for some
smaller `Z_V`.

There are two cases.

#### Case 4.1: `R = 0`

Then there is nothing to prove.

#### Case 4.2: `R ≠ 0`

For each `x ∈ U`, the stalk `R_x` is a subgroup of `Z`, so it has the form
`d_x Z` for a unique integer `d_x ≥ 0`.

Because `R ≠ 0`, there exists some stalk where `d_x > 0`.
Let `d` be the least positive integer that occurs among the nonzero stalks.

Hartshorne's claim is that there exists a nonempty open subset `V ⊆ U` such that

`R|_V = d Z|_V`

as a subsheaf of `Z|_V`.

Intuitively:

- pick `x ∈ U` with `R_x = dZ`,
- choose a germ represented by a section equal to `d` at `x`,
- because `d` was chosen minimal, after shrinking around `x` that section
  generates the whole subsheaf `R` locally,
- on that smaller open `V`, the subsheaf becomes the principal subgroup sheaf
  `dZ`.

Since multiplication by `d` is an isomorphism `Z_V ≅ dZ_V`, this yields

`R_V ≅ Z_V`.

Here `R_V` means Hartshorne's notation for `R` extended by zero from `V`;
formally it is again a `zeroOutsideInt` construction on `V`.

Then there is an exact sequence

`0 → R_V → R → R / R_V → 0`.

The quotient `R / R_V` is supported on the closed subset `closure(U \ V)`.
Because `X` is irreducible and `V` is nonempty open, `closure(U \ V)` is a
proper closed subset of `X`, hence has dimension `< d`.

Now apply Hartshorne Lemma 2.10 plus the induction hypothesis:

- any sheaf supported on that proper closed subset may be regarded as a
  pushforward from the closed subspace,
- therefore its `m`-th cohomology vanishes because `m > d > dim(closure(U \ V))`.

In this repo, the weaker vanishing form of Lemma 2.10 is already available as
`PushforwardHVanishing`, so one does not need the full isomorphism of cohomology
groups here, only the vanishing transfer.

Therefore `H^m(X, R / R_V)=0`.
By the long exact sequence, to prove `H^m(X,R)=0` it is enough to prove
`H^m(X,R_V)=0`, and since `R_V ≅ Z_V`, it is enough to prove
`H^m(X,Z_V)=0`.

So Step 4 reduces vanishing for arbitrary subsheaves of `Z_U` to Step 5.

### Step 5: Vanishing for `Z_U`

Now let `U ⊆ X` be open.
We must prove `H^m(X,Z_U)=0`.

If `U = ∅`, then `Z_U = 0`, so this is trivial.

Assume `U ≠ ∅`. Let `Y := X \ U`, a proper closed subset of `X`.
There is an exact sequence

`0 → Z_U → Z → Z_Y → 0`

where:

- `Z` is the constant sheaf on `X`,
- `Z_Y` is the extension by zero of the constant sheaf on the closed subset `Y`.

Now:

1. `dim Y < d` because `X` is irreducible and `Y` is a proper closed subset.
2. `H^m(X,Z)=0` because the constant sheaf on an irreducible space is flasque,
   and flasque sheaves are acyclic.
3. `H^{m-1}(X,Z_Y)=0` because `m-1 > dim Y` and `Z_Y` is a pushforward from
   the smaller closed space `Y`; this is exactly the place to use the
   induction hypothesis plus `PushforwardHVanishing`.

Therefore, from the long exact sequence,

`H^m(X,Z_U)=0`.

This completes Step 5, hence Step 4, hence the singly generated case, hence the
finitely generated case, and finally the general case by Proposition 2.9.

## What This Means for the Lean Work

The mathematically correct plan is now clear.

### What can be closed immediately

The three reducible-case `sorry`s in `Setup.lean` should be replaced from
`ReducibleVanishing.lean`. No new mathematics is needed there.

### What still has to be built

To finish `IrreduciblePosVanishing` honestly, the project still needs formal
versions of the following ingredients.

1. **Direct-limit reduction**
   - a formal directed system of finitely generated subsheaves,
   - a proof that the colimit is the original sheaf,
   - the Hartshorne 2.8/2.9 commutation of cohomology with direct limits.

2. **Single-generator quotient**
   - define the subsheaf generated by one section,
   - prove the canonical map `zeroOutsideInt U ⟶ F` is epi onto that subsheaf.

3. **Step 4 local structure**
   - for a nonzero subsheaf `R ⊆ Z_U`, construct the minimal positive integer `d`,
   - show after shrinking to some nonempty `V ⊆ U`, one has `R|_V = dZ|_V`,
   - conclude `R_V ≅ Z_V`.

4. **Closed-support reduction**
   - identify sheaves supported on a proper closed subset with pushforwards from
     the closed subspace,
   - use the already-proved `PushforwardHVanishing` to transfer vanishing from
     the smaller closed space to `X`.

The repo already contains useful pieces for this:

- `ZeroOutside.lean` gives the formal `Z_U` object and its generator map.
- `ClosedImmersion.lean` gives the closed-immersion counit/stalk comparison.
- `PushforwardHVanishing` gives the vanishing form of Hartshorne 2.10.
- `ConstantSheafFlasque.lean` gives acyclicity of the constant sheaf on an
  irreducible space once `FlasqueVanishing` is available.

## Bottom Line

The current `proofs.md` should guide the provers as follows:

- Do **not** spend time inventing new arguments for `Setup.lean:1083`,
  `1103`, or `1105`. Those are already solved in `ReducibleVanishing.lean`.
- Do **not** try to finish `IrreduciblePosVanishing` by the current
  "kernel supported on a smaller closed subset" comments in `Setup.lean`;
  that argument is not valid on an irreducible space.
- The correct route is Hartshorne III.2.7, Steps 3-5, implemented using
  `zeroOutsideInt`, direct limits, and closed-support pushforward vanishing.
