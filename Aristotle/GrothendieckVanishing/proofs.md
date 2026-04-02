# Proof: cohomology_vanishing_of_finitelyGenerated_vanishing

## Statement
On a Noetherian space X, if H^m(K_S) = 0 for all finitely generated subsheaves K_S of K,
then H^m(K) = 0. Here H^m = Ext^m(Z_X, -) where Z_X is the constant sheaf.

## Current Status

**1 sorry remains**: `ext_comm_filtered_colimit_mono` in IrreducibleStep.lean.

This sorry encodes: in a Grothendieck abelian category, Ext^n(Z, -) preserves
filtered colimits of monomorphism diagrams. Equivalently, for sheaves on a
Noetherian space, H^n commutes with filtered colimits (Hartshorne III Lemma 2.9).

## Why this is hard (analysis of failed approaches)

### Approach 1: Dimension shifting by induction on n
- **Base case (n=0)**: WORKS. Hom(Z_X, colim F_i) ≅ Γ(colim F_i) = colim Γ(F_i)
  because filtered colimits of sheaves are objectwise.
- **Inductive step (n→n+1)**: Embed colim ↪ I (injective), form quotient Q = I/colim.
  By AB5: Q = colim(I/F_j). The quotient diagram has EPI transitions (not mono).
  Applying the IH at degree n to the quotient requires the IH for ARBITRARY filtered
  diagrams (not just mono). This creates a new problem:
  - For n≥1 WITHOUT mono transitions: can't form individual SES's for pieces
    (Y_j → colim → I might not be mono if Y_j → colim is not mono).
  - For n=0 WITHOUT mono: works (objectwise colimits).
  - So the induction BREAKS at degree 2: need degree 1 for the quotient (epi transitions),
    which needs degree 0 for the double-quotient (works), BUT forming the double-quotient
    requires mono embeddings that the epi-transition quotient doesn't provide.

### Approach 2: Specializing to sheaves + Γ-surjectivity
- For n=1 specifically: can prove directly using surjectivity of Γ(I) → Γ(Q_j)
  (from H^1(Y_j)=0 and the LES) combined with objectwise colimits.
- For n≥2: the recursive reduction to n=1 fails because quotient diagrams
  have epi transitions and we can't form SES's for their subsheaves.

### Approach 3: Cardinal-filtered colimit preservation
- Mathlib has `preservesColimit_coyoneda_obj_of_mono` requiring `IsCardinalFiltered J κ`
  and `HasCardinalLT (Subobject Z) κ` for a regular κ.
- For our J = Finset(SectionIndex K): only ℵ₀-filtered (IsFiltered), not κ-filtered
  for κ > ℵ₀. And Subobject(constantSheaf ℤ) is infinite. So κ = ℵ₀ is too small.
- **Cardinal conditions cannot be satisfied for this application.**

### Fundamental Obstacle
All dimension-shifting approaches fail because:
**Cohomological vanishing for a sheaf does NOT propagate to its subsheaves.**
From H^k(A) = 0 and B ↪ A, one CANNOT conclude H^k(B) = 0.

The correct proof of Hartshorne III.2.9 requires either:
(a) Čech cohomology (finite covers commute with filtered colimits), or
(b) Universal δ-functor theorem (effaceable functors), or
(c) Functorial flasque/Godement resolution (commutes with filtered colimits)
None of these are in Mathlib v4.28.0.

## What IS proved

### Degree cascade (NEW, in GrothendieckVanishing.lean)
`sheafH_vanishing_succ`: If H^m(F) = 0 for ALL F at degree m, then H^{m+1}(F) = 0 for all F.
`sheafH_vanishing_cascade`: Extends from one degree to all higher degrees.

This means: once we establish vanishing at the MINIMUM degree (dim+1) for ALL sheaves,
all higher degrees follow automatically WITHOUT the colimit step. The colimit step is
only needed at degree dim+1.

### Filtered diagram infrastructure (PROVED, in IrreducibleStep.lean)
- `finsetGenFunctor`: functor Finset(SectionIndex K) ⥤ Sheaf(X)
- `finsetGenCocone`: cocone with vertex K
- `finsetGenCocone_isColimit`: K is the colimit
- `finsetGenFunctor_mono`: transition maps are mono

## Paths to closing the sorry

### Path A: Build Čech cohomology infrastructure
- Define Čech complex for finite open covers
- Prove Čech cohomology commutes with filtered colimits (uses finite intersections)
- Prove Čech = derived functor cohomology on Noetherian spaces
- **Effort: ~500+ lines, requires substantial new Mathlib infrastructure**

### Path B: Universal δ-functor theorem
- Define universal δ-functors in Lean
- Prove effaceability implies universality
- Show the filtered-colimit Ext functor is effaceable
- **Effort: ~300+ lines, requires abstract homological algebra**

### Path C: Godement resolution
- Define the Godement resolution G^n(F) = ∏_x F_x (product over stalks)
- Prove it's functorial and flasque
- Prove it commutes with filtered colimits (stalkwise computation)
- **Effort: ~400+ lines, requires stalk theory**

### Path D: Wait for Mathlib
- The theorem `Ext^n commutes with filtered colimits` is a standard result
  that may eventually be added to Mathlib as part of the derived category infrastructure.
