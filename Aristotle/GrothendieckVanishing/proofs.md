# Proof: cohomology_vanishing_of_finitelyGenerated_vanishing

## Statement
On a Noetherian space X, if H^m(K_S) = 0 for all finitely generated subsheaves K_S of K,
then H^m(K) = 0. Here H^m = Ext^m(Z_X, -) where Z_X is the constant sheaf.

## Key Insight
The general categorical statement `ext_comm_filtered_colimit_mono` (Ext^n preserves
filtered colimits of mono diagrams in Grothendieck abelian categories) is TOO GENERAL.
For sheaves, we have the crucial property that Gamma(X, colim F_i) = colim Gamma(X, F_i)
(filtered colimits of sheaves are computed objectwise). This gives us the n=0 base case
for free, and the inductive step uses dimension shifting via injective hulls.

## Proof by strong induction on m

**Base case m = 0:**
Sheaf.H K 0 = Ext^0(Z_X, K) ~ Hom(Z_X, K) ~ K(X) (global sections).
K = colim K_S (filtered colimit of subsheaves). Filtered colimits of sheaves are objectwise:
K(X) = colim K_S(X). Each K_S(X) is subsingleton => colim is subsingleton => K(X) subsingleton.

Key Mathlib facts needed:
- Ext.homEquiv_0 : Ext Z X 0 ~ (Z -> X)
- Hom(constantSheaf Z, F) ~ F(top) (constant sheaf-global sections adjunction)
- Filtered colimits of sheaves are objectwise

**Inductive step m -> m+1:**
Given: Ext^{m+1}(Z_X, K_S) = 0 for all S. Want: Ext^{m+1}(Z_X, K) = 0.

Choose an injective hull: 0 -> K -> I (exists in Grothendieck abelian category).
Set Q = I/K. Then 0 -> K -> I -> Q -> 0 is SES.

For each S: 0 -> K_S -> I -> I/K_S -> 0 is SES.
Dimension shift: Ext^{m+1}(Z_X, K_S) ~ Ext^m(Z_X, I/K_S) (since I injective).
So Ext^m(Z_X, I/K_S) = 0 for all S.

Key step: Q = I/K = I/colim(K_S) = colim(I/K_S) by AB5 (exactness of filtered colimits).
The diagram {I/K_S} is a filtered diagram (transitions need NOT be mono).

By the INDUCTIVE HYPOTHESIS (for m, applied to the diagram {I/K_S}):
Ext^m(Z_X, colim(I/K_S)) = 0, i.e., Ext^m(Z_X, Q) = 0.

From the SES 0 -> K -> I -> Q -> 0 and I injective:
subsingleton_ext_of_ses gives Ext^{m+1}(Z_X, K) subsingleton. QED.

## Implementation Plan

1. DELETE ext_comm_filtered_colimit_mono and its sub-lemmas (they are not needed)
2. REWRITE cohomology_vanishing_of_finitelyGenerated_vanishing with the inductive proof
3. The proof needs:
   - The filtered diagram infrastructure (finsetGenFunctor, finsetGenCocone, etc.) — KEEP
   - n=0 base: Sheaf.H specialization + objectwise colimit — NEW
   - Injective hull for the inductive step — from IsGrothendieckAbelian
   - AB5 for I/colim = colim(I/-) — from AB5OfSize
   - subsingleton_ext_of_ses — EXISTING (line 24)

4. Key new sub-lemma: for sheaves on a topological space,
   `Subsingleton (Sheaf.H (colim F_i) 0)` given `forall i, Subsingleton (Sheaf.H (F_i) 0)`.
   This is the n=0 base case using Gamma-colimit commutation.

5. The inductive hypothesis needs to be for GENERAL filtered diagrams (not just mono).
   So the theorem statement should drop the mono condition.
