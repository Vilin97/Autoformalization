# Natural Language Proofs of Remaining Sorry's

Following Hartshorne III, Section 2, Theorem 2.7 and its proof.

## Overview

**Theorem (Grothendieck Vanishing, Hartshorne III.2.7).** Let X be a Noetherian
topological space of dimension n. Then for all sheaves F of abelian groups on X
and all i > n, we have H^i(X, F) = 0.

The proof proceeds by induction on dim X. There are three cases:
1. **Reducible case (Step 1):** Reduce to irreducible X via induction on the number of irreducible components.
2. **Irreducible dim 0 (Step 2):** Γ is an exact functor, so all higher cohomology vanishes.
3. **Irreducible dim ≥ 1 (Steps 3–5):** Use the constant sheaf Z_U and noetherian induction.

Cases 1 (modulo one sorry) and 2 are proved. Case 3 has one sorry. There are also
sorry's in PushforwardHVanishing (degree 1) and ReducibleVanishing (stalk computation).

---

## Sorry 1: `PushforwardHVanishing` degree 1 (Setup.lean:798)

**Statement.** Let i : Z ↪ X be a closed immersion of Noetherian spaces. If
Subsingleton(H^1(Z, G)) then Subsingleton(H^1(X, i_*G)).

**Context.** The n ≥ 2 case is proved by LES + FlasqueVanishing + dimension shift.
The n = 0 case is proved by Γ comparison. Only n = 1 remains.

**Proof (Hartshorne, Lemma 2.10 + Proposition 2.5).**

i_* is exact for closed immersions (already proved as `closedIncl_pushforward_shortExact`).
The key insight is that since i_* is exact AND maps injectives to flasques (already proved),
it maps injective resolutions to flasque resolutions.

Take an injective resolution 0 → G → J → R → 0 on Z. Then:
- 0 → i_*G → i_*J → i_*R → 0 is exact on X (by exactness of i_*).
- i_*J is flasque (injective sheaves are flasque, and i_* preserves flasqueness for closed immersions — in fact i_*J is flasque because the restriction maps of J are surjective, and pulling back along i preserves this).
- Since i_*J is flasque, H^1(X, i_*J) = 0 by FlasqueVanishing.

From the long exact sequence on X:
  Γ(i_*J) → Γ(i_*R) → H^1(X, i_*G) → H^1(X, i_*J) = 0

So H^1(X, i_*G) = coker(Γ(X, i_*J) → Γ(X, i_*R)).

From the long exact sequence on Z:
  Γ(Z, J) → Γ(Z, R) → H^1(Z, G) → H^1(Z, J) = 0

So H^1(Z, G) = coker(Γ(Z, J) → Γ(Z, R)).

Now, Γ(X, i_*G) = G(i⁻¹(X)) = G(Z) = Γ(Z, G) by definition of pushforward.
More precisely, (Opens.map i).obj ⊤ = ⊤, so Γ_X ∘ i_* = Γ_Z naturally.

Therefore coker(Γ(X, i_*J) → Γ(X, i_*R)) = coker(Γ(Z, J) → Γ(Z, R)),
and H^1(X, i_*G) ≅ H^1(Z, G). If the latter is a subsingleton, so is the former.

**Formalization approach.** Rather than comparing cokernels (which requires naturality
of the Γ iso), use the existing LES machinery directly:

Since i_*J is flasque, H^1(X, i_*J) = 0. By the LES, any a ∈ H^1(X, i_*G) lifts to
c ∈ H^0(X, i_*R) = H^0(Z, R). The map Γ(i_*J) → Γ(i_*R) factors through
Γ(J) → Γ(R) (via the Γ equality). If H^1(Z, G) = 0 then Γ(J) → Γ(R) is surjective,
hence Γ(i_*J) → Γ(i_*R) is surjective, hence H^1(X, i_*G) = 0.

Alternatively: the same LES argument used for n ≥ 2 works for n = 1 if we set m = -1.
The pattern: "a lifts from H^n to H^{n-1} of the quotient, then
Subsingleton(H^{n-1}(R)) by induction" — for n = 1 we need Subsingleton(H^0(R))
which follows from H^1(G) = 0 + exactness of the Γ sequence (i.e., surjectivity of
Γ(J) → Γ(R) follows from flasqueness of J). This is exactly what FlasqueVanishing proves
at the base case.

In fact the simplest approach: for n = 1, use the *same* pattern as n ≥ 2.
The pushed-forward SES 0 → i_*G → i_*J → i_*R → 0 is exact, i_*J is flasque,
so H^1(i_*J) = 0. By LES, H^1(i_*G) injects into H^0(i_*R)/im(H^0(i_*J)).
But H^0(i_*R) = Γ(R) and H^0(i_*J) = Γ(J), and Γ(J) → Γ(R) is surjective
(from flasqueness of J + exactness of evaluated SES — this is epi_app_of_shortExact_flasque).
So H^0(i_*R)/im(H^0(i_*J)) = 0, hence H^1(i_*G) = 0.

Wait — this doesn't use the hypothesis Subsingleton(H^1(G))! Let's reconsider.
The pushed-forward SES approach gives H^1(i_*G) ≅ H^1(G) unconditionally?
No — Γ(J) → Γ(R) surjective requires J flasque on Z (which it is, since injective → flasque).
And the pushed-forward SES being exact requires i_* exact (proved).

Actually: the LES on X from 0 → i_*G → i_*J → i_*R → 0 gives:
  H^0(i_*J) → H^0(i_*R) → H^1(i_*G) → H^1(i_*J) = 0

The map H^0(i_*J) → H^0(i_*R) is Γ(i_*J) → Γ(i_*R) = Γ(J) → Γ(R).
Is this surjective? Yes, because J is flasque on Z, the SES 0 → G → J → R → 0
is exact on Z, and epi_app_of_shortExact_flasque gives Γ(J) → Γ(R) surjective
(using flasqueness of G? No — flasqueness of X₁ = G, which we don't know!).

Hmm, epi_app_of_shortExact_flasque needs *X₁* (= G) flasque, not X₂ (= J).
So the "Γ(J) → Γ(R) surjective" is not immediate from our existing lemma.

**Correct approach:** The degree 1 case truly needs the hypothesis.
From the LES on Z: Γ(J) → Γ(R) → H^1(G) → 0. So if H^1(G) = 0, then Γ(J) → Γ(R)
is surjective. Via the Γ equality, Γ(i_*J) → Γ(i_*R) is surjective. From the LES on X:
H^1(i_*G) = coker of a surjection = 0.

**Formal plan:** Use Ext.covariant_sequence_exact₃ (the connecting map).
For the SES 0 → i_*G → i_*J → i_*R → 0 with i_*J flasque:
- Any a ∈ Ext(Z', i_*G, 1) maps to Ext(Z', i_*J, 1) = 0 (FlasqueVanishing).
- By covariant_sequence_exact₃: a = δ(c) for some c ∈ Ext(Z', i_*R, 0).
- Need: every c ∈ Ext(Z', i_*R, 0) is in the image of Ext(Z', i_*J, 0) → Ext(Z', i_*R, 0).
  i.e., the map H^0(i_*J) → H^0(i_*R) is surjective in the Ext sense.
  This is equivalent to epi_app at ⊤ (for Z' = constant sheaf), i.e., Γ(i_*J) → Γ(i_*R) surjective.
  Use: Γ(i_*J) = Γ(J), Γ(i_*R) = Γ(R), and Subsingleton(H^1(G)) implies surjectivity.

---

## Sorry 2: `ReducibleVanishing` base case (Setup.lean:984)

**Statement.** If G has zero stalks everywhere (∀ x, G_x = 0), then H^n(X, G) = 0.

**Proof.** A sheaf with all zero stalks is the zero sheaf (IsZero).
For an IsZero object G, Ext(Z, G, n) = 0 for any Z and n.

This is already proved in ReducibleVanishing.lean as `sheaf_isZero_of_zero_stalks` +
`subsingleton_sheafH_of_isZero'`. The sorry in Setup.lean is a *duplicate* —
the ReducibleVanishing.lean file already contains the complete proof of
ReducibleVanishing' which replaces the sorry'd ReducibleVanishing in Setup.lean.

**Formal plan:** The ReducibleVanishing' in ReducibleVanishing.lean handles this case
correctly via `sheaf_isZero_of_zero_stalks` + `subsingleton_sheafH_of_isZero'`.
The Setup.lean sorry can be replaced by delegating to ReducibleVanishing'.
However, ReducibleVanishing' itself has one sorry (sorry 3 below).

---

## Sorry 3: `ReducibleVanishing` stalk at x ∈ Z (ReducibleVanishing.lean:153 / Setup.lean:1004)

**Statement.** In the SES 0 → K → F → i_*(i^*F) → 0 from ClosedImmersionSES, if x ∈ Z
then the stalk K_x = 0.

**Proof (Hartshorne, Step 1).**
The map F → i_*(i^*F) is the adjunction unit η. At a point x ∈ Z, the stalk map
η_x : F_x → (i_*(i^*F))_x is an isomorphism (this is `closedIncl_unit_stalk_isIso`,
already proved). Since K = ker(η), and η_x is an iso (hence mono), K_x = 0.

More precisely: K_x → F_x is mono (K → F is mono in the SES, and the stalk functor
preserves monos). And F_x → (i_*i^*F)_x is an iso. The composition K_x → F_x → (i_*i^*F)_x
is zero (since K → F → i_*i^*F is zero in the SES). Since the second map is an iso,
the first map is zero. Since it is also mono, K_x = 0.

This is exactly what `stalk_zero_of_ses_g_iso` proves in ReducibleVanishing.lean!
The sorry bridges the fact that S.g from ClosedImmersionSES is definitionally equal
to adj.unit.app G, and `closedIncl_unit_stalk_isIso` gives the iso on stalks.

**Formal plan:** Provide the IsIso instance for the stalk of S.g at x ∈ Z.
S.g = adj.unit.app G (by construction in ClosedImmersionSES).
The stalk map T.map S.g.val = T.map (adj.unit.app G).val.
By `closedIncl_unit_stalk_isIso`, T.map (adj.unit.app G).val is an iso at x ∈ Z.
Then apply `stalk_zero_of_ses_g_iso`.

---

## Sorry 4: `ReducibleVanishing` stalk at x ∉ Z (Setup.lean:1006)

**Statement.** In the SES 0 → K → F → i_*(i^*F) → 0, if x ∉ Z and x ∉ ⋃s (so F_x = 0
by hypothesis), then K_x = 0.

**Proof.** K → F is mono. The stalk functor preserves monos. So K_x → F_x is mono.
But F_x = 0 (by hypothesis hG_stalks). A mono from K_x to 0 forces K_x = 0.

This is already proved in the `· else` branch of ReducibleVanishing.lean (lines 154–167).
The sorry in Setup.lean:1006 is only in the *duplicate* proof in Setup.lean;
ReducibleVanishing.lean handles this case.

---

## Sorry 5: `IrreduciblePosVanishing` kernel vanishing (Setup.lean:1086)

**Statement.** For irreducible X with dim ≥ 1 and the SES 0 → K → F → i_*(i^*F) → 0
where Z ⊊ X is a proper closed subset, show Subsingleton(H^n(X, K)).

**Context.** K = ker(η : F → i_*i^*F). The kernel K has zero stalks on Z (by sorry 3),
but supp(K) ⊆ X \ Z with closure(X \ Z) = X (since X is irreducible and Z ⊊ X).
So we CANNOT transfer K to a smaller space and use the induction hypothesis.

**Proof (Hartshorne, Steps 3–5).**

Hartshorne's proof does NOT use the ClosedImmersionSES approach for the irreducible case.
Instead, Steps 3–5 use the constant sheaf Z and subsheaves generated by sections:

**Step 3.** Let X be irreducible of dimension n, and let F ∈ Ab(X). Let
B = ∪_{U⊆X} F(U), and let A be the set of all finite subsets of B. For each α ∈ A,
let F_α be the subsheaf of F generated by the sections in α. Then F = lim F_α
(directed system). By Proposition 2.9 (cohomology commutes with direct limits on
Noetherian spaces), H^i(X, F) = lim H^i(X, F_α). So it suffices to show
H^i(X, F_α) = 0 for each F_α, i.e., reduce to the case where F is generated by
finitely many sections over various open sets.

**Step 4.** If F_α is generated by a single section s ∈ F(U), then F is a quotient
of Z_U (the constant sheaf Z extended by zero from U). We have a surjection
Z_U → F with kernel R. The SES 0 → R → Z_U → F → 0 gives:
H^i(X, Z_U) → H^i(X, F) → H^{i+1}(X, R).
Z is flasque on X (irreducible!), so H^i(X, Z) = 0 for i > 0.
The sheaf R/Z_V is supported on (U − V)⁻ which has dim < n since X is irreducible.
By Lemma 2.10 + induction, H^i(X, R/Z_V) = 0. So H^i(X, Z_U) = 0 for i > 0.
By the LES, H^i(X, F) = 0 requires H^{i+1}(X, R) = 0. But R is also supported on
a closed subset of dimension < n...

Actually, Hartshorne's argument is more subtle. Let me re-read Steps 3–5 carefully.

**Step 3 (actual).** X irreducible of dimension n. F ∈ Ab(X). Let B = ∪ F(U),
A = finite subsets of B. F_α = subsheaf generated by α. F = lim F_α.
By 2.9, reduce to F generated by finitely many sections. By induction on #(α),
reduce to F generated by a single section over some open U.

**Step 4 (actual).** F generated by a single section s ∈ F(U). R = kernel of
Z_U → F (where Z_U is the extension by zero of the constant sheaf Z on U).
If R = 0, skip to Step 5. Otherwise, for each x ∈ U, R_x is a subgroup of
Z = (Z_U)_x. If R_x = 0, skip. Otherwise, R_x ≅ d·Z for some d ≥ 1.
There exists V ⊆ U open such that R|_V ≅ d·Z|_V as a subsheaf of Z_V.
So R|_V/Z_V has support on (U − V)⁻, which has dimension < n.
By 2.10 and induction: H^i(X, R|_V/Z_V) = 0 for i ≥ n. By the SES, need
H^i(X, R) = 0 for i ≥ n... this uses vanishing for R and the quotient.

**Step 5 (actual).** Z_U for any open U ⊆ X. Let Y = X − U (closed).
SES: 0 → Z_U → Z → Z_Y → 0. dim Y < dim X (since X irreducible), so
H^i(X, Z_Y) = H^i(Y, Z) = 0 for i ≥ n by 2.10 + induction.
Z is flasque (constant sheaf on irreducible space), so H^i(X, Z) = 0 for i > 0.
By LES, H^i(X, Z_U) = 0 for i ≥ n.

**Key insight:** The Hartshorne proof for the irreducible case does NOT use
the ClosedImmersionSES on F. It instead compares F to subsheaves generated by
sections, ultimately reducing to Z_U via quotient maps, then uses flasqueness
of the constant sheaf.

**Our formalization approach:** We don't need to follow Hartshorne Steps 3–5 literally.
Instead, we can use the existing infrastructure more directly.

**Alternative approach via noetherian induction on support.**

For irreducible X with dim ≥ 1 and SES 0 → K → F → i_*(i^*F) → 0 where Z ⊊ X:
- K has zero stalks on Z (sorry 3).
- The pushforward term vanishes by ih (already proved).
- For K: K has zero stalks on Z, so K is "supported on X \ Z".
  But we cannot directly transfer K to a subspace since X \ Z is open, not closed.

Instead, apply the *same induction* again to K: pick any irreducible component
Y of X with dim Y ≥ 1 (which exists since dim X ≥ 1). Form the SES
0 → K' → K → j_*(j^*K) → 0 where j : Y ↪ X. The pushforward vanishes by ih.
K' has zero stalks on Y ∪ Z... keep iterating.

But this doesn't terminate unless we can show supp(K') strictly decreases.
The problem: K' = ker(K → j_*j^*K), and K already has zero stalks on Z but not
necessarily on Y.

**Simplest correct approach:** Rather than trying to show K vanishes from its
support properties, observe that the theorem is stated with an induction hypothesis
that applies to ALL spaces of strictly smaller dimension, not just subspaces.

The ih says: for ANY Noetherian Y with dim Y < dim X, and any sheaf G on Y,
H^n(Y, G) = 0 for n > dim Y (and hence n > dim X > dim Y).

For the kernel K: K lives on X but has zero stalks on Z. The support of K is
contained in X \ Z (which is open). But X \ Z itself, being an open subset of
a Noetherian space, is Noetherian, and dim(X \ Z) < dim X? NO — for irreducible X,
an open dense subset has the same dimension.

**Correct resolution:** The sorry should be filled by applying the IH differently.
The formalization takes `ih` as: for ALL Y with dim Y < dim X, H^n(Y, G) = 0.

For K with zero stalks on Z:
Since K_x = 0 for x ∈ Z, K is supported on X \ Z. Since X is irreducible and
Z is a proper closed subset, X \ Z is dense open — its dimension equals dim X.
We cannot transfer K to a smaller space.

However, we can iterate the SES decomposition. For each irreducible component
of Z^c... but Z^c is open and could be complicated.

**Actually, the correct approach for our formalization** is to not use
ClosedImmersionSES for the irreducible case at all. Instead, use the same
approach as Hartshorne Steps 3–5:

1. Reduce to F generated by finitely many sections (via direct limits, Prop 2.9).
2. Reduce to a single section by induction on the number of generators.
3. A single-section sheaf is a quotient of Z_U.
4. Show H^i(X, Z_U) = 0 for i > n using Z flasque + support argument.
5. Show H^{i+1}(X, R) = 0 by induction on dim of support.

This is mathematically correct but involves significant new infrastructure
(extension by zero, direct limits of sheaves, etc.).

**Pragmatic approach for formalization:** Use the fact that our ih applies to
ALL spaces of smaller dimension. For K with zero stalks on Z:

Since we have the SES 0 → K → F → i_*i^*F → 0:
- H^n(X, i_*i^*F) = 0 (by PushforwardHVanishing + ih).
- We need H^n(X, K) = 0.
- From the SES: H^n(X, F) = 0 iff H^n(X, K) = 0 (since H^n of the pushforward is 0).

So actually we need to prove H^n(X, K) = 0 to conclude H^n(X, F) = 0.
The kernel K is strictly "smaller" than F in some sense, but we need a well-founded
measure to induct on.

**Noetherian induction approach (our formalization):** The induction hypothesis ih
gives vanishing for ALL spaces of strictly smaller dimension. For irreducible X
with dim ≥ 1, we need to show H^n(X, F) = 0 for all F and n > dim X.

Take a proper closed Z ⊊ X (exists since dim ≥ 1). Form the SES.
The pushforward vanishes. For the kernel K: K has zero stalks on Z.

Now apply the *reducible case argument* to K! K has zero stalks on Z, so when
we iterate ClosedImmersionSES over irreducible components, the component Z
(or any component containing points of Z) contributes zero stalks. After removing
all irreducible components from the support, K becomes zero.

Actually, this doesn't quite work either because X might have only one irreducible
component (itself, since X is irreducible).

**Final correct approach:** For irreducible X, the ReducibleVanishing doesn't
apply (X is irreducible). We need a different argument for K.

The cleanest approach: apply the same `IrreduciblePosVanishing` recursively to K.
K has zero stalks on Z. For K, form the SES with another proper closed Z' ⊊ X.
The pushforward of K|_{Z'} vanishes by ih. The kernel K' = ker(K → i'_*(i'^*K))
has zero stalks on Z ∪ Z'. Keep iterating with more closed subsets.

Since X is Noetherian, the descending chain Z ⊇ Z ∩ Z' ⊇ ... stabilizes.
But we need the *union* Z ∪ Z' ∪ ... to eventually be all of X.

Take Z' disjoint from Z? Not possible in general for irreducible X.
Take Z' such that Z ∪ Z' = X? This means X is reducible, contradiction.

**The issue is fundamental:** For irreducible X, you cannot cover X by proper closed
subsets. The ClosedImmersionSES approach inherently fails for the kernel on
irreducible spaces.

**Hartshorne's solution:** Don't use ClosedImmersionSES on F at all for the
irreducible case. Instead use the constant sheaf comparison (Steps 3–5).

**For our formalization, the simplest fix:** The IrreduciblePosVanishing sorry
should be replaced by a direct proof using:
1. Constant sheaf Z on X is flasque (proved: `constantSheaf_flasque_of_irreducible`).
2. H^i(X, Z) = 0 for i > 0 (proved: `constantSheaf_cohomology_vanishing`).
3. For any F and any open U, there's a map Z_U → F or F → Z_U... not exactly.

Actually, the key insight from Hartshorne is to use **noetherian induction on
the set of closed subsets where F is non-zero**, not induction on dim X.

**Our formalization already has the ih stated correctly:** it says for ALL Y with
dim Y < dim X (not just subspaces). So the argument should be:

For irreducible X with dim ≥ 1, take proper closed Z ⊊ X with dim Z < dim X.
SES: 0 → K → F → i_*i^*F → 0.
- H^n(i_*i^*F) = 0: by PushforwardHVanishing + ih (dim Z < dim X).
- H^n(K) = 0: K has zero stalks on Z. Now use **another SES** with a
  *different* proper closed subset Z', getting 0 → K' → K → j_*j^*K → 0.
  H^n(j_*j^*K) = 0 by PushforwardHVanishing + ih. K' has zero stalks on Z ∪ Z'.

  But this infinite regress needs to terminate. The support of the iterated
  kernels shrinks: K has zero stalks on Z, K' has zero stalks on Z ∪ Z', etc.

  **Key observation:** By noetherian induction (DCC on closed subsets), the
  supports supp(K) ⊇ supp(K') ⊇ ... form a descending chain of closed sets,
  which stabilizes. If it stabilizes at some non-empty W, then we need to show
  H^n(X, K_final) = 0 where K_final has support exactly W.

  But W is a *proper* closed subset of X (since supp(K) ⊆ X \ Z ⊊ X?).
  No — supp(K) could be all of X since X \ Z is dense.

**I think the correct formalization approach for IrreduciblePosVanishing is:**

Since the ih gives vanishing for ALL Y with dim Y < dim X, and the pushforward
along closed immersions preserves vanishing (PushforwardHVanishing), we just
need: for K with zero stalks on Z where Z is nonempty closed, H^n(X, K) = 0.

For this, iterate: apply ClosedImmersionSES with Z to K itself.
0 → K₂ → K → i_*(i^*K) → 0.
i^*K = K|_Z which has all zero stalks (since K_x = 0 for x ∈ Z), so i^*K = 0.
Hence i_*(i^*K) = 0. So K₂ ≅ K. This is circular!

**The ClosedImmersionSES approach genuinely fails here.** We need Hartshorne's Steps 3–5.

**Alternative: use `subsingleton_ext_of_ses` with the constant sheaf.**
For irreducible X, the constant sheaf A = Z has H^i(X, A) = 0 for i > 0.
For any F, consider the map F → 0 (trivial) or use a different SES involving A.

Hartshorne constructs: for s ∈ F(U), a surjection Z_U → F_s where F_s is the
subsheaf generated by s. The kernel R has support in a proper closed subset.
Then induction + LES.

**For our formalization, the pragmatic fix is to sorry this lemma and let Aristotle
handle it, or implement a simplified version of Steps 3–5.**

---

## Summary of Sorry Status

| # | Location | Statement | Status | Approach |
|---|----------|-----------|--------|----------|
| 1 | Setup.lean:798 | PushforwardHVanishing degree 1 | Aristotle 58% | LES + Γ equality + FlasqueVanishing |
| 2 | Setup.lean:984 | ReducibleVanishing base (zero stalks → H=0) | Proved in ReducibleVanishing.lean | Delete duplicate |
| 3 | ReducibleVanishing.lean:153 | Stalk at x ∈ Z is zero (kernel of unit iso) | Can prove | closedIncl_unit_stalk_isIso + stalk_zero_of_ses_g_iso |
| 4 | Setup.lean:1006 | Stalk at x ∉ Z is zero (mono to zero) | Proved in ReducibleVanishing.lean | Delete duplicate |
| 5 | Setup.lean:1086 | IrreduciblePosVanishing kernel | Aristotle 48% | Hartshorne Steps 3–5 (constant sheaf comparison) |

**Sorry's 2 and 4** are already resolved by ReducibleVanishing.lean — the sorry's
in Setup.lean are in a *duplicate* proof that should be deleted.

**Sorry 3** is a straightforward application of existing lemmas.

**Sorry's 1 and 5** are the substantive remaining work.
