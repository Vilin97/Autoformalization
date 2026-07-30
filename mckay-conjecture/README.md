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
inertia-fibre count
`CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis`
separate from the prime-to-`q` relative-degree input
`CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis`. Their
checked composition supplies
`CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis` and the
existing conditional final reduction. The counting route works inside each
actual character inertia group and uses Gallagher's direct commutator-sum
proof followed by the classical, non-equivariant Okuyama--Wajima argument.
The invariant Clifford degree formulas and the two central commutator
identities are formalized as independent milestones, together with the
induced-character fibre identity, quotient-fibre reindexing, cyclic coset
norm, one-extension torsor criterion, preimage-centralizer commutator
identity, extension-ratio character and its good/non-good orthogonality
sum, the good-class orbit sum, the local Gallagher Schur identity, and its
cyclic-over-normal-subgroup coset norm. Their global assembly now proves
the complete ordinary Gallagher good-class cardinality theorem. Navarro
Lemma 5.13's two-generator extension criterion and the arithmetic adapter
from relative-degree divisibility to prime-to-degree fibres are also
formalized. A pointwise good-element equivalence now has a checked adapter
all the way to ordinary inertia-fibre cardinalities. The universal Navarro
relative-degree divisibility theorem is now formalized via the factor-set
multiplicity extension and character-center index comparison. It closes the
exact central-intersection automatic-degree hypothesis and gives final
reduction endpoints requiring only the ordinary inertia-fibre count. The ordinary
divisibility theorem `χ.degree ∣ Nat.card G` and its sharpening
`χ.degree ∣ χ.characterCenter.index` are now formalized by direct
class-sum integrality and free center-orbit arguments. Compatible linear
twisting, independent source/target fibre transport, and invariant
normal-Sylow parameter extension are formalized. The quotient Sylow image,
its exact normal-product preimage, normality descent, and first-isomorphism
coordinates needed to instantiate those twists are also formalized, as is
the resulting fibre-twist wrapper stated directly on the normal product.
The Okuyama--Wajima step now consumes the exact semantic uniform extension
comparison; weak factor matching remains only as an optional adapter, without
the false centralizer condition. The source-audited prime-local route is
decomposed into Navarro's Sylow-preimage criterion, the proved automatic
`p`-local extension, and the original OW comparison only at primes away from
`p`. The required quotient-preimage, local Sylow, normalizer, and intersection
coordinates are formalized, as is a generic theorem gluing Sylow-local
homomorphic sections over a finite abelian quotient with central kernel.
The canonical associated-factor restriction now converts local ordinary
extensions into those sections and proves Navarro local--global for every
abelian outer quotient; the uniform Navarro premise in the OW route is
therefore discharged automatically. The later transfer/cohomology proof
establishes Navarro local--global for arbitrary finite outer quotients and
discharges the prime-away `Q`-deletion step. The prime-away adapter proves
all local OW coordinates and now keeps only the genuine printed OW theorem
as a source input. The
Schur--Zassenhaus complement and canonical-base-fibre count are also
complete: determinant normalization constructs the invariant source and
target base extensions internally, and no chosen complement or canonical
extension hypothesis occurs in the automatic count.  The independent
source and target quotient-Sylow twists are now assembled into the
per-invariant-linear-parameter ordinary fibre equality, together with an
explicit-character theorem which extracts the two independent Gallagher
coordinates directly from separately invariant source and target
extensions. The theorem neither states nor proves any identification
between those parameters. The full inertia of the canonical kernel
character is also constructed, but the blueprint explicitly distinguishes
it from the smaller inertia of the chosen extension character, which is
the group used by the per-character cardinality boundary.
The retained prime-to-`p` coefficient calculation is also connected to the
printed extension interface by an explicit quotient-cochain gauge
construction. This honestly isolates the extra residue-transfer statement
that route would require (inflation injectivity is not assumed), but a
primary-source audit shows that it is not the argument proved by
Okuyama--Wajima. The source-faithful route now formalized follows their
direct strong induction: a Gorenstein cyclic-quotient subgroup dichotomy,
the subgroup-compatible Isaacs 13.29 Glauberman correspondence,
Glauberman transitivity, and two smaller-group recursive applications. The
Gorenstein output bundle, induced action on `P/P'`, dichotomy, and all
proper-branch subgroup consequences are formalized. The cyclic-image
existence proposition is proved by choosing a minimal normal subgroup
inside the abelianization kernel, interpreting it as an irreducible
`ZMod p`-module, and applying Schur's lemma, Little Wedderburn, and
cyclicity of finite-field units to its abelian action image.
Isaacs 13.28 is
also isolated at its exact source boundary—one invariant constituent,
not invariance of all constituents—but it is no longer a dependency of
the shorter full-fixed argument. The exact Isaacs 13.29 interface is now
proved: the two restriction-transitivity computations are compared
modulo `p`, and the needed normal Clifford
multiplicity-divides-degree fact is derived from the existing conjugacy
and restriction-degree APIs. All of its coordinate, multiplicity, fibre,
and cardinality consequences are formalized, and automatic full-fixed
wrappers discharge the theorem input. It identifies the invariant source
subfibre with the full fixed-point target fibre. A target extension over
the abelian quotient gives the
latter the full index cardinality; its injection into the complete source
fibre and the sharp Clifford upper bound squeeze that fibre to maximal
size. The sum-of-squared-multiplicities identity then forces every source
constituent to be an extension. The common index is now derived directly
from the explicit second-isomorphism equivalence
`U / C_K(S) ≃ (U ⊔ K) / K`, rather than retained as an independent
coordinate hypothesis. The ambient full-fixed coordinate module now
constructs the conjugation actions, identifies `(U ⊔ K)^P` with `U` and
the fixed normal subgroup with `C_K(P)`, transports quotient
commutativity, and specializes the index identity to the subgroup selected
by the proved Gorenstein theorem. The formerly isolated coprime
Burnside-basis premise is now discharged automatically. The IA
automorphisms of a finite `p`-group act freely on pointwise lifts of the
identity of `P/P'`; every such lift generates because `P'` lies in the
Frattini subgroup, and the lift set has `p`-power cardinality. Hence the IA
kernel is a `p`-group, so a `p'`-group acting trivially on `P/P'` acts
trivially on `P`. The
proper-branch Glauberman transitivity adapter is
complete as well, including both strong stages, ambient
`C_K(Q)`/`C_K(P)` coordinates, prime-to-`p` multiplicities, and
normalizer invariance for the selected subgroup. The proper recursive
chain is also formalized on the canonical `N_G(Q) / Q` and `Q M K`
character triples: both orders decrease, a direct coset equivalence
identifies the two ascent indices, and the group coordinates automatically
make them `p`-power indices. This uses `G = P H` and `P ∩ H = Q`,
without the generally unavailable assumption `H ◁ G`. Its endpoint
therefore retains only the two genuine smaller-group induction
conclusions. The subgroup recursive conclusion is now constructed
automatically from the universal smaller-group theorem. On the quotient
side, determinant normalization gives exact descent and ascent between
the source extension problems on `N_G(Q)` and `N_G(Q) / Q`. The target
comparison is automatic as well: the canonical containment
`N_G(P) ≤ N_G(Q)` identifies the internal normalizers, the two-stage
Glauberman transitivity theorem identifies their base characters, and
quotient extension descent identifies the remaining extension problems.

The well-founded part of the printed proof is also complete.
`OkuyamaWajimaPrintedInduction.lean` packages the exact printed extension
statement, handles the trivial Sylow case, selects the canonical
Gorenstein branch, and performs strong induction on `Nat.card`. In the
full-fixed branch the selected groups `U K ≤ M K` now have a cyclic
middle quotient, exact outer index `[G : M K] = |P|`, commutative source
and target quotients, and trivial `P`-action on `(U K) / K`. Both outer
character transports are now complete. In the forward direction,
normalizer-equivariance selects an `M K`-invariant source extension,
followed by cyclic and Navarro ascent. In the reverse direction,
equivariant 13.29 constructs an `M`-invariant target extension, followed
by the symmetric cyclic and Navarro ascents.
The source group `U K` is now proved normal in the whole ambient group,
the target complement has exact index `|P|` in `N_G(P)`, and the strong
action Glauberman correspondence is equivariant under every compatible
pair of automorphisms. These are the structural inputs used by the two
completed transport proofs.
The exact
extension-character inertia already has its characteristic `q'`-kernel
copy, Sylow subgroup, normal product, and Frattini generation; the canonical
kernel character and chosen extension character are transported through
those copies with their extension relation and full inertia invariance.
The ordinary OW count has now been specialized inside that exact inertia
group: its source and target normal products are related to the existing
coordinates by explicit equivalences, and the final fibre count is
transported through the canonical target-inertia equivalence. The copied
strong Glauberman correspondence is now constructed, its fixed-point
coordinate is proved compatible with the original correspondence, and
the canonical target extension and normalizer invariance are discharged.
Thus the transport-layer exact-inertia count endpoint retains only the
uniform printed OW input, and the canonical source-route automatic leaf
discharges that parameter. The two full-fixed implications, both
proper-quotient character-coordinate comparisons, and their canonical
strong-induction assembly are now proved, yielding the universal printed
extension statement for every finite group. An explicit local-subgroup
transport converts that universal theorem into the source-route input,
which is specialized automatically inside the exact character inertia,
transported to the matched target inertia, and relabelled through the two
standard character-triple equivalences. Consequently the global ordinary
inertia-fibre cardinality hypothesis is inhabited with no residual
Okuyama--Wajima premise. Combining it with the already automatic
relative-degree theorem also inhabits the prime-to-`q`
central-intersection cardinality hypothesis unconditionally. The entire
ordinary normal-subgroup seam is therefore closed; the remaining
mathematical input to the general theorem is the explicit
quasisimple/universal-cover verification supplied by the CFSG families.
`FinalCardinalityAutomatic.lean` exposes this boundary as
universe-polymorphic `statement_of_quasisimple` and
`statement_of_universalCover` wrappers whose only premise is that
classification input. `FinalCardinalityCFSGAutomatic.lean` further exposes
the prime-supported CFSG and alternating-family forms with no
central-intersection argument. No classification input is hidden behind an
axiom.

On that explicit classification side, the `A₅` universal-cover verification
is already closed at all relevant primes. For `A₆`, the two audited
Schur-cover outer automorphisms are now transported to the canonical cover
and inner-corrected into genuine stabilizers of any chosen Sylow subgroup,
uniformly in the prime. Their genuine ambient character-row permutations
are defined semantically from the completed table, and inner correction is
proved not to change them. Their genuine actions on the 31 certified
conjugacy classes are also computed as explicit checked vectors, and the
contragredient inverse-column formula for every transported table row is
proved.
Identifying the induced character-row permutations with the audited
CTblLib vectors remains. On the local
side, the genuine stabilizer actions are now transported through the proved
actual-normalizer row enumerations at `p = 2, 3, 5`, without asserting any
finite-vector identification. At all three primes, ordering-safe
reductions keep the ambient and local CT-position-to-Lean-row equivalences
explicit. Four bridge predicates in each case isolate exactly the two
ambient and two local outer-generator identifications. The audited finite
calculations then prove generator equivariance, and an equalizer argument
proves full equivariance from those four bridges and the now-proved theorem
that the inner normalizer range and the two corrected outer elements
generate the Sylow automorphism stabilizer. Thus each route conditionally
constructs the corresponding concrete character-table certificate from
only the proposed row identifications and their four semantic bridges,
without asserting that the recorded project order is the CTblLib order.
The local semantic permutation is also proved independent of the
noncanonical Sylow-conjugacy witness: any explicit correcting element gives
the same row action as the abstract chosen correction. This lets the four
local bridges be discharged by finite calculations with concrete
conjugators.
The `p = 3` route uses the corrected nonidentity candidate; the old
displayed-order identity is known not to satisfy the audited generator
equations.  Degree together with the audited central exponent partitions
the twelve ambient CT positions into two singletons and five pairs.  Two
ATLAS-aligned invariant-safe orientations are recorded, differing only in
the `row24`/`row25` pair.  Exact trace calculations now prove both full
ambient generator bridges for both orientations: alpha-one swaps that last
pair, while alpha-two fixes it.  These are complete semantic checks of the
proposed ambient orders, not independent proofs of CTblLib's stored order.
A proposed invariant-safe local order has also been recovered: its eight
linear rows have frequencies `[0,4,2,6,1,3,5,7]`, followed by the four
degree-four coordinates in lexicographic order.  It matches every audited
degree and central sign.  Explicit Schur-coordinate corrections settle the
first generator on `Z,X` and the second on `Z`; each full local bridge is
now exactly equivalent to its eleven nontrivial position equations.
Transport through the fixed-Sylow equivalence and the remaining coordinate
character evaluations are still open.
At `p = 2`, the old engineered central-block position identification is
now formally ruled out as a CTblLib identification.  Its two ambient bridges
would send a degree-three row to rows of degrees nine and five, while both
local bridges contradict the genuine inversion of the actual normalizer's
central `C₃` generator at CT position `1`.  A new
invariant-safe orientation matches every audited degree and central
exponent, transports back to the same algebraic central-block row matching,
and reduces each remaining ambient bridge exactly to a finite `12 × 31`
equality of constructed class values.  Its choices inside indistinguishable
invariant blocks remain conventions, not claims about CTblLib order.  On
the local side, evaluation at the actual normalizer's central `C₃`
generator proves that both genuine corrected actions negate the cyclic
coordinate.  The audited invariant-safe permutations do the same, so each
full local bridge is equivalent to equality of only the remaining
quaternion sign pair.  Those two residual equalities are now also proved
false: the first audited target moves a row trivial on the quaternion factor
at zero-based local position `6`, while the second changes the sign on the
characteristic order-eight cyclic subgroup at position `1`.  Thus the
invariant-safe local orientation is not genuine either.  A corrected
finite local order has now been recovered from the semantic action:
positions are ordered by cyclic/quaternion coordinates
`(0,00),(0,10),(0,11),(0,01),(1,10),(2,10),(1,11),(2,11),`
`(1,00),(2,00),(1,01),(2,01)`.  It preserves every audited central
exponent.  Both genuine generators are proved on all rows with first
quaternion sign zero, and injectivity forces the mate of every nonzero-sign
seed.  Consequently the two full 12-row local bridges are now exactly
equivalent to six genuine seed equations—one nonzero-sign value per cyclic
coordinate and generator.  Explicit quaternion coordinates now prove the
first generator's rotation/reflection action, construct an inner correction
for the second generator with its rotation/reflection shear, and transport
valid corrections back to the project's fixed Sylow subgroup.  Identifying
those transported actions with the existing noncomputable Sylow equivalence
and evaluating the six character seeds is the remaining local semantic
calculation.
The engineered `p = 5` position identification is likewise formally
impossible: its first audited ambient generator would change degree four to
six, and its second would change degree three to four.  Its invariant-safe
replacement matches all audited degrees and central exponents, recovers the
same algebraic central-block matching, and reduces each ambient bridge to an
explicit `24 × 31` class-value equality.  Exact evaluation at zero-based
position `20` and certified class `15` now proves that both of those
ambient bridges are false.  Thus this orientation is invariant-compatible
but is not the genuine CTblLib identification.  Exact cyclotomic
class-value transport now resolves its degree-twelve ambiguity: once
position `20` is anchored at ATLAS power two, positions `20..23` must be
ordered by powers `[2, 7, 11, 1]`, obtained by swapping the old positions
`21` and `23`.  All eight directed generator transports are proved:
alpha-one pairs powers `1 ↔ 2` and `7 ↔ 11`, while alpha-two pairs
`1 ↔ 11` and `2 ↔ 7`.  The resulting full corrected 24-position
equivalence and its induced local identification are now recorded and
recover the proved central-block candidate.  Prime-independent semantic
transport plus the completed `p = 3` actions settles all non-Atlas rows
currently determined by the value API.  In particular, alpha-two now
interchanges `row06` and `row07`.  Each full ambient bridge is therefore
exactly equivalent to the same ten residual positions `8..13,16..19`.
These are now the precise finite ambient calculations, rather than an
unresolved ordering search.
Independently, evaluation on the two standard presentation generators
injects `Aut(A₆)` into an executable-counted relation-pair type of cardinal
`1440`. Four conjugacy-class-separated outer representatives times the
inner group give the reverse injection, proving
`|Aut(A₆)| = |Aut(6.A₆)| = 1440`. The resulting four-coset normal form proves
that the two audited outer automorphisms and the inner subgroup generate the
full cover automorphism group. A general Sylow-correction theorem then
proves the exact stabilizer-generation statement uniformly for every prime,
closing its `p = 2, 3, 5` specializations. The finite upper-bound count uses
`native_decide`, so this particular certificate relies on Lean's executable
compiler path rather than only kernel reduction.

For projective compatibility, a reusable exact-normalizer row adapter now
derives all group-theoretic comparison data and the common scalar
automatically. With canonical associated projective lifts, each row is
reduced to literal equality of the two intertwiner factors on the character
stabilizer and one cross-multiplied projective-trace identity on the
relevant centralizer. For a nontrivial row whose inertia consists only of
normalizer-induced inner automorphisms, a second adapter now chooses a
normalized implementer lift automatically; that route leaves only
surjectivity of the normalizer-to-inertia map and matching ambient/local
central scalar actions.  A generator-cross variant further derives all
those scalar actions from one cross-multiplied character-value identity
whenever the local center is cyclically generated inside the ambient
center.  For the actual five-normalizer of `6.A₆`, the distinguished
order-six element is now proved to generate its center, and that center is
proved ambient-central.  Hence, conditional on ordinary five-local
equivariance, every row whose normalizer-inner map surjects onto its
character inertia has complete exact-normalizer projective data; no further
central-value or factor-set premise remains.  Surjectivity itself is now
equivalent to the finite assertion that every row-fixing Sylow automorphism
is inner.  The certified four-coset automorphism normal form reduces this
to movement by the two audited outer generators and their product.  Exactly
twelve audited five-local positions—zero-based positions `8..11` and
`16..23`—have free outer orbit.  For the invariant-safe orientation, its
four semantic bridges alone imply ordinary central-block equivariance and
would give all twelve complete projective rows, indexed as a `Fin 12`
family.  This remains a useful conditional decomposition, but the two
ambient premises are now proved false for that orientation, so it closes no
actual row until the position alignment is corrected.
For the ten audited positions in outer orbits of size two, a separate
conditional inertia reduction is complete.  Any row identification
satisfying the two genuine ambient bridges gives an inner-times-audited-
outer normal form, normality of the exact-normalizer inner image, and an
outer inertia quotient of cardinality at most two, hence cyclic.  This is
the correct interface for adjoining one residual outer implementer; it
does not apply to the disproved invariant-safe orientation without first
correcting its row order.  The one nontrivial fully fixed candidate remains
a separate four-element outer-inertia case.
The first genuine row
milestone is also closed at all
three exceptional primes: conditional only on the corresponding existing
ordinary candidate-equivariance bridge, the degree-one ambient row and its
frequency-zero local mate are proved intrinsically trivial and yield
complete exact-normalizer projective row data for `p = 2, 3, 5`. No
additional display-order assumption is introduced; the `p = 2` and `p = 5`
specializations use the deliberately engineered central-block candidates,
not an assertion about CTblLib display order.

As the first honest Lie-type foothold,
`ProjectiveSpecialLinearTwoSimpleFamily.lean` packages the groups
`PSL(2, 𝔽_{r^n})` for `4 ≤ r^n` as an isomorphism-invariant finite simple
family using mathlib's finite-field and `PSL₂` APIs.
`ProjectiveSpecialLinearTwoFamilyReduction.lean` then proves the structural
properties for every isomorphic family member and reduces family
verification to one explicit universal-cover/Sylow/local-data witness for
each prime-power representative. This is infrastructure and an exact
formal proof boundary. The next cover layer constructs the genuine
free-presentation universal cover, its central comparison onto `SL₂`, and
compatible Sylow and normalizer central extensions. Exact `SL₂`, center,
and `PSL₂` order formulas and prime-support iff theorems are also proved
from mathlib's determinant-kernel and roots-of-unity APIs.  The resulting
representative verification is now proved exactly equivalent to the three
rank-one support branches `p ∣ q`, `p ∣ q - 1`, and `p ∣ q + 1`; parameters
outside the target prime support are discharged automatically by the
central Sylow subgroup of a universal cover. This still provides no local
McKay verification or CFSG coverage. The efficient next split treats
`q = 4` through the closed `A₅` case, `q = 9` through the `A₆` residual,
and only then develops the generic `SL₂(q)` cover and normalizer theory.
That trichotomy, including the exact `(r,n) = (2,2)` and `(3,2)`
characterizations, is formalized. The `q = 4` branch is now closed by the
faithful action of `PSL₂(𝔽₄)` on its five-point projective line: perfectness
forces the image into `A₅`, and the two order-60 groups are isomorphic. The
closed `A₅` family theorem then supplies representative verification at
every prime. The structural `PSL₂(𝔽₉) ≃ A₆` residual is now closed by
explicit determinant-one matrices over `𝔽₉`: their projective classes
satisfy the certified four-relator presentation of `A₆`, simplicity gives
injectivity, and the two order-360 groups are then isomorphic. Verification
of this branch consequently reduces to the still-open `A₆` family datum.
Generic central-closedness has also been sharpened to the explicit family
`Nat.card (FreePresentation.HopfKernel (SL₂(q))) = 1`; this cardinality-one
input is proved sufficient to identify `SL₂(q)` with the free-presentation
universal cover. The strongest branch reduction now needs the `A₆`
verification, that generic Hopf-kernel computation, and one explicit
`SL₂(q)` Sylow/local datum only when the prime divides the projective
target to produce the complete `PSL₂` family verification and local data
on every isomorphic universal cover and Sylow subgroup. Generic parameters
outside the target prime support are now discharged automatically by the
central Sylow subgroup of `SL₂(q) → PSL₂(q)`.
