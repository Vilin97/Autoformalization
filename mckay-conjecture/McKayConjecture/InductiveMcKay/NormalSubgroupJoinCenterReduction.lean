/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralIndexQuotient
import McKayConjecture.GroupTheory.FrattiniIntermediate
import McKayConjecture.GroupTheory.NormalCentralSylowDecomposition
import McKayConjecture.GroupTheory.SylowNormalIntersection
import McKayConjecture.InductiveMcKay.MatchedCentralTripleCliffordAssembly
import McKayConjecture.InductiveMcKay.Normalizer
import McKayConjecture.InductiveMcKay.NumericalReduction

/-!
# Reduction through a normal subgroup joined with the center

Let `N ◁ G` be noncentral and put `J = N ⊔ Z(G)`.  If `J < G`, then
`J` has strictly smaller central index.  This file records that descent,
the canonical Sylow subgroup `Q = P ∩ J`, and the two intermediate
subgroups that occur in the normal-subgroup reduction.

The first intermediate is Rossi's

`J ⊔ N_G(P)`.

An explicit `p'`-character equivalence from `G` to this subgroup gives a
local correspondence whenever the subgroup is proper.  Conversely, in a
putative counterexample that equivalence forces `J ⊔ N_G(P) = G`.  This is
the exact numerical content of Rossi's Proposition 4.2 and Corollary 4.3;
properness does not follow from `J < G` alone.

The second intermediate starts from a local correspondence
`Irr_{p'}(J) ≃ Irr_{p'}(M)` at `Q` and is

`M N_G(Q)`.

Under the explicit normalizer-invariance hypothesis it is proper.  Two
further character-level assertions--equivariance of the displayed
correspondence and complete central witnesses for the matched inertia
triples--then suffice for the existing Clifford assembler to construct a
local correspondence at `P`.  These are kept as direct theorem parameters;
no local correspondence is hidden inside an opaque reduction hypothesis.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupJoinCenterReduction

open CharacterTriple
open GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The normal subgroup obtained by adjoining the ambient center to `N`. -/
abbrev joinCenter (N : Subgroup G) : Subgroup G :=
  N ⊔ Subgroup.center G

/-- A join with the center remains normal. -/
instance joinCenterNormal (N : Subgroup G) [N.Normal] :
    (joinCenter N).Normal :=
  inferInstance

omit [Finite G] in
/-- The original normal subgroup lies in its join with the center. -/
theorem le_joinCenter (N : Subgroup G) :
    N ≤ joinCenter N :=
  le_sup_left

omit [Finite G] in
/-- The ambient center lies in the join-center subgroup. -/
theorem center_le_joinCenter (N : Subgroup G) :
    Subgroup.center G ≤ joinCenter N :=
  le_sup_right

omit [Finite G] in
/-- Noncentrality says exactly that adjoining `N` strictly enlarges the
ambient center. -/
theorem center_lt_joinCenter (N : Subgroup G)
    (hNnoncentral : ¬N ≤ Subgroup.center G) :
    Subgroup.center G < joinCenter N := by
  refine lt_of_le_of_ne (center_le_joinCenter N) ?_
  intro h
  exact hNnoncentral
    ((le_joinCenter N).trans h.ge)

/-- Exact numerical hypothesis of Rossi's Proposition 4.2: adjoining a
noncentral subgroup to the center makes the quotient index strictly smaller
than the ambient central index. -/
theorem card_quotient_joinCenter_lt (N : Subgroup G)
    [N.Normal]
    (hNnoncentral : ¬N ≤ Subgroup.center G) :
    Nat.card (G ⧸ joinCenter N) < centralIndex G :=
  (card_quotient_sup_center_lt_centralIndex_iff
    (G := G) N).mpr hNnoncentral

/-- A proper join-center subgroup has strictly smaller central index. -/
theorem centralIndex_joinCenter_lt (N : Subgroup G)
    (hproper : joinCenter N ≠ ⊤) :
    centralIndex (joinCenter N) < centralIndex G :=
  centralIndex_lt_of_center_le_of_lt_top
    (joinCenter N)
    (center_le_joinCenter N)
    (lt_top_iff_ne_top.mpr hproper)

/-- The quotient by a normal noncentral subgroup also has strictly smaller
central index. -/
theorem centralIndex_quotient_lt (N : Subgroup G) [N.Normal]
    (hNnoncentral : ¬N ≤ Subgroup.center G) :
    centralIndex (G ⧸ N) < centralIndex G :=
  GroupTheory.centralIndex_quotient_lt N hNnoncentral

variable (P : Sylow p G) (N : Subgroup G) [N.Normal]

/-- If `N` has central intersection with the ambient Sylow subgroup, then
the same is true after adjoining the ambient center. -/
theorem joinCenter_inf_sylow_le_center
    (hcentral :
      N ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    joinCenter N ⊓ (P : Subgroup G) ≤
      Subgroup.center G :=
  GroupTheory.normal_sup_center_inf_sylow_le_center
    P N hcentral

/-- Exact form of `joinCenter_inf_sylow_le_center`. -/
theorem joinCenter_inf_sylow_eq
    (hcentral :
      N ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    joinCenter N ⊓ (P : Subgroup G) =
      (P : Subgroup G) ⊓ Subgroup.center G :=
  GroupTheory.normal_sup_center_inf_sylow_eq
    P N hcentral

/-- The canonical Sylow subgroup `P ∩ (N ⊔ Z(G))`, viewed internally in
the join-center subgroup. -/
abbrev joinCenterSylow :
    Sylow p (joinCenter N) :=
  GroupTheory.Sylow.intersectionNormal P (joinCenter N)

/-- Mapping the canonical join-center Sylow subgroup back to `G` gives the
literal intersection with `P`. -/
theorem map_joinCenterSylow_subtype :
    (joinCenterSylow P N : Subgroup (joinCenter N)).map
        (joinCenter N).subtype =
      (P : Subgroup G) ⊓ joinCenter N :=
  GroupTheory.Sylow.map_intersectionNormal_subtype
    P (joinCenter N)

/-- The ambient subgroup associated to the canonical join-center Sylow is
the literal intersection `P ∩ (N ⊔ Z(G))`. -/
theorem ambientSubgroup_joinCenterSylow :
    GroupTheory.Sylow.ambientSubgroup
        (joinCenterSylow P N) =
      (P : Subgroup G) ⊓ joinCenter N := by
  exact map_joinCenterSylow_subtype P N

/-- The ambient Sylow normalizer normalizes the canonical intersection
Sylow subgroup. -/
theorem normalizer_le_joinCenterSylow_normalizer :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer
        (GroupTheory.Sylow.ambientSubgroup
          (joinCenterSylow P N) : Set G) := by
  rw [ambientSubgroup_joinCenterSylow P N]
  exact
    GroupTheory.normalizer_le_normalizer_inf
      (joinCenter N) (P : Subgroup G)

/-- The Frattini argument for the canonical join-center Sylow subgroup. -/
theorem joinCenter_sup_sylowNormalizer :
    joinCenter N ⊔
        Subgroup.normalizer
          (GroupTheory.Sylow.ambientSubgroup
            (joinCenterSylow P N) : Set G) =
      ⊤ :=
  GroupTheory.Sylow.frattiniArgument
    (joinCenterSylow P N)

/-! ## Rossi's `J N_G(P)` intermediate -/

/-- Rossi's normal-subgroup intermediate `J N_G(P)`, written as a subgroup
join. -/
abbrev normalizerIntermediate : Subgroup G :=
  joinCenter N ⊔ Subgroup.normalizer (P : Set G)

omit [Finite G] [Fact p.Prime] [N.Normal] in
/-- The center is already contained in every Sylow normalizer, so Rossi's
intermediate simplifies from `(N ⊔ Z(G)) ⊔ N_G(P)` to `N ⊔ N_G(P)`. -/
theorem normalizerIntermediate_eq_normal_sup :
    normalizerIntermediate P N =
      N ⊔ Subgroup.normalizer (P : Set G) := by
  calc
    normalizerIntermediate P N =
        N ⊔
          (Subgroup.center G ⊔
            Subgroup.normalizer (P : Set G)) := by
      change
        (N ⊔ Subgroup.center G) ⊔
            Subgroup.normalizer (P : Set G) =
          N ⊔
            (Subgroup.center G ⊔
              Subgroup.normalizer (P : Set G))
      exact sup_assoc _ _ _
    _ = N ⊔ Subgroup.normalizer (P : Set G) := by
      rw [sup_eq_right.mpr
        (Subgroup.center_le_normalizer
          (P : Set G))]

omit [Finite G] [Fact p.Prime] [N.Normal] in
/-- The join-center subgroup lies in Rossi's intermediate. -/
theorem joinCenter_le_normalizerIntermediate :
    joinCenter N ≤ normalizerIntermediate P N :=
  le_sup_left

omit [Finite G] [Fact p.Prime] [N.Normal] in
/-- The ambient Sylow normalizer lies in Rossi's intermediate. -/
theorem normalizer_le_normalizerIntermediate :
    Subgroup.normalizer (P : Set G) ≤
      normalizerIntermediate P N :=
  le_sup_right

omit [Finite G] [Fact p.Prime] [N.Normal] in
/-- Hence the Sylow subgroup itself lies in Rossi's intermediate. -/
theorem sylow_le_normalizerIntermediate :
    (P : Subgroup G) ≤ normalizerIntermediate P N :=
  Subgroup.le_normalizer.trans
    (normalizer_le_normalizerIntermediate P N)

omit [Finite G] [Fact p.Prime] [N.Normal] in
/-- The ambient center lies in Rossi's intermediate. -/
theorem center_le_normalizerIntermediate :
    Subgroup.center G ≤ normalizerIntermediate P N :=
  (center_le_joinCenter N).trans
    (joinCenter_le_normalizerIntermediate P N)

/-- The canonical Sylow subgroup of Rossi's intermediate. -/
abbrev normalizerIntermediateSylow :
    Sylow p (normalizerIntermediate P N) :=
  sylowIn P (normalizerIntermediate P N)
    (sylow_le_normalizerIntermediate P N)

omit [Finite G] [Fact p.Prime] [N.Normal] in
/-- The Sylow normalizer computed inside Rossi's intermediate maps back to
the ambient normalizer. -/
theorem map_normalizerIntermediateSylow_normalizer :
    (Subgroup.normalizer
      (normalizerIntermediateSylow P N :
        Set (normalizerIntermediate P N))).map
        (normalizerIntermediate P N).subtype =
      Subgroup.normalizer (P : Set G) :=
  map_normalizer_sylowIn_eq
    P (normalizerIntermediate P N)
      (sylow_le_normalizerIntermediate P N)
      (normalizer_le_normalizerIntermediate P N)

omit [Fact p.Prime] [N.Normal] in
/-- Properness of Rossi's intermediate gives strict central-index descent. -/
theorem centralIndex_normalizerIntermediate_lt
    (hproper : normalizerIntermediate P N ≠ ⊤) :
    centralIndex (normalizerIntermediate P N) <
      centralIndex G :=
  centralIndex_lt_of_center_le_of_lt_top
    (normalizerIntermediate P N)
    (center_le_normalizerIntermediate P N)
    (lt_top_iff_ne_top.mpr hproper)

/-- The central-index induction hypothesis supplies local data on the
join-center subgroup. -/
theorem joinCenterLocalOfCentralIndexIH
    (hproper : joinCenter N ≠ ⊤)
    (ih :
      ∀ (H : Type u) [Group H] [Finite H],
        centralIndex H < centralIndex G →
          ∀ Q : Sylow p H,
            Nonempty (LocalCorrespondence Q)) :
    Nonempty (LocalCorrespondence (joinCenterSylow P N)) :=
  ih (joinCenter N)
    (centralIndex_joinCenter_lt N hproper)
    (joinCenterSylow P N)

/-- An explicit DGN/Rossi character equivalence to a proper
`J N_G(P)` is already exactly the character field of a local
correspondence at `P`. -/
def localCorrespondenceOfNormalizerIntermediateEquiv
    (hproper : normalizerIntermediate P N ≠ ⊤)
    (e :
      PPrimeIrreducibleCharacter G p ≃
        PPrimeIrreducibleCharacter
          (normalizerIntermediate P N) p) :
    LocalCorrespondence P where
  intermediate := normalizerIntermediate P N
  normalizer_le := normalizer_le_normalizerIntermediate P N
  proper_of_normalizer_ne_top := fun _ =>
    lt_top_iff_ne_top.mpr hproper
  correspondence := e

omit [Finite G] [Fact p.Prime] [N.Normal] in
/-- Numerical Corollary 4.3: if the DGN/Rossi equivalence to
`J N_G(P)` exists but no local correspondence at `P` exists, then
`J N_G(P) = G`.

This theorem deliberately does not claim that `J < G` forces
`J N_G(P) < G`; that implication is false for general finite groups. -/
theorem normalizerIntermediate_eq_top_of_equiv_of_noLocal
    (e :
      PPrimeIrreducibleCharacter G p ≃
        PPrimeIrreducibleCharacter
          (normalizerIntermediate P N) p)
    (hnoLocal : ¬Nonempty (LocalCorrespondence P)) :
    normalizerIntermediate P N = ⊤ := by
  by_contra hproper
  exact hnoLocal
    ⟨localCorrespondenceOfNormalizerIntermediateEquiv
      P N hproper e⟩

omit [Finite G] [Fact p.Prime] [N.Normal] in
/-- Corollary 4.3 in its customary form: the same hypotheses force
`G = N N_G(P)`.  The center adjoined to apply Proposition 4.2 disappears
because it already lies in `N_G(P)`. -/
theorem normal_sup_normalizer_eq_top_of_equiv_of_noLocal
    (e :
      PPrimeIrreducibleCharacter G p ≃
        PPrimeIrreducibleCharacter
          (normalizerIntermediate P N) p)
    (hnoLocal : ¬Nonempty (LocalCorrespondence P)) :
    N ⊔ Subgroup.normalizer (P : Set G) = ⊤ := by
  rw [← normalizerIntermediate_eq_normal_sup P N]
  exact
    normalizerIntermediate_eq_top_of_equiv_of_noLocal
      P N e hnoLocal

/-! ## Clifford assembly from the local correspondence on `J` -/

/-- Given a local correspondence on `J`, adjoin the ambient normalizer of
the canonical Sylow `Q = P ∩ J` to the image of its intermediate subgroup. -/
abbrev cliffordIntermediate
    (d : LocalCorrespondence (joinCenterSylow P N)) :
    Subgroup G :=
  d.intermediate.map (joinCenter N).subtype ⊔
    Subgroup.normalizer
      (GroupTheory.Sylow.ambientSubgroup
        (joinCenterSylow P N) : Set G)

/-- The target of the `J`-local correspondence, viewed as a subgroup of the
Clifford intermediate. -/
abbrev internalLocalIntermediate
    (d : LocalCorrespondence (joinCenterSylow P N)) :
    Subgroup (cliffordIntermediate P N d) :=
  (d.intermediate.map (joinCenter N).subtype).subgroupOf
    (cliffordIntermediate P N d)

/-- The internal target is canonically isomorphic to the original
intermediate subgroup in `J`. -/
def internalLocalIntermediateEquiv
    (d : LocalCorrespondence (joinCenterSylow P N)) :
    internalLocalIntermediate P N d ≃*
      d.intermediate :=
  (Subgroup.subgroupOfEquivOfLe le_sup_left).trans
    (Subgroup.equivMapOfInjective
      d.intermediate (joinCenter N).subtype
        (joinCenter N).subtype_injective).symm

/-- Transport the local character equivalence on `J` to the copy of its
target internal to the Clifford intermediate. -/
def internalLocalCharacterEquiv
    (d : LocalCorrespondence (joinCenterSylow P N)) :
    PPrimeIrreducibleCharacter (joinCenter N) p ≃
      PPrimeIrreducibleCharacter
        (internalLocalIntermediate P N d) p :=
  d.correspondence.trans
    (IrreducibleCharacter.pPrimeComapEquiv p
      (internalLocalIntermediateEquiv P N d))

/-- The original Sylow normalizer lies in the Clifford intermediate. -/
theorem normalizer_le_cliffordIntermediate
    (d : LocalCorrespondence (joinCenterSylow P N)) :
    Subgroup.normalizer (P : Set G) ≤
      cliffordIntermediate P N d :=
  (normalizer_le_joinCenterSylow_normalizer P N).trans
    le_sup_right

/-- The ambient center lies in the Clifford intermediate, because it
normalizes every subgroup. -/
theorem center_le_cliffordIntermediate
    (d : LocalCorrespondence (joinCenterSylow P N)) :
    Subgroup.center G ≤ cliffordIntermediate P N d :=
  (Subgroup.center_le_normalizer
    (GroupTheory.Sylow.ambientSubgroup
      (joinCenterSylow P N) : Set G)).trans
    le_sup_right

/-- The join-center subgroup and the Clifford intermediate generate `G`. -/
theorem joinCenter_sup_cliffordIntermediate
    (d : LocalCorrespondence (joinCenterSylow P N)) :
    joinCenter N ⊔ cliffordIntermediate P N d = ⊤ := by
  calc
    joinCenter N ⊔ cliffordIntermediate P N d =
        joinCenter N ⊔
          Subgroup.normalizer
            (GroupTheory.Sylow.ambientSubgroup
              (joinCenterSylow P N) : Set G) := by
      apply le_antisymm
      · refine sup_le le_sup_left (sup_le ?_ le_sup_right)
        exact
          (Subgroup.map_le_range
            (joinCenter N).subtype d.intermediate).trans
            ((joinCenter N).range_subtype.le.trans
              le_sup_left)
      · exact
          sup_le le_sup_left
            (le_sup_right.trans le_sup_right)
    _ = ⊤ :=
      joinCenter_sup_sylowNormalizer P N

/-- Normalizer invariance makes the internal target normal in the Clifford
intermediate. -/
theorem internalLocalIntermediate_normal
    (d : LocalCorrespondence (joinCenterSylow P N))
    (hinvariant :
      Subgroup.normalizer
          (GroupTheory.Sylow.ambientSubgroup
            (joinCenterSylow P N) : Set G) ≤
        Subgroup.normalizer
          (d.intermediate.map (joinCenter N).subtype)) :
    (internalLocalIntermediate P N d).Normal := by
  exact
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le Subgroup.le_normalizer hinvariant)

/-- If the local intermediate in `J` is proper and invariant under the
ambient normalizer of `Q`, then the Clifford intermediate is proper. -/
theorem cliffordIntermediate_lt_top
    (d : LocalCorrespondence (joinCenterSylow P N))
    (hQnormalizer :
      Subgroup.normalizer
        (joinCenterSylow P N :
          Set (joinCenter N)) ≠ ⊤)
    (hinvariant :
      Subgroup.normalizer
          (GroupTheory.Sylow.ambientSubgroup
            (joinCenterSylow P N) : Set G) ≤
        Subgroup.normalizer
          (d.intermediate.map (joinCenter N).subtype)) :
    cliffordIntermediate P N d < ⊤ :=
  GroupTheory.Sylow.map_sup_ambientNormalizer_lt_top
    (joinCenter N) (joinCenterSylow P N)
      d.intermediate
      (d.proper_of_normalizer_ne_top hQnormalizer)
      d.normalizer_le hinvariant

/-- The same proper Clifford intermediate has strictly smaller central
index. -/
theorem centralIndex_cliffordIntermediate_lt
    (d : LocalCorrespondence (joinCenterSylow P N))
    (hQnormalizer :
      Subgroup.normalizer
        (joinCenterSylow P N :
          Set (joinCenter N)) ≠ ⊤)
    (hinvariant :
      Subgroup.normalizer
          (GroupTheory.Sylow.ambientSubgroup
            (joinCenterSylow P N) : Set G) ≤
        Subgroup.normalizer
          (d.intermediate.map (joinCenter N).subtype)) :
    centralIndex (cliffordIntermediate P N d) <
      centralIndex G :=
  centralIndex_lt_of_center_le_of_lt_top
    (cliffordIntermediate P N d)
    (center_le_cliffordIntermediate P N d)
    (cliffordIntermediate_lt_top
      P N d hQnormalizer hinvariant)

/-! ### Character-theoretic completion

The active Clifford partition currently lives in `Type`, so the final
assembler below retains that existing universe boundary.  All structural
descent lemmas above are universe-polymorphic.
-/

section CliffordAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (K : Subgroup X) [K.Normal]

/-- Assemble a local correspondence at `S` from the local correspondence
on `K ⊔ Z(X)` and the two exact character assertions required by matched
central-triple Clifford theory.

Besides the structural normalizer-invariance hypothesis, the only
character-theoretic inputs are:

* equivariance of the transported local character equivalence under the
  full Clifford intermediate;
* a complete central-isomorphism witness for each exactly matched pair of
  inertia triples.

No ambient local correspondence is assumed. -/
def localCorrespondenceOfCliffordData
    (d : LocalCorrespondence (joinCenterSylow S K))
    (hQnormalizer :
      Subgroup.normalizer
        (joinCenterSylow S K :
          Set (joinCenter K)) ≠ ⊤)
    (hinvariant :
      Subgroup.normalizer
          (GroupTheory.Sylow.ambientSubgroup
            (joinCenterSylow S K) : Set X) ≤
        Subgroup.normalizer
          (d.intermediate.map (joinCenter K).subtype))
    (characterEquiv_smul :
      letI :
          (internalLocalIntermediate S K d).Normal :=
        internalLocalIntermediate_normal
          S K d hinvariant
      ∀ (h : cliffordIntermediate S K d)
        (θ :
          PPrimeIrreducibleCharacter
            (joinCenter K) q),
        internalLocalCharacterEquiv S K d (h • θ) =
          h • internalLocalCharacterEquiv S K d θ)
    (centralWitness :
      letI :
          (internalLocalIntermediate S K d).Normal :=
        internalLocalIntermediate_normal
          S K d hinvariant
      ∀ θ :
          PPrimeIrreducibleCharacter
            (joinCenter K) q,
        CompleteCentralIsomorphismWitness
          (ofInertia (joinCenter K) θ.1)
          (ofInertia
            (internalLocalIntermediate S K d)
            (internalLocalCharacterEquiv S K d θ).1)) :
    LocalCorrespondence S := by
  letI :
      (internalLocalIntermediate S K d).Normal :=
    internalLocalIntermediate_normal
      S K d hinvariant
  let assembly :
      MatchedCentralTripleCliffordAssemblyData
        (joinCenter K)
        (cliffordIntermediate S K d)
        (internalLocalIntermediate S K d) q :=
    { sup_eq_top :=
        joinCenter_sup_cliffordIntermediate S K d
      characterEquiv :=
        internalLocalCharacterEquiv S K d
      characterEquiv_smul := characterEquiv_smul
      centralWitness := centralWitness }
  exact
    { intermediate := cliffordIntermediate S K d
      normalizer_le :=
        normalizer_le_cliffordIntermediate S K d
      proper_of_normalizer_ne_top := fun _ =>
        cliffordIntermediate_lt_top
          S K d hQnormalizer hinvariant
      correspondence := assembly.assembledPPrimeEquiv }

@[simp]
theorem localCorrespondenceOfCliffordData_intermediate
    (d : LocalCorrespondence (joinCenterSylow S K))
    (hQnormalizer :
      Subgroup.normalizer
        (joinCenterSylow S K :
          Set (joinCenter K)) ≠ ⊤)
    (hinvariant :
      Subgroup.normalizer
          (GroupTheory.Sylow.ambientSubgroup
            (joinCenterSylow S K) : Set X) ≤
        Subgroup.normalizer
          (d.intermediate.map (joinCenter K).subtype))
    (characterEquiv_smul :
      letI :
          (internalLocalIntermediate S K d).Normal :=
        internalLocalIntermediate_normal
          S K d hinvariant
      ∀ (h : cliffordIntermediate S K d)
        (θ :
          PPrimeIrreducibleCharacter
            (joinCenter K) q),
        internalLocalCharacterEquiv S K d (h • θ) =
          h • internalLocalCharacterEquiv S K d θ)
    (centralWitness :
      letI :
          (internalLocalIntermediate S K d).Normal :=
        internalLocalIntermediate_normal
          S K d hinvariant
      ∀ θ :
          PPrimeIrreducibleCharacter
            (joinCenter K) q,
        CompleteCentralIsomorphismWitness
          (ofInertia (joinCenter K) θ.1)
          (ofInertia
            (internalLocalIntermediate S K d)
            (internalLocalCharacterEquiv S K d θ).1)) :
    (localCorrespondenceOfCliffordData
      S K d hQnormalizer hinvariant
        characterEquiv_smul centralWitness).intermediate =
      cliffordIntermediate S K d :=
  rfl

end CliffordAssembly

end NormalSubgroupJoinCenterReduction
end InductiveMcKay
end McKayConjecture
