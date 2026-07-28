/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.Transport
import McKayConjecture.CharacterTriple.Transitivity

/-!
# Butterfly transport for character triples

This file formalizes the exact group-theoretic content of the Butterfly
theorem for centrally isomorphic character triples.

Suppose `(A, X, χ) ≥c (H, M, χ')`, and let `A'` be another ambient group
containing the same character triple `(X, χ)`.  Write

* `κ : A → Aut(X)` and `κ' : A' → Aut(X)` for conjugation;
* `H' = κ'⁻¹(κ(H))`.

If `κ(A) = κ'(A')`, the classical Butterfly theorem gives
`(A', X, χ) ≥c (H', M, χ')`.  We allow all four ambient groups and both
copies of the normal subgroup to have different Lean types.  Consequently,
the hypotheses below record the isomorphisms identifying the two copies of
`(X, χ)` and `(M, χ')`, as well as the literal pullback equality defining
`H'` and the exact pushout/intersection equality identifying its normal
subgroup.

The current `CentralIsomorphismWitness` API stores chosen projective lifts,
but it has no uniqueness or descent theorem saying that such a lift depends
only on the induced automorphism of `X`.  The classical proof uses precisely
that descent.  `ButterflyProjectiveCoherence` therefore isolates the minimal
missing projective input: equality of the two new factor sets on `H' × H'`
and equality of their scalar operators over `C_{A'}(X)`.  Under this exact
coherence, `butterfly` constructs the transported central-isomorphism
witness; no character-count or cardinality surrogate is used.
-/

noncomputable section

universe u u' v v'

namespace McKayConjecture
namespace CharacterTriple

section ConjugationActions

variable {A : Type u} {A' : Type u'} [Finite A] [Finite A']
  [Group A] [Group A']

/-- The conjugation action attached to the ambient group of a character
triple. -/
abbrev conjugationAction (T : CharacterTriple A) :
    A →* MulAut T.normalSubgroup :=
  MulAut.conjNormal

/-- Transport the conjugation action of `T'` to the normal subgroup of `T`.

The equivalence `e` is the formal identification of the two copies of the
normal group occurring in the Butterfly theorem.
-/
def conjugationActionAlong (T : CharacterTriple A)
    (T' : CharacterTriple A')
    (e : T'.normalSubgroup ≃* T.normalSubgroup) :
    A' →* MulAut T.normalSubgroup :=
  (MulAut.congr e).toMonoidHom.comp T'.conjugationAction

@[simp]
theorem conjugationActionAlong_apply (T : CharacterTriple A)
    (T' : CharacterTriple A')
    (e : T'.normalSubgroup ≃* T.normalSubgroup) (a : A') :
    T.conjugationActionAlong T' e a =
      MulAut.congr e (T'.conjugationAction a) :=
  rfl

/-- Conjugation is trivial exactly on the centralizer of the normal
subgroup. -/
theorem conjugationAction_eq_one_iff (T : CharacterTriple A) (a : A) :
    T.conjugationAction a = 1 ↔
      a ∈ Subgroup.centralizer (T.normalSubgroup : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro ha x hx
    let xT : T.normalSubgroup := ⟨x, hx⟩
    have hax := DFunLike.congr_fun ha xT
    have hax' := congrArg Subtype.val hax
    change a * x * a⁻¹ = x at hax'
    exact (eq_comm.mp ((mul_inv_eq_iff_eq_mul).mp hax'))
  · intro ha
    ext x
    change a * (x : A) * a⁻¹ = x
    rw [← ha (x : A) x.property, mul_assoc]
    simp

/-- The action transported along an isomorphism has the same kernel as the
original conjugation action. -/
theorem conjugationActionAlong_eq_one_iff (T : CharacterTriple A)
    (T' : CharacterTriple A')
    (e : T'.normalSubgroup ≃* T.normalSubgroup) (a : A') :
    T.conjugationActionAlong T' e a = 1 ↔
      a ∈ Subgroup.centralizer (T'.normalSubgroup : Set A') := by
  rw [← T'.conjugationAction_eq_one_iff]
  constructor
  · intro ha
    change MulAut.congr e (T'.conjugationAction a) = 1 at ha
    apply (MulAut.congr e).injective
    simpa only [map_one] using ha
  · intro ha
    change MulAut.congr e (T'.conjugationAction a) = 1
    rw [ha, map_one]

/-- On an element of the normal subgroup, transported ambient conjugation is
the corresponding inner automorphism in the old copy of the normal group. -/
theorem conjugationActionAlong_normal (T : CharacterTriple A)
    (T' : CharacterTriple A')
    (e : T'.normalSubgroup ≃* T.normalSubgroup)
    (x : T'.normalSubgroup) :
    T.conjugationActionAlong T' e (x : A') =
      T.conjugationAction (e x : A) := by
  ext y
  change
    ((e.symm.trans ((T'.conjugationAction (x : A')).trans e)) y : A) =
      (e x : A) * (y : A) * (e x : A)⁻¹
  simp only [MulEquiv.trans_apply]
  have hsub :
      e (T'.conjugationAction (x : A') (e.symm y)) =
        e x * y * (e x)⁻¹ := by
    rw [MulAut.conjNormal_val]
    simp [MulAut.conj_apply]
  exact congrArg Subtype.val hsub

end ConjugationActions

section Diagram

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
  [Finite A] [Finite A'] [Finite B] [Finite B']
  [Group A] [Group A'] [Group B] [Group B']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
  {U : CharacterTriple B} {U' : CharacterTriple B'}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- The action on `X` induced by the subgroup in the original
central-isomorphism witness. -/
def CentralIsomorphismWitness.rightConjugationAction
    (C : CentralIsomorphismWitness T U V W) :
    B →* MulAut T.normalSubgroup :=
  T.conjugationAction.comp C.embedding

@[simp]
theorem CentralIsomorphismWitness.rightConjugationAction_apply
    (C : CentralIsomorphismWitness T U V W) (b : B) :
    C.rightConjugationAction b =
      T.conjugationAction (C.embedding b) :=
  rfl

/-- The canonical Butterfly subgroup
`κ'⁻¹(κ(H)) ≤ A'`, before choosing a group type isomorphic to it. -/
def butterflySubgroup
    (C : CentralIsomorphismWitness T U V W)
    (e : T'.normalSubgroup ≃* T.normalSubgroup) : Subgroup A' :=
  (MonoidHom.range C.rightConjugationAction).comap
    (T.conjugationActionAlong T' e)

@[simp]
theorem mem_butterflySubgroup_iff
    (C : CentralIsomorphismWitness T U V W)
    (e : T'.normalSubgroup ≃* T.normalSubgroup) (a : A') :
    a ∈ butterflySubgroup C e ↔
      ∃ b : B,
        C.rightConjugationAction b =
          T.conjugationActionAlong T' e a :=
  Iff.rfl

/-- The exact subgroup square used by Butterfly transport.

`ambient_action_range_eq` is the hypothesis `κ(A) = κ'(A')`.
`pullback_eq` says that the chosen copy of `H'` is literally the inverse
image `κ'⁻¹(κ(H))`.  Finally, `normal_pushout_eq` identifies the image of the
new right normal subgroup with the exact intersection `X ∩ H'`.
-/
structure ButterflySubgroupDiagram
    (C : CentralIsomorphismWitness T U V W)
    (T' : CharacterTriple A') (U' : CharacterTriple B') where
  /-- Identification of the two copies of the normal group `X`. -/
  normalEquiv : T'.normalSubgroup ≃* T.normalSubgroup
  /-- The chosen abstract copy of the Butterfly subgroup inside `A'`. -/
  embedding : B' →* A'
  /-- The chosen copy really is a subgroup, rather than a quotient. -/
  embedding_injective : Function.Injective embedding
  /-- Equality `κ(A) = κ'(A')` after identifying the two copies of `X`. -/
  ambient_action_range_eq :
    MonoidHom.range (T.conjugationActionAlong T' normalEquiv) =
      MonoidHom.range T.conjugationAction
  /-- The pullback identity `H' = κ'⁻¹(κ(H))`. -/
  pullback_eq :
    MonoidHom.range embedding =
      butterflySubgroup C normalEquiv
  /-- The exact normal-subgroup pushout/intersection identity
  `M = X ∩ H'`. -/
  normal_pushout_eq :
    U'.normalSubgroup.map embedding =
      T'.normalSubgroup ⊓ MonoidHom.range embedding

namespace ButterflySubgroupDiagram

variable (C : CentralIsomorphismWitness T U V W)
  (D : ButterflySubgroupDiagram C T' U')

/-- The image of an element of the new right normal subgroup, regarded as an
element of the new left normal subgroup. -/
def newRightNormalInLeft (m : U'.normalSubgroup) :
    T'.normalSubgroup :=
  ⟨D.embedding m, by
    have hm : D.embedding m ∈ U'.normalSubgroup.map D.embedding :=
      ⟨m, m.property, rfl⟩
    rw [D.normal_pushout_eq] at hm
    exact hm.1⟩

/-- The image of an element of the old right normal subgroup, regarded as an
element of the old left normal subgroup. -/
def oldRightNormalInLeft (m : U.normalSubgroup) :
    T.normalSubgroup :=
  ⟨C.embedding m, C.embedding_rightNormal_mem_leftNormal m⟩

@[simp]
theorem coe_newRightNormalInLeft (m : U'.normalSubgroup) :
    (newRightNormalInLeft C D m : A') = D.embedding m :=
  rfl

@[simp]
theorem coe_oldRightNormalInLeft (m : U.normalSubgroup) :
    (oldRightNormalInLeft C m : A) = C.embedding m :=
  rfl

/-- Identification of the two occurrences of `(X, χ)` and `(M, χ')` in the
classical Butterfly statement.

The last field says that these identifications commute with the two subgroup
embeddings, not merely that the normal groups have the same cardinality.
-/
structure CharacterCoherence where
  /-- The two copies of `χ` agree under `normalEquiv`. -/
  left_character_agreement : ∀ x : T'.normalSubgroup,
    T'.character.values x =
      T.character.values (D.normalEquiv x)
  /-- Identification of the two copies of `M`. -/
  rightNormalEquiv : U'.normalSubgroup ≃* U.normalSubgroup
  /-- The two copies of `χ'` agree under `rightNormalEquiv`. -/
  right_character_agreement : ∀ m : U'.normalSubgroup,
    U'.character.values m =
      U.character.values (rightNormalEquiv m)
  /-- The normal-subgroup identifications form the required commutative
  square inside the two copies of `X`. -/
  normal_embedding_commutes : ∀ m : U'.normalSubgroup,
    D.normalEquiv (newRightNormalInLeft C D m) =
      oldRightNormalInLeft C (rightNormalEquiv m)

/-- The pullback identity forces the new subgroup to contain the full
centralizer of `X`. -/
theorem centralizer_le_range :
    Subgroup.centralizer (T'.normalSubgroup : Set A') ≤
      MonoidHom.range D.embedding := by
  intro a ha
  rw [D.pullback_eq]
  change T.conjugationActionAlong T' D.normalEquiv a ∈
    MonoidHom.range C.rightConjugationAction
  rw [(T.conjugationActionAlong_eq_one_iff
    T' D.normalEquiv a).2 ha]
  exact Subgroup.one_mem _

/-- Equality of ambient action images and the old decomposition `A = XH`
imply the new decomposition `A' = XH'`. -/
theorem ambient_eq_product (a : A') :
    ∃ x : T'.normalSubgroup, ∃ h : B',
      (x : A') * D.embedding h = a := by
  have haRange :
      T.conjugationActionAlong T' D.normalEquiv a ∈
        MonoidHom.range T.conjugationAction := by
    rw [← D.ambient_action_range_eq]
    exact ⟨a, rfl⟩
  obtain ⟨aOld, haOld⟩ := haRange
  obtain ⟨xOld, hOld, hdecomp⟩ := C.ambient_eq_product aOld
  let xNew : T'.normalSubgroup := D.normalEquiv.symm xOld
  have hxAction :
      T.conjugationActionAlong T' D.normalEquiv (xNew : A') =
        T.conjugationAction (xOld : A) := by
    simpa [xNew] using
      T.conjugationActionAlong_normal T' D.normalEquiv xNew
  have haAction :
      T.conjugationActionAlong T' D.normalEquiv a =
        T.conjugationAction (xOld : A) *
          C.rightConjugationAction hOld := by
    rw [← haOld, ← hdecomp, map_mul]
    rfl
  have hpreimage :
      (xNew : A')⁻¹ * a ∈ butterflySubgroup C D.normalEquiv := by
    rw [mem_butterflySubgroup_iff]
    refine ⟨hOld, ?_⟩
    rw [map_mul, map_inv, hxAction, haAction]
    simp
  have hRange :
      (xNew : A')⁻¹ * a ∈ MonoidHom.range D.embedding := by
    rw [D.pullback_eq]
    exact hpreimage
  obtain ⟨hNew, hhNew⟩ := hRange
  refine ⟨xNew, hNew, ?_⟩
  rw [hhNew]
  simp

end ButterflySubgroupDiagram

end Diagram

section ProjectiveCoherence

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
  [Finite A] [Finite A'] [Finite B] [Finite B']
  [Group A] [Group A'] [Group B] [Group B']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
  {U : CharacterTriple B} {U' : CharacterTriple B'}
variable {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup V'] [Module ℂ V'] [Module.Finite ℂ V'] [Nontrivial V']
  [AddCommGroup W'] [Module ℂ W'] [Module.Finite ℂ W'] [Nontrivial W']
variable (C : CentralIsomorphismWitness T U V W)
  (D : ButterflySubgroupDiagram C T' U')
variable (P' : ProjectiveRepresentation ℂ A' V')
  (Q' : ProjectiveRepresentation ℂ B' W')

/-- The minimal projective descent input absent from the present associated
representation API.

These are exactly the two projective equalities used by the Butterfly
witness.  They are deliberately stronger than equality of character counts
and deliberately weaker than an arbitrary identification of the two
representation spaces.
-/
structure ButterflyProjectiveCoherence : Prop where
  /-- Agreement of factor sets on the pullback subgroup. -/
  factor_agreement : ∀ h k : B',
    P'.factor (D.embedding h) (D.embedding k) =
      Q'.factor h k
  /-- Agreement of scalar operators over the centralizer of `X`. -/
  scalar_agreement : ∀ h : B',
    D.embedding h ∈
      Subgroup.centralizer (T'.normalSubgroup : Set A') →
        ∃ c : ℂˣ,
          P'.operator (D.embedding h) = scalarLinearEquiv ℂ V' c ∧
          Q'.operator h = scalarLinearEquiv ℂ W' c

/-- Butterfly transport of a central-isomorphism witness.

The group-theoretic witness fields are derived from the literal automorphism
pullback diagram.  The chosen associated projective lifts only need the
minimal factor/scalar coherence isolated above.
-/
def CentralIsomorphismWitness.butterfly
    (R' : AssociatedProjectiveRepresentation T' V' P')
    (S' : AssociatedProjectiveRepresentation U' W' Q')
    (_hchar : D.CharacterCoherence C)
    (hproj : ButterflyProjectiveCoherence C D P' Q') :
    CentralIsomorphismWitness T' U' V' W' where
  leftProjective := P'
  leftAssociated := R'
  rightProjective := Q'
  rightAssociated := S'
  embedding := D.embedding
  embedding_injective := D.embedding_injective
  centralizer_le := D.centralizer_le_range C
  ambient_eq_product := D.ambient_eq_product C
  intersection_eq := D.normal_pushout_eq.symm
  factor_agreement := hproj.factor_agreement
  scalar_agreement := hproj.scalar_agreement

/-- The existence-form Butterfly theorem with exact subgroup and projective
data. -/
theorem centrallyIsomorphicVia_butterfly
    (R' : AssociatedProjectiveRepresentation T' V' P')
    (S' : AssociatedProjectiveRepresentation U' W' Q')
    (hchar : D.CharacterCoherence C)
    (hproj : ButterflyProjectiveCoherence C D P' Q') :
    CentralIsomorphismWitness.CentrallyIsomorphicVia T' U' V' W' :=
  ⟨C.butterfly D P' Q' R' S' hchar hproj⟩

end ProjectiveCoherence

end CharacterTriple
end McKayConjecture
