/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveRepresentation
import McKayConjecture.IrreducibleCharacter
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.Trace

/-!
# Centrally isomorphic character triples

This file formalizes the character-triple data and the projective-representation
witness in the definition of the relation `≥c`.

An associated projective representation is required not only to restrict to a
linear representation affording the character, but also to satisfy
`P(ng) = P(n)P(g)` and `P(gn) = P(g)P(n)`.  These are the standard
normal-subgroup compatibility equations; equivalently, the factor set is
trivial on `(X × A) ∪ (A × X)`.

For flexibility, the right ambient group is allowed to be abstractly embedded
in the left ambient group.  Its image is the subgroup denoted `H` in the
usual definition.  Thus the hypotheses below say exactly
`C_A(X) ≤ H`, `A = XH`, and `H ∩ X = M`, after identifying the right
ambient group and its normal subgroup with their images.
-/

noncomputable section

open CategoryTheory

universe u v w

namespace McKayConjecture

/-- Conjugate an element of a normal subgroup, retaining its subgroup proof. -/
def conjugateNormalElement {A : Type u} [Group A] (X : Subgroup A)
    (hX : X.Normal) (a : A) (x : X) : X :=
  ⟨a * x * a⁻¹, hX.conj_mem x x.property a⟩

/-- A character triple `(A, X, χ)`: `A` is finite, `X` is normal in `A`,
and the irreducible character `χ` of `X` is invariant under conjugation by
`A`. -/
structure CharacterTriple (A : Type u) [Finite A] [Group A] where
  /-- The normal subgroup `X`. -/
  normalSubgroup : Subgroup A
  /-- Normality of `X` in `A`. -/
  isNormal : normalSubgroup.Normal
  /-- The irreducible character `χ` of `X`. -/
  character : IrreducibleCharacter normalSubgroup
  /-- Invariance of `χ` under conjugation by the ambient group. -/
  isInvariant : ∀ (a : A) (x : normalSubgroup),
    character.values (conjugateNormalElement normalSubgroup isNormal a x) =
      character.values x

namespace CharacterTriple

variable {A : Type u} [Finite A] [Group A]

instance (T : CharacterTriple A) : T.normalSubgroup.Normal :=
  T.isNormal

/-- Character invariance expressed using mathlib's conjugation automorphism of
a normal subgroup. -/
theorem invariant_conjNormal (T : CharacterTriple A) (a : A) (x : T.normalSubgroup) :
    T.character.values (MulAut.conjNormal a x) = T.character.values x := by
  exact T.isInvariant a x

/-- A linear action by automorphisms, regarded as a mathlib representation. -/
def linearRepresentationOfAction {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (D : G →* (V ≃ₗ[ℂ] V)) : Representation ℂ G V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp D

@[simp]
theorem linearRepresentationOfAction_apply {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (D : G →* (V ≃ₗ[ℂ] V)) (g : G) :
    linearRepresentationOfAction D g = (D g : V →ₗ[ℂ] V) :=
  rfl

/-- A projective representation associated with a character triple.

The restriction is certified as a simple finite-dimensional representation
whose character is the character in the triple.  The final two fields are the
standard compatibility conditions with multiplication by the normal subgroup.
-/
structure AssociatedProjectiveRepresentation (T : CharacterTriple A)
    (V : Type) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
    (P : CharacterTriple.ProjectiveRepresentation ℂ A V) where
  /-- The ordinary representation obtained by restricting to `X`. -/
  restriction : T.normalSubgroup →* (V ≃ₗ[ℂ] V)
  /-- The restricted action is the chosen projective lift on `X`. -/
  restriction_apply : ∀ x : T.normalSubgroup, restriction x = P.operator x
  /-- The restricted representation is irreducible. -/
  restriction_simple :
    Simple (FDRep.of (linearRepresentationOfAction restriction))
  /-- The restricted representation affords the character in the triple. -/
  restriction_character :
    (FDRep.of (linearRepresentationOfAction restriction)).character =
      T.character.values
  /-- Compatibility with multiplication by `X` on the left. -/
  normal_mul : ∀ (x : T.normalSubgroup) (a : A),
    P.operator ((x : A) * a) = P.operator x * P.operator a
  /-- Compatibility with multiplication by `X` on the right. -/
  mul_normal : ∀ (a : A) (x : T.normalSubgroup),
    P.operator (a * (x : A)) = P.operator a * P.operator x

namespace AssociatedProjectiveRepresentation

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  {T : CharacterTriple A} {P : CharacterTriple.ProjectiveRepresentation ℂ A V}

/-- The bundled finite-dimensional restriction representation. -/
abbrev fdRestriction (R : AssociatedProjectiveRepresentation T V P) : FDRep ℂ T.normalSubgroup :=
  FDRep.of (linearRepresentationOfAction R.restriction)

instance (R : AssociatedProjectiveRepresentation T V P) : Simple R.fdRestriction :=
  R.restriction_simple

@[simp]
theorem fdRestriction_character (R : AssociatedProjectiveRepresentation T V P) :
    R.fdRestriction.character = T.character.values :=
  R.restriction_character

/-- The factor set is trivial whenever its first argument lies in the normal
subgroup. -/
theorem factor_normal_left (R : AssociatedProjectiveRepresentation T V P)
    (x : T.normalSubgroup) (a : A) :
    P.factor x a = 1 := by
  apply scalarLinearEquiv_injective ℂ V
  rw [map_one]
  apply mul_right_cancel
  rw [← P.map_mul]
  simpa [R.restriction_apply] using (R.normal_mul x a).symm

/-- The factor set is trivial whenever its second argument lies in the normal
subgroup. -/
theorem factor_normal_right (R : AssociatedProjectiveRepresentation T V P)
    (a : A) (x : T.normalSubgroup) :
    P.factor a x = 1 := by
  apply scalarLinearEquiv_injective ℂ V
  rw [map_one]
  apply mul_right_cancel
  rw [← P.map_mul]
  simpa [R.restriction_apply] using (R.mul_normal a x).symm

/-- An ambient element centralizing `X` acts as an endomorphism of the
irreducible restriction representation. -/
def centralizerEndomorphism (R : AssociatedProjectiveRepresentation T V P)
    (a : A) (ha : a ∈ Subgroup.centralizer (T.normalSubgroup : Set A)) :
    R.fdRestriction ⟶ R.fdRestriction :=
  ⟨InducedCategory.homMk (ModuleCat.ofHom (P.operator a : V →ₗ[ℂ] V)),
    fun x ↦ by
        ext z
        change P.operator a (R.restriction x z) =
          R.restriction x (P.operator a z)
        rw [R.restriction_apply, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply]
        congr 1
        rw [← R.mul_normal a x, ← R.normal_mul x a]
        exact congrArg P.operator
          ((Subgroup.mem_centralizer_iff.mp ha) x x.property).symm⟩

@[simp]
theorem centralizerEndomorphism_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (a : A) (ha : a ∈ Subgroup.centralizer (T.normalSubgroup : Set A)) (z : V) :
    R.centralizerEndomorphism a ha z = P.operator a z :=
  rfl

/-- Schur's lemma: every ambient element centralizing `X` is represented by
a nonzero scalar matrix. -/
theorem operator_centralizer_isScalar
    (R : AssociatedProjectiveRepresentation T V P)
    (a : A) (ha : a ∈ Subgroup.centralizer (T.normalSubgroup : Set A)) :
    ∃ c : ℂˣ, P.operator a = scalarLinearEquiv ℂ V c := by
  let f := R.centralizerEndomorphism a ha
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ f
  have hpoint : ∀ z : V, c • z = P.operator a z := by
    intro z
    have hz := ConcreteCategory.congr_hom hc z
    change c • z = P.operator a z at hz
    exact hz
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨z : V, hz⟩ := exists_ne (0 : V)
    have hopen_zero : P.operator a z = 0 := by
      rw [← hpoint z, hc0, zero_smul]
    exact hz ((P.operator a).injective (by simpa using hopen_zero))
  refine ⟨Units.mk0 c hc0, ?_⟩
  ext z
  exact (hpoint z).symm

end AssociatedProjectiveRepresentation

section CentralIsomorphism

variable {B : Type w} [Finite B] [Group B]
  (T : CharacterTriple A) (U : CharacterTriple B)
  (V W : Type)
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- The part of a central character-triple comparison needed for the
ordinary character correspondence.

It records the two associated projective representations, literal agreement
of their factor sets, and the three subgroup conditions used by the tensor
and multiplicity constructions.  In contrast with
`CentralIsomorphismWitness`, it deliberately does not require the image to
contain the left centralizer or the two projective lifts to have the same
scalar there. -/
structure FactorMatchedIsomorphismWitness where
  /-- The projective representation associated with the left character triple. -/
  leftProjective : ProjectiveRepresentation ℂ A V
  /-- Certification that the left projective representation is associated with `χ`. -/
  leftAssociated :
    AssociatedProjectiveRepresentation T V leftProjective
  /-- The projective representation associated with the right character triple. -/
  rightProjective : ProjectiveRepresentation ℂ B W
  /-- Certification that the right projective representation is associated with `χ'`. -/
  rightAssociated :
    AssociatedProjectiveRepresentation U W rightProjective
  /-- Identification of the right ambient group with a subgroup `H` of `A`. -/
  embedding : B →* A
  /-- The identification with `H` is injective. -/
  embedding_injective : Function.Injective embedding
  /-- The exact product condition `A = XH`. -/
  ambient_eq_product : ∀ a : A,
    ∃ x : T.normalSubgroup, ∃ h : B, (x : A) * embedding h = a
  /-- The exact intersection condition `H ∩ X = M`, after applying the embedding. -/
  intersection_eq :
    T.normalSubgroup ⊓ MonoidHom.range embedding =
      U.normalSubgroup.map embedding
  /-- The two factor sets coincide on `H × H`. -/
  factor_agreement : ∀ h k : B,
    leftProjective.factor (embedding h) (embedding k) =
      rightProjective.factor h k

/-- A witness that `(A, X, χ) ≥c (H, M, χ')`.

The right ambient group `B` is identified with the subgroup `H ≤ A` by the
injective homomorphism `embedding`; consequently `H` is its range.  This
formulation makes reflexivity literal while retaining all three exact subgroup
hypotheses from the standard definition.
-/
structure CentralIsomorphismWitness extends
    FactorMatchedIsomorphismWitness T U V W where
  /-- The exact condition `C_A(X) ≤ H`. -/
  centralizer_le :
    Subgroup.centralizer (T.normalSubgroup : Set A) ≤ MonoidHom.range embedding
  /-- On `C_A(X)`, the two projective representations are scalar matrices
  with the same nonzero scalar. -/
  scalar_agreement : ∀ (h : B),
    embedding h ∈ Subgroup.centralizer (T.normalSubgroup : Set A) →
      ∃ c : ℂˣ,
        leftProjective.operator (embedding h) = scalarLinearEquiv ℂ V c ∧
          rightProjective.operator h = scalarLinearEquiv ℂ W c

instance :
    Coe (CentralIsomorphismWitness T U V W)
      (FactorMatchedIsomorphismWitness T U V W) :=
  ⟨CentralIsomorphismWitness.toFactorMatchedIsomorphismWitness⟩

namespace FactorMatchedIsomorphismWitness

variable {T U V W}

/-- The subgroup denoted `H` in the standard definition. -/
abbrev H (C : FactorMatchedIsomorphismWitness T U V W) : Subgroup A :=
  MonoidHom.range C.embedding

/-- The subgroup product decomposition supplied by the witness. -/
theorem exists_normal_mul_H
    (C : FactorMatchedIsomorphismWitness T U V W) (a : A) :
    ∃ x : T.normalSubgroup, ∃ h : B, (x : A) * C.embedding h = a :=
  C.ambient_eq_product a

/-- The subgroup product condition implies the lattice statement `X ⊔ H = ⊤`. -/
theorem normal_sup_H_eq_top
    (C : FactorMatchedIsomorphismWitness T U V W) :
    T.normalSubgroup ⊔ C.H = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨x, h, rfl⟩ := C.ambient_eq_product a
  exact (T.normalSubgroup ⊔ C.H).mul_mem
    (show (x : A) ∈ T.normalSubgroup ⊔ C.H from
      Subgroup.mem_sup_left x.property)
    (show C.embedding h ∈ T.normalSubgroup ⊔ C.H from
      Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem H_inf_normal_eq
    (C : FactorMatchedIsomorphismWitness T U V W) :
    C.H ⊓ T.normalSubgroup = U.normalSubgroup.map C.embedding := by
  rw [inf_comm, C.intersection_eq]

/-- The embedded right normal subgroup lies in the left normal subgroup. -/
theorem map_rightNormal_le_leftNormal
    (C : FactorMatchedIsomorphismWitness T U V W) :
    U.normalSubgroup.map C.embedding ≤ T.normalSubgroup := by
  rw [← C.intersection_eq]
  exact inf_le_left

/-- The factor-set agreement, exposed without referring to structure fields. -/
theorem factors_eq
    (C : FactorMatchedIsomorphismWitness T U V W) (h k : B) :
    C.leftProjective.factor (C.embedding h) (C.embedding k) =
      C.rightProjective.factor h k :=
  C.factor_agreement h k

end FactorMatchedIsomorphismWitness

namespace CentralIsomorphismWitness

variable {T U V W}

/-- The subgroup denoted `H` in the standard definition. -/
abbrev H (C : CentralIsomorphismWitness T U V W) : Subgroup A :=
  C.toFactorMatchedIsomorphismWitness.H

theorem centralizer_le_H (C : CentralIsomorphismWitness T U V W) :
    Subgroup.centralizer (T.normalSubgroup : Set A) ≤ C.H :=
  C.centralizer_le

/-- The subgroup product decomposition supplied by the witness. -/
theorem exists_normal_mul_H
    (C : CentralIsomorphismWitness T U V W) (a : A) :
    ∃ x : T.normalSubgroup, ∃ h : B, (x : A) * C.embedding h = a :=
  C.toFactorMatchedIsomorphismWitness.exists_normal_mul_H a

/-- The subgroup product condition implies the lattice statement `X ⊔ H = ⊤`. -/
theorem normal_sup_H_eq_top
    (C : CentralIsomorphismWitness T U V W) :
    T.normalSubgroup ⊔ C.H = ⊤ :=
  C.toFactorMatchedIsomorphismWitness.normal_sup_H_eq_top

theorem H_inf_normal_eq
    (C : CentralIsomorphismWitness T U V W) :
    C.H ⊓ T.normalSubgroup = U.normalSubgroup.map C.embedding :=
  C.toFactorMatchedIsomorphismWitness.H_inf_normal_eq

/-- The embedded right normal subgroup lies in the left normal subgroup. -/
theorem map_rightNormal_le_leftNormal
    (C : CentralIsomorphismWitness T U V W) :
    U.normalSubgroup.map C.embedding ≤ T.normalSubgroup :=
  C.toFactorMatchedIsomorphismWitness.map_rightNormal_le_leftNormal

/-- The factor-set agreement, exposed without referring to structure fields. -/
theorem factors_eq
    (C : CentralIsomorphismWitness T U V W) (h k : B) :
    C.leftProjective.factor (C.embedding h) (C.embedding k) =
      C.rightProjective.factor h k :=
  C.toFactorMatchedIsomorphismWitness.factors_eq h k

/-- Exact scalar agreement for a centralizer element, after choosing its
unique preimage in `H`. -/
theorem scalar_agreement_on_centralizer
    (C : CentralIsomorphismWitness T U V W)
    (a : Subgroup.centralizer (T.normalSubgroup : Set A)) :
    ∃ h : B, C.embedding h = (a : A) ∧
      ∃ c : ℂˣ,
        C.leftProjective.operator a = scalarLinearEquiv ℂ V c ∧
          C.rightProjective.operator h = scalarLinearEquiv ℂ W c := by
  obtain ⟨h, hh⟩ := C.centralizer_le a.property
  refine ⟨h, hh, ?_⟩
  simpa [hh] using C.scalar_agreement h (hh ▸ a.property)

/-- The identity witness: any associated projective representation gives a
central isomorphism of a character triple with itself. -/
def refl {P : ProjectiveRepresentation ℂ A V}
    (R : AssociatedProjectiveRepresentation T V P) :
    CentralIsomorphismWitness T T V V where
  leftProjective := P
  leftAssociated := R
  rightProjective := P
  rightAssociated := R
  embedding := MonoidHom.id A
  embedding_injective := Function.injective_id
  centralizer_le := by
    intro a _
    exact ⟨a, rfl⟩
  ambient_eq_product := by
    intro a
    exact ⟨1, a, by simp⟩
  intersection_eq := by
    ext a
    simp
  factor_agreement := by
    intro h k
    rfl
  scalar_agreement := by
    intro a ha
    obtain ⟨c, hc⟩ := R.operator_centralizer_isScalar a ha
    exact ⟨c, hc, hc⟩

/-- Existence of a witness using fixed representation spaces. -/
def CentrallyIsomorphicVia
    (T' : CharacterTriple A) (U' : CharacterTriple B)
    (V' W' : Type)
    [AddCommGroup V'] [Module ℂ V'] [Module.Finite ℂ V'] [Nontrivial V']
    [AddCommGroup W'] [Module ℂ W'] [Module.Finite ℂ W'] [Nontrivial W'] :
    Prop :=
  Nonempty (CentralIsomorphismWitness T' U' V' W')

theorem centrallyIsomorphicVia_refl {P : ProjectiveRepresentation ℂ A V}
    (R : AssociatedProjectiveRepresentation T V P) :
    CentrallyIsomorphicVia T T V V :=
  ⟨refl R⟩

end CentralIsomorphismWitness
end CentralIsomorphism
end CharacterTriple
end McKayConjecture
