/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCorrespondence

/-!
# Irreducible projective representations

A subspace of a projective representation is stable when it is preserved by
every chosen projective operator.  This condition is independent of the scalar
discrepancies in the multiplication law, since every discrepancy is a nonzero
scalar.

Projective irreducibility means that the representation space is nonzero and
that its only stable subspaces are `⊥` and `⊤`.  Pullback along a group
homomorphism preserves this notion whenever the pulled-back operators cover
all the original operators.

For the embedding in a central-isomorphism witness, this coverage condition
holds for an inverse-factor projective representation that is trivial on the
left normal subgroup.  Indeed, the product decomposition `A = XH`, together
with cancellation of the associated factor on `X × A`, shows that every
operator already occurs on the embedded right ambient group.
-/

noncomputable section

universe u v w x

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} {G : Type v} {H : Type w} {Z : Type x}
variable [Field K] [Group G] [Group H]
variable [AddCommGroup Z] [Module K Z]

/-- A submodule is stable under a projective representation when every chosen
projective operator preserves it. -/
def IsStable (Q : ProjectiveRepresentation K G Z)
    (S : Submodule K Z) : Prop :=
  ∀ (g : G) ⦃z : Z⦄, z ∈ S → Q.operator g z ∈ S

@[simp]
theorem isStable_bot (Q : ProjectiveRepresentation K G Z) :
    Q.IsStable (⊥ : Submodule K Z) := by
  intro g z hz
  rw [Submodule.mem_bot] at hz
  subst z
  rw [map_zero]
  exact (⊥ : Submodule K Z).zero_mem

@[simp]
theorem isStable_top (Q : ProjectiveRepresentation K G Z) :
    Q.IsStable (⊤ : Submodule K Z) := by
  intro g z hz
  exact Submodule.mem_top

/-- A projective representation is irreducible when its space is nonzero and
its only stable submodules are `⊥` and `⊤`.

The explicit `Nontrivial Z` conjunct rules out the zero representation, whose
submodule lattice alone would otherwise satisfy the second conjunct. -/
def IsIrreducible (Q : ProjectiveRepresentation K G Z) : Prop :=
  Nontrivial Z ∧
    ∀ S : Submodule K Z, Q.IsStable S → S = ⊥ ∨ S = ⊤

theorem IsIrreducible.nontrivial
    {Q : ProjectiveRepresentation K G Z} (hQ : Q.IsIrreducible) :
    Nontrivial Z :=
  hQ.1

theorem IsIrreducible.eq_bot_or_eq_top
    {Q : ProjectiveRepresentation K G Z} (hQ : Q.IsIrreducible)
    (S : Submodule K Z) (hS : Q.IsStable S) :
    S = ⊥ ∨ S = ⊤ :=
  hQ.2 S hS

/-- Pulling back a projective representation can only weaken the stability
condition on a submodule. -/
theorem IsStable.comap
    {Q : ProjectiveRepresentation K G Z} {S : Submodule K Z}
    (hS : Q.IsStable S) (f : H →* G) :
    (Q.comap f).IsStable S := by
  intro h z hz
  exact hS (f h) hz

/-- The operators pulled back along `f` cover the operators of `Q` if every
original operator is equal, as a linear automorphism, to one occurring in the
pullback. -/
def OperatorsCoveredBy
    (Q : ProjectiveRepresentation K G Z) (f : H →* G) : Prop :=
  ∀ g : G, ∃ h : H, Q.operator g = Q.operator (f h)

/-- Under operator coverage, stability is unchanged by pullback. -/
theorem isStable_comap_iff
    (Q : ProjectiveRepresentation K G Z) (f : H →* G)
    (hcover : Q.OperatorsCoveredBy f) (S : Submodule K Z) :
    (Q.comap f).IsStable S ↔ Q.IsStable S := by
  constructor
  · intro hS g z hz
    obtain ⟨h, hoperator⟩ := hcover g
    rw [hoperator]
    exact hS h hz
  · intro hS
    exact hS.comap f

/-- Under operator coverage, a projective representation is irreducible
exactly when its pullback is irreducible. -/
theorem isIrreducible_iff_comap
    (Q : ProjectiveRepresentation K G Z) (f : H →* G)
    (hcover : Q.OperatorsCoveredBy f) :
    Q.IsIrreducible ↔ (Q.comap f).IsIrreducible := by
  constructor
  · intro hQ
    refine ⟨hQ.1, ?_⟩
    intro S hS
    exact hQ.2 S ((Q.isStable_comap_iff f hcover S).mp hS)
  · intro hQ
    refine ⟨hQ.1, ?_⟩
    intro S hS
    exact hQ.2 S ((Q.isStable_comap_iff f hcover S).mpr hS)

end ProjectiveRepresentation

namespace FactorMatchedIsomorphismWitness

local notation "CentralIsomorphismWitness" =>
  FactorMatchedIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z : Type}
variable [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
variable [AddCommGroup Z] [Module ℂ Z]

/-- An inverse-factor projective representation trivial on the left normal
subgroup has no new operators outside the embedded right ambient group. -/
theorem multiplicity_operator_eq_embedding
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T) (a : A) :
    ∃ b : B, Q.operator a = Q.operator (C.embedding b) := by
  obtain ⟨x, b, hxb⟩ := C.ambient_eq_product a
  refine ⟨b, ?_⟩
  have hfactor :
      Q.factor (x : A) (C.embedding b) = 1 := by
    rw [hQ, C.leftAssociated.factor_normal_left x, inv_one]
  have hmul := Q.map_mul (x : A) (C.embedding b)
  rw [htriv x, one_mul, hfactor, map_one, one_mul, hxb] at hmul
  exact hmul.symm

/-- The central-isomorphism embedding covers every operator of an
inverse-factor projective representation trivial on the normal subgroup. -/
theorem multiplicity_operatorsCoveredBy_embedding
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T) :
    Q.OperatorsCoveredBy C.embedding :=
  C.multiplicity_operator_eq_embedding Q hQ htriv

/-- Projective irreducibility of a multiplicity representation is unchanged
by restriction across the embedding of a central-isomorphism witness. -/
theorem multiplicity_isIrreducible_iff_comap
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T) :
    Q.IsIrreducible ↔ (Q.comap C.embedding).IsIrreducible :=
  Q.isIrreducible_iff_comap C.embedding
    (C.multiplicity_operatorsCoveredBy_embedding Q hQ htriv)

end FactorMatchedIsomorphismWitness

namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z : Type}
variable [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
variable [AddCommGroup Z] [Module ℂ Z]

export FactorMatchedIsomorphismWitness
  (multiplicity_operator_eq_embedding
    multiplicity_operatorsCoveredBy_embedding)

theorem multiplicity_isIrreducible_iff_comap
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T) :
    Q.IsIrreducible ↔ (Q.comap C.embedding).IsIrreducible :=
  C.toFactorMatchedIsomorphismWitness
    |>.multiplicity_isIrreducible_iff_comap Q hQ htriv

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
