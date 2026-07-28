/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.RestrictionWitness
import McKayConjecture.InductiveMcKay.CentralTripleCliffordAssembly

/-!
# Complete central witnesses from a restricted projective lift

This file packages the restriction constructor for use by Clifford assembly.
It separates two independent inputs:

* `CentralRestrictionGroupData` contains the three ordinary group conditions
  for the specified embedding; and
* `CompleteProjectiveRestrictionData` contains one associated projective lift
  on the left whose restriction is associated to the right character.

Together they produce a `CompleteCentralIsomorphismWitness`.  In particular,
factor-set and scalar agreement are conclusions, not duplicated hypotheses.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A : Type} {B : Type}
variable [Finite A] [Group A] [Finite B] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}

/-- The purely group-theoretic part of a central witness for a fixed
embedding of the right ambient group into the left ambient group. -/
structure CentralRestrictionGroupData
    (T : CharacterTriple A) (U : CharacterTriple B)
    (e : B →* A) : Prop where
  /-- The right ambient group is identified with a subgroup of the left. -/
  embedding_injective : Function.Injective e
  /-- The left centralizer of the normal subgroup lies in that image. -/
  centralizer_le :
    Subgroup.centralizer
        (T.normalSubgroup : Set A) ≤
      MonoidHom.range e
  /-- The left ambient group is the product of its normal subgroup and the
  embedded right ambient group. -/
  ambient_eq_product :
    ∀ a : A,
      ∃ x : T.normalSubgroup,
        ∃ h : B, (x : A) * e h = a
  /-- The embedded right normal subgroup is the exact intersection. -/
  intersection_eq :
    T.normalSubgroup ⊓ MonoidHom.range e =
      U.normalSubgroup.map e

/-- One projective lift whose left restriction affords `T.character` and
whose pullback along `e` affords `U.character`.  The representation space and
all of its finite-dimensional structure are bundled. -/
structure CompleteProjectiveRestrictionData
    (T : CharacterTriple A) (U : CharacterTriple B)
    (e : B →* A) where
  /-- Common representation space for the lift and its restriction. -/
  space : Type
  [addCommGroup : AddCommGroup space]
  [module : Module ℂ space]
  [moduleFinite : Module.Finite ℂ space]
  [nontrivial : Nontrivial space]
  /-- Projective representation on the left ambient group. -/
  projective :
    ProjectiveRepresentation ℂ A space
  /-- Association to the left character triple. -/
  leftAssociated :
    AssociatedProjectiveRepresentation
      T space projective
  /-- Association of the restricted lift to the right character triple. -/
  rightAssociated :
    AssociatedProjectiveRepresentation
      U space (projective.comap e)

namespace CompleteProjectiveRestrictionData

variable {e : B →* A}

/-- A shared associated lift and the exact group conditions give a complete
central-isomorphism witness. -/
def toCompleteCentralIsomorphismWitness
    (d : CompleteProjectiveRestrictionData T U e)
    (g : CentralRestrictionGroupData T U e) :
    CompleteCentralIsomorphismWitness T U := by
  letI := d.addCommGroup
  letI := d.module
  letI := d.moduleFinite
  letI := d.nontrivial
  exact
    { leftSpace := d.space
      rightSpace := d.space
      witness :=
        CentralIsomorphismWitness.ofProjectiveRestriction
          d.leftAssociated e
          g.embedding_injective
          g.centralizer_le
          g.ambient_eq_product
          g.intersection_eq
          d.rightAssociated }

end CompleteProjectiveRestrictionData

end InductiveMcKay
end McKayConjecture
