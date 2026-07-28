/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCorrespondence
import McKayConjecture.CharacterTriple.CentralQuotient
import McKayConjecture.CharacterTriple.ProjectiveLinearGroup

/-!
# Projective quotient action under a central triple isomorphism

A multiplicity-space projective representation is identity on the normal
subgroup, so its projective-linear action descends to the quotient.  The
canonical quotient isomorphism attached to a central character-triple
witness identifies the descended actions on the two sides exactly.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup Z] [Module ℂ Z]

/-- The projective-linear multiplicity action on `A / X`. -/
def leftQuotientProjectiveAction
    (_C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (htriv : Q.IsTrivialOnNormal T) :
    A ⧸ T.normalSubgroup →*
      ProjectiveLinearGroup ℂ Z :=
  Q.quotientProjectiveLinearGroup T.normalSubgroup htriv

/-- The restricted projective-linear multiplicity action on `B / M`. -/
def rightQuotientProjectiveAction
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (htriv : Q.IsTrivialOnNormal T) :
    B ⧸ U.normalSubgroup →*
      ProjectiveLinearGroup ℂ Z :=
  (Q.comap C.embedding).quotientProjectiveLinearGroup
    U.normalSubgroup (C.right_isTrivialOnNormal Q htriv)

@[simp]
theorem leftQuotientProjectiveAction_mk
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (htriv : Q.IsTrivialOnNormal T) (a : A) :
    C.leftQuotientProjectiveAction Q htriv
        (QuotientGroup.mk' T.normalSubgroup a) =
      Q.toProjectiveLinearGroup a :=
  rfl

@[simp]
theorem rightQuotientProjectiveAction_mk
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (htriv : Q.IsTrivialOnNormal T) (b : B) :
    C.rightQuotientProjectiveAction Q htriv
        (QuotientGroup.mk' U.normalSubgroup b) =
      Q.toProjectiveLinearGroup (C.embedding b) :=
  rfl

/-- The quotient isomorphism identifies the two descended projective
actions. -/
theorem rightQuotientProjectiveAction_eq_comp
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (htriv : Q.IsTrivialOnNormal T) :
    C.rightQuotientProjectiveAction Q htriv =
      (C.leftQuotientProjectiveAction Q htriv).comp
        C.quotientEquiv.toMonoidHom := by
  ext b
  rfl

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
