/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorNormalization
import McKayConjecture.CharacterTriple.AssociatedGeneralExistence
import McKayConjecture.CharacterTriple.FactorSetCentralExtension
import McKayConjecture.CharacterTriple.FactorSetQuotient
import McKayConjecture.GroupTheory.CentralExtensionCentralIndex

/-!
# Finite quotient factor extensions attached to character triples

An associated projective representation has factor one whenever either
argument belongs to the normal subgroup.  After the association-preserving
finite-factor normalization, its roots-of-unity-valued factor therefore
descends to the outer quotient.  The resulting normalized finite factor set
defines a finite central extension of that quotient.

This is the group constructed at the start of the projective
central-extension reduction in Rossi's Lemma 4.1.
-/

noncomputable section

universe u x

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type u} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- Quotient compatibility of the finite roots-of-unity factor set. -/
theorem associatedFiniteFactorSet_isQuotientCompatible
    (R : AssociatedProjectiveRepresentation T V P) :
    R.associatedFiniteFactorSet.IsQuotientCompatible
      T.normalSubgroup where
  factor_normal_left x a := by
    apply Subtype.ext
    change
      R.associatedFiniteFactorProjective.factor
          (x : A) a = 1
    exact
      R.associatedFiniteFactorAssociated.factor_normal_left
        x a
  factor_normal_right a x := by
    apply Subtype.ext
    change
      R.associatedFiniteFactorProjective.factor
          a (x : A) = 1
    exact
      R.associatedFiniteFactorAssociated.factor_normal_right
        a x

/-- The finite roots-of-unity factor set descended to the quotient by the
normal subgroup of the character triple. -/
def associatedFiniteQuotientFactorSet
    (R : AssociatedProjectiveRepresentation T V P) :
    FactorSet (A ⧸ T.normalSubgroup)
      (rootsOfUnity (associatedFactorExponent T V) ℂ) :=
  R.associatedFiniteFactorSet.quotient
    R.associatedFiniteFactorSet_isQuotientCompatible

@[simp]
theorem associatedFiniteQuotientFactorSet_mk
    (R : AssociatedProjectiveRepresentation T V P)
    (a b : A) :
    R.associatedFiniteQuotientFactorSet
        (QuotientGroup.mk' T.normalSubgroup a)
        (QuotientGroup.mk' T.normalSubgroup b) =
      R.associatedFiniteFactorSet a b :=
  FactorSet.quotient_mk
    R.associatedFiniteFactorSet_isQuotientCompatible a b

@[simp]
theorem associatedFiniteQuotientFactorSet_mk_coe
    (R : AssociatedProjectiveRepresentation T V P)
    (a b : A) :
    ((R.associatedFiniteQuotientFactorSet
          (QuotientGroup.mk' T.normalSubgroup a)
          (QuotientGroup.mk' T.normalSubgroup b) :
        rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ) =
      R.associatedFiniteFactorProjective.factor a b := by
  rw [R.associatedFiniteQuotientFactorSet_mk]
  exact R.associatedFiniteFactorSet_coe a b

/-- The quotient factor remains normalized. -/
theorem associatedFiniteQuotientFactorSet_isNormalized
    (R : AssociatedProjectiveRepresentation T V P) :
    R.associatedFiniteQuotientFactorSet.IsNormalized :=
  FactorSet.quotient_isNormalized
    R.associatedFiniteFactorSet_isQuotientCompatible
    R.associatedFiniteFactorSet_isNormalized

/-- The finite central-extension group attached to an associated projective
representation and its normal quotient. -/
abbrev AssociatedFiniteFactorCentralExtensionGroup
    (R : AssociatedProjectiveRepresentation T V P) :=
  FactorSet.CentralExtensionGroup
    R.associatedFiniteQuotientFactorSet
    R.associatedFiniteQuotientFactorSet_isNormalized

/-- The canonical central extension of the character-triple quotient by
the finite factor group. -/
def associatedFiniteFactorCentralExtension
    (R : AssociatedProjectiveRepresentation T V P) :
    GroupTheory.CentralExtension
      R.AssociatedFiniteFactorCentralExtensionGroup
      (A ⧸ T.normalSubgroup) :=
  FactorSet.CentralExtensionGroup.centralExtension
    R.associatedFiniteQuotientFactorSet
    R.associatedFiniteQuotientFactorSet_isNormalized

/-- The central index of the finite factor extension is bounded by the
cardinality of the quotient on which the projective factor is defined. -/
theorem associatedFiniteFactorCentralExtension_centralIndex_le
    (R : AssociatedProjectiveRepresentation T V P) :
    GroupTheory.centralIndex
        R.AssociatedFiniteFactorCentralExtensionGroup ≤
      Nat.card (A ⧸ T.normalSubgroup) :=
  R.associatedFiniteFactorCentralExtension.centralIndex_le_card_target

/-- Any strict bound for the quotient cardinality gives the same strict
central-index descent for the finite factor extension. -/
theorem associatedFiniteFactorCentralExtension_centralIndex_lt
    (R : AssociatedProjectiveRepresentation T V P)
    {X : Type x} [Group X] [Finite X]
    (hquotient :
      Nat.card (A ⧸ T.normalSubgroup) <
        GroupTheory.centralIndex X) :
    GroupTheory.centralIndex
        R.AssociatedFiniteFactorCentralExtensionGroup <
      GroupTheory.centralIndex X :=
  R.associatedFiniteFactorCentralExtension_centralIndex_le.trans_lt
    hquotient

/-! ## Canonical extension for an arbitrary character triple -/

/-- The canonical associated lift supplied by the arbitrary-triple
existence theorem, followed by finite quotient-factor extension. -/
abbrev CanonicalFiniteFactorCentralExtensionGroup
    (T : CharacterTriple A) :=
  (AssociatedGeneralExistence.associated T
    ).AssociatedFiniteFactorCentralExtensionGroup

/-- The canonical finite central extension of the outer quotient of an
arbitrary character triple. -/
def canonicalFiniteFactorCentralExtension
    (T : CharacterTriple A) :
    GroupTheory.CentralExtension
      (CanonicalFiniteFactorCentralExtensionGroup T)
      (A ⧸ T.normalSubgroup) :=
  (AssociatedGeneralExistence.associated T
    ).associatedFiniteFactorCentralExtension

/-- If the normal subgroup of a character triple strictly contains the
ambient center, its canonical finite factor extension has strictly smaller
central index than the ambient group. -/
theorem canonicalFiniteFactorCentralExtension_centralIndex_lt
    (T : CharacterTriple A)
    (hcenter :
      Subgroup.center A < T.normalSubgroup) :
    GroupTheory.centralIndex
        (CanonicalFiniteFactorCentralExtensionGroup T) <
      GroupTheory.centralIndex A := by
  apply
    (AssociatedGeneralExistence.associated T
      ).associatedFiniteFactorCentralExtension_centralIndex_lt
  exact
    GroupTheory.card_quotient_lt_centralIndex_of_center_lt
      hcenter

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
