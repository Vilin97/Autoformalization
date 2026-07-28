/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedExistence
import McKayConjecture.InductiveMcKay.SemidirectStructure

/-!
# Canonical projective data for the inductive McKay condition

The associated-existence theorem supplies normalized projective
representations on both sides of every proposed local character
correspondence.  Consequently, central character-triple compatibility
reduces to equality of their chosen factor sets and scalar actions.
-/

noncomputable section

universe u

namespace McKayConjecture.InductiveMcKay

open McKayConjecture.CharacterTriple

variable {G : Type u} [Group G] [Finite G] {p : ℕ}
  {P : Sylow p G}

namespace EquivariantLocalCorrespondence

/-- The canonical associated projective representation on
`G ⋊ Γ_χ`. -/
abbrev canonicalAmbientProjective
    (_d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    ProjectiveRepresentation ℂ
      (G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ)
      χ.1.realization :=
  AssociatedExistence.projectiveRepresentation
    PPrimeCharacterStabilizer.ambientAction χ.1
      PPrimeCharacterStabilizer.character_invariant

/-- The canonical associated projective representation on
`N ⋊ Γ_χ`. -/
abbrev canonicalIntermediateProjective
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    ProjectiveRepresentation ℂ
      (d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ)
      (d.localCharacter χ).1.realization :=
  AssociatedExistence.projectiveRepresentation
    (d.stabilizerIntermediateAction χ)
    (d.localCharacter χ).1
    (d.localCharacter_invariant χ)

/-- The two remaining equations for the canonical associated projective
representations.

All group-theoretic central-isomorphism clauses and both association
certificates are automatic.
-/
structure CanonicalProjectiveCompatibility
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) : Prop where
  /-- Equality of the two canonical factor sets on `Γ_χ × Γ_χ`. -/
  factorAgreement :
    ∀ a b : PPrimeCharacterStabilizer P χ,
      AssociatedExistence.intertwinerFactor
          PPrimeCharacterStabilizer.ambientAction χ.1
            PPrimeCharacterStabilizer.character_invariant a b =
        AssociatedExistence.intertwinerFactor
          (d.stabilizerIntermediateAction χ)
          (d.localCharacter χ).1
          (d.localCharacter_invariant χ) a b
  /-- Equality of scalar actions on the centralizer. -/
  scalarAgreement :
    ∀ h :
      d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ,
      d.semidirectEmbedding χ h ∈
          Subgroup.centralizer
            ((ambientTriple (P := P) χ).normalSubgroup :
              Set
                (G ⋊[PPrimeCharacterStabilizer.ambientAction]
                  PPrimeCharacterStabilizer P χ)) →
        ∃ c : ℂˣ,
          (d.canonicalAmbientProjective χ).operator
              (d.semidirectEmbedding χ h) =
              scalarLinearEquiv ℂ χ.1.realization c ∧
            (d.canonicalIntermediateProjective χ).operator h =
              scalarLinearEquiv ℂ
                (d.localCharacter χ).1.realization c

namespace CanonicalProjectiveCompatibility

variable {d : EquivariantLocalCorrespondence P}
  {χ : PPrimeIrreducibleCharacter G p}

/-- Package the canonical factor/scalar equations as the reduced projective
compatibility witness. -/
def toProjectiveCompatibilityWitness
    (C : CanonicalProjectiveCompatibility d χ) :
    ProjectiveCompatibilityWitness d χ
      χ.1.realization (d.localCharacter χ).1.realization where
  leftProjective := d.canonicalAmbientProjective χ
  leftAssociated :=
    AssociatedExistence.associated
      PPrimeCharacterStabilizer.ambientAction χ.1
        PPrimeCharacterStabilizer.character_invariant
  rightProjective := d.canonicalIntermediateProjective χ
  rightAssociated :=
    AssociatedExistence.associated
      (d.stabilizerIntermediateAction χ)
      (d.localCharacter χ).1
      (d.localCharacter_invariant χ)
  factorAgreement := by
    intro h k
    exact C.factorAgreement h.right k.right
  scalarAgreement := C.scalarAgreement

/-- Canonical factor/scalar compatibility proves the complete
character-triple clause of inductive McKay. -/
theorem tripleCompatible
    (C : CanonicalProjectiveCompatibility d χ) :
    d.TripleCompatible χ :=
  C.toProjectiveCompatibilityWitness.tripleCompatible

end CanonicalProjectiveCompatibility
end EquivariantLocalCorrespondence
end McKayConjecture.InductiveMcKay
