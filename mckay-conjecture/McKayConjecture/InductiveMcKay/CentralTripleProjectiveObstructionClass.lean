/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveObstructionClass
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveFactorCohomology

/-!
# Intrinsic projective obstruction along a central restriction

A central restriction identifies the two outer quotient groups.  The factor
part of a central character-triple comparison is therefore the equality of
the two intrinsic projective obstruction classes after transporting the
left class along that quotient identification.

The main theorem proves that this choice-free condition is equivalent to
`QuotientFactorH2ClassAgreement` for any independently chosen associated
projective lifts.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

namespace CentralRestrictionGroupData

/-- Equality of the intrinsic projective obstruction classes of two
centrally restricted triples, using the canonical quotient identification
provided by the ordinary group data. -/
def ProjectiveObstructionClassAgreement
    (g : CentralRestrictionGroupData T U e) : Prop :=
  (AssociatedGeneralExistence.associated T
    ).QuotientFactorH2ClassAgreement
      (AssociatedGeneralExistence.associated U) g

end CentralRestrictionGroupData

end InductiveMcKay

namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

open InductiveMcKay

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

/-- Factor-class agreement for arbitrary associated lifts is equivalent to
the intrinsic obstruction-class agreement of the two triples. -/
theorem quotientFactorH2ClassAgreement_iff_projectiveObstructionClass
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :
    R.QuotientFactorH2ClassAgreement S g ↔
      g.ProjectiveObstructionClassAgreement := by
  constructor
  · intro h
    exact
      R.quotientFactorH2ClassAgreement_congr
        (AssociatedGeneralExistence.associated T)
        S (AssociatedGeneralExistence.associated U)
        g h
  · intro h
    exact
      (AssociatedGeneralExistence.associated T
        ).quotientFactorH2ClassAgreement_congr
          R
          (AssociatedGeneralExistence.associated U) S
          g h

end AssociatedProjectiveRepresentation
end CharacterTriple

end McKayConjecture
