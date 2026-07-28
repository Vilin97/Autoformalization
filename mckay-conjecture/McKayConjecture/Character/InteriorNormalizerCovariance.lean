/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InteriorFaithfulNormalizerAction
import McKayConjecture.Character.InteriorNormalizerConjugation

/-!
# Covariance of interior normalizer conjugation

For a faithful interior action, conjugation by a normalizing unit
intertwines the original algebra action with the induced automorphism
of the acting group.  This is the compatibility needed to transport
relative traces and descend normalizer conjugation to the Brauer
quotient.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

namespace InteriorAction

variable (I : InteriorAction (P := P) (A := A))

omit [SMulCommClass P k A] in
/-- Conjugation by a normalizing unit is covariant for the automorphism
that the unit induces on a faithfully represented interior group. -/
theorem unitConjugationAlgEquiv_smul
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer)
    (g : P)
    (a : A) :
    g • unitConjugationAlgEquiv (k := k) (s : Aˣ) a =
      unitConjugationAlgEquiv (k := k) (s : Aˣ)
        (I.normalizerMulAut hI s g • a) := by
  rw [I.smul_eq, I.smul_eq]
  simp only [unitConjugationAlgEquiv_apply,
    I.unit_normalizerMulAut]
  simp [mul_assoc]

omit [SMulCommClass P k A] in
/-- Direct covariance form: conjugating an acted-on element by `s`
is the action of the automorphism induced by `s⁻¹` on the conjugated
element. -/
theorem unitConjugationAlgEquiv_map_smul
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer)
    (g : P)
    (a : A) :
    unitConjugationAlgEquiv (k := k) (s : Aˣ) (g • a) =
      I.normalizerMulAut hI s⁻¹ g •
        unitConjugationAlgEquiv (k := k) (s : Aˣ) a := by
  rw [I.smul_eq, I.smul_eq]
  simp only [unitConjugationAlgEquiv_apply,
    I.unit_normalizerMulAut]
  simp [mul_assoc]

end InteriorAction
end Representation
