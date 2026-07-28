/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InteriorAlgebra
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The normalizer action of a faithful interior action

When the implementing homomorphism of an interior action is injective,
it identifies the acting group with its image in the unit group.  Thus
conjugation by a unit normalizing that image induces an automorphism of
the original acting group.

This file constructs the resulting homomorphism

`N_{Aˣ}(I(P)) → Aut(P)`

and records its defining conjugation formula.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

namespace InteriorAction

variable (I : InteriorAction (P := P) (A := A))

/-- For a faithful interior action, the implementing homomorphism
identifies the acting group with its image in the ambient unit group. -/
def unitRangeMulEquiv
    (hI : Function.Injective I.unit) :
    P ≃* I.unitRange :=
  MonoidHom.ofInjective hI

@[simp]
theorem coe_unitRangeMulEquiv
    (hI : Function.Injective I.unit)
    (g : P) :
    ((I.unitRangeMulEquiv hI g : I.unitRange) : Aˣ) =
      I.unit g :=
  MonoidHom.ofInjective_apply hI

/-- The action of the interior unit normalizer on the original acting
group, obtained by transporting its conjugation action on the image of
the implementing homomorphism. -/
def faithfulNormalizerAction
    (hI : Function.Injective I.unit) :
    I.unitNormalizer →* MulAut P :=
  (MulAut.congr (I.unitRangeMulEquiv hI)).symm.toMonoidHom.comp
    I.unitRange.normalizerMonoidHom

/-- The automorphism induced by one unit in the interior normalizer. -/
def normalizerMulAut
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    MulAut P :=
  I.faithfulNormalizerAction hI s

@[simp]
theorem unit_normalizerMulAut
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer)
    (g : P) :
    I.unit (I.normalizerMulAut hI s g) =
      (s : Aˣ) * I.unit g * (s : Aˣ)⁻¹ := by
  change
    ((I.unitRangeMulEquiv hI
        (I.normalizerMulAut hI s g) : I.unitRange) : Aˣ) =
      (s : Aˣ) * I.unit g * (s : Aˣ)⁻¹
  simp [normalizerMulAut, faithfulNormalizerAction]

end InteriorAction
end Representation
