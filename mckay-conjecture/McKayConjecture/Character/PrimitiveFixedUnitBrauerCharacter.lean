/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerPrimitiveNormalizerExtensionCriterion
import McKayConjecture.Character.InteriorNormalizerFixedUnitQuotient

/-!
# The fixed-unit Brauer character in the primitive case

For a faithful interior action on a Brauer-primitive Dade algebra, the
Brauer quotient is one-dimensional.  The induced normalizer
automorphism of that quotient is therefore trivial.  It follows that
the fixed-unit Brauer projection is invariant under conjugation by
the entire interior unit normalizer.

Together with
`InteriorAction.fixedUnitRange_eq_faithfulNormalizerAction_ker`, this
isolates the remaining character-extension problem in group-theoretic
terms: one must extend an invariant character from the kernel of the
normalizer action to the whole normalizer.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable (I : InteriorAction (P := P) (A := A))

/-- Conjugation by an interior normalizer unit, on the unit group of
the fixed algebra. -/
def normalizerConjFixedUnit
    (s : I.unitNormalizer) :
    (fixedSubalgebra (k := k) (P := P) (A := A))ˣ →*
      (fixedSubalgebra (k := k) (P := P) (A := A))ˣ :=
  Units.map
    (I.normalizerConjFixedAlgEquiv (k := k) s).toMonoidHom

omit [Fintype P] in
@[simp]
theorem coe_normalizerConjFixedUnit
    (s : I.unitNormalizer)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    (I.normalizerConjFixedUnit (k := k) s u :
        fixedSubalgebra (k := k) (P := P) (A := A)) =
      I.normalizerConjFixedAlgEquiv (k := k) s u :=
  rfl

/-- In the faithful primitive case, the fixed-unit Brauer character
is invariant under every unit in the interior normalizer. -/
theorem fixedUnitBrauerProjection_normalizerConjFixedUnit
    (S : DadeAlgebra p k P A)
    (hI : Function.Injective I.unit)
    (hprimitive : S.IsBrauerPrimitive)
    (s : I.unitNormalizer)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    fixedUnitBrauerProjection (k := k) (P := P) (A := A)
        (I.normalizerConjFixedUnit (k := k) s u) =
      fixedUnitBrauerProjection (k := k) (P := P) (A := A) u := by
  apply Units.ext
  change
    brauerAlgebraProjection (k := k) (P := P) (A := A)
        (I.normalizerConjFixedAlgEquiv (k := k) s u) =
      brauerAlgebraProjection (k := k) (P := P) (A := A) u
  rw [← I.normalizerConjBrauerAlgEquiv_brauerAlgebraProjection
    hI s]
  rw [I.normalizerConjBrauerAlgEquiv_eq_refl_of_finrank_eq_one
    hI
    ((S.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive).2
      hprimitive)
    s]
  rfl

end InteriorAction
end Representation
