/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion
import McKayConjecture.Character.TrivialActionBrauerQuotient
import McKayConjecture.Character.TrivialEndomorphismInteriorAction

/-!
# Brauer-primitivity for trivial Dade actions

For a trivial action of a finite `p`-group in characteristic `p`, the
Brauer quotient is the original algebra.  A Dade algebra with this
action is therefore Brauer-primitive exactly when the algebra itself
is one-dimensional.

For the endomorphism algebra of a trivially acted-on module this says
more concretely that Brauer-primitivity forces the module to be a
line.  This prevents the invariant selected summand in the
Glauberman construction from being mistaken for the separate
primitive Dade algebra supplied by cross-characteristic reduction.
-/

noncomputable section

namespace Representation
namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A V : Type}
variable [Field k] [CharP k p]
variable [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- A Dade algebra with trivial action is Brauer-primitive exactly
when its underlying algebra has dimension one. -/
theorem isBrauerPrimitive_iff_finrank_eq_one_of_trivialAction
    [Finite P] :
    letI : Fintype P := Fintype.ofFinite P
    ∀ (S : DadeAlgebra p k P A),
      IsTrivialAlgebraAction P A →
        (S.IsBrauerPrimitive ↔ Module.finrank k A = 1) := by
  letI : Fintype P := Fintype.ofFinite P
  intro S htriv
  rw [
    ← S.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive]
  have hfinrank :=
    (brauerQuotientAlgebraEquivOfTrivialAction
      (p := p) (k := k) (P := P) (A := A)
      htriv S.isPGroup).toLinearEquiv.finrank_eq
  rw [hfinrank]

section Endomorphism

variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/-- Under the conjugation action of a trivial linear representation,
the endomorphism Dade algebra is Brauer-primitive exactly when the
underlying module is one-dimensional. -/
theorem
    endomorphism_isBrauerPrimitive_iff_finrank_eq_one_of_trivialLinearAction
    [Finite P] :
    letI : Fintype P := Fintype.ofFinite P
    letI : MulSemiringAction P (Module.End k V) :=
      endomorphismConjugationMulSemiringAction
        (trivialLinearAction (k := k) (P := P) (V := V))
    letI : SMulCommClass P k (Module.End k V) :=
      endomorphismConjugation_smulCommClass
        (trivialLinearAction (k := k) (P := P) (V := V))
    ∀ S : DadeAlgebra p k P (Module.End k V),
      S.IsBrauerPrimitive ↔ Module.finrank k V = 1 := by
  letI : Fintype P := Fintype.ofFinite P
  letI : MulSemiringAction P (Module.End k V) :=
    endomorphismConjugationMulSemiringAction
      (trivialLinearAction (k := k) (P := P) (V := V))
  letI : SMulCommClass P k (Module.End k V) :=
    endomorphismConjugation_smulCommClass
      (trivialLinearAction (k := k) (P := P) (V := V))
  intro S
  rw [
    S.isBrauerPrimitive_iff_finrank_eq_one_of_trivialAction
      isTrivialAlgebraAction_endomorphismConjugation_trivialLinearAction,
    Module.finrank_linearMap]
  constructor
  · exact Nat.eq_one_of_mul_eq_one_right
  · intro h
    rw [h, one_mul]

end Endomorphism
end DadeAlgebra
end Representation
