/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotientAlgebraLinearComparison
import McKayConjecture.Character.TwistedInteriorBrauerMultiplication

/-!
# The identity component of the twisted Brauer construction

When the interior action is the prescribed algebra action, the
identity twisted representation is that algebra action.  Consequently
the identity twisted Brauer component is canonically the underlying
module of the ordinary multiplicative Brauer quotient.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable (I : InteriorAction (P := P) (A := A))

/-- The identity twisted fixed submodule is canonically the fixed
subalgebra, as a `k`-module. -/
def twistedIdentityFixedEquiv :
    I.twistedFixedSubmodule (k := k) 1 ≃ₗ[k]
      fixedSubalgebra (k := k) (P := P) (A := A) :=
  (I.twistedInvariantsEquiv (k := k) 1).symm.trans
    ((invariantsLinearEquivOfRepresentationEq
      (I.twistedInteriorRepresentation_one (k := k))).trans
        (invariantsEquivFixedSubalgebra
          (k := k) (P := P) (A := A)))

omit [Fintype P] in
@[simp]
theorem coe_twistedIdentityFixedEquiv
    (a : I.twistedFixedSubmodule (k := k) 1) :
    ((I.twistedIdentityFixedEquiv (k := k) a :
        fixedSubalgebra (k := k) (P := P) (A := A)) : A) =
      a := by
  simp [twistedIdentityFixedEquiv]

omit [Fintype P] in
@[simp]
theorem coe_twistedIdentityFixedEquiv_symm
    (a : fixedSubalgebra (k := k) (P := P) (A := A)) :
    ((I.twistedIdentityFixedEquiv (k := k).symm a :
        I.twistedFixedSubmodule (k := k) 1) : A) =
      a := by
  have h :=
    I.coe_twistedIdentityFixedEquiv (k := k)
      ((I.twistedIdentityFixedEquiv (k := k)).symm a)
  rw [(I.twistedIdentityFixedEquiv
    (k := k)).apply_symm_apply] at h
  exact h.symm

/-- The identity twisted component and the ordinary algebra Brauer
quotient are canonically linearly equivalent. -/
def twistedBrauerIdentityEquiv :
    I.TwistedBrauerComponent (k := k) 1 ≃ₗ[k]
      BrauerQuotientAlgebra (k := k) (P := P) (A := A) :=
  (brauerQuotientLinearEquivOfRepresentationEq
      (I.twistedInteriorRepresentation_one (k := k))).trans
    (brauerQuotientAlgebraLinearEquiv
      (k := k) (P := P) (A := A)).symm

/-- The identity-component equivalence identifies the two quotient
projections. -/
@[simp]
theorem twistedBrauerIdentityEquiv_projection
    (a : I.twistedFixedSubmodule (k := k) 1) :
    I.twistedBrauerIdentityEquiv (k := k)
        (I.twistedBrauerProjection (k := k) 1 a) =
      brauerAlgebraProjection (k := k) (P := P) (A := A)
        (I.twistedIdentityFixedEquiv (k := k) a) := by
  simp only [twistedBrauerIdentityEquiv,
    LinearEquiv.trans_apply]
  simp only [twistedBrauerProjection, LinearMap.comp_apply]
  rw [brauerQuotientLinearEquivOfRepresentationEq_projection]
  apply
    (brauerQuotientAlgebraLinearEquiv
      (k := k) (P := P) (A := A)).injective
  rw [LinearEquiv.apply_symm_apply,
    brauerQuotientAlgebraLinearEquiv_projection]
  congr 1

/-- The multiplicative identity in the identity twisted component. -/
def twistedBrauerOne :
    I.TwistedBrauerComponent (k := k) 1 :=
  I.twistedBrauerProjection (k := k) 1
    ((I.twistedIdentityFixedEquiv (k := k)).symm 1)

/-- The identity-component equivalence carries the twisted identity
to the ordinary quotient identity. -/
@[simp]
theorem twistedBrauerIdentityEquiv_one :
    I.twistedBrauerIdentityEquiv (k := k)
        (I.twistedBrauerOne (k := k)) =
      1 := by
  rw [twistedBrauerOne,
    I.twistedBrauerIdentityEquiv_projection]
  simp

end InteriorAction
end Representation
