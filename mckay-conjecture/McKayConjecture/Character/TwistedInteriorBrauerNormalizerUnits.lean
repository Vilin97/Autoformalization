/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwistedInteriorBrauerIdentity

/-!
# Homogeneous Brauer classes of interior normalizer units

A unit normalizing a faithful interior action determines a homogeneous
class in the twisted Brauer component indexed by its induced
automorphism.  Multiplication of normalizer units agrees with the
componentwise twisted Brauer multiplication.

The fibers are pulled back from `Aut(P)` to the unit normalizer.  In
this pullback grading the class of `s⁻¹` is a two-sided homogeneous
inverse to the class of `s`.  This conclusion does not require the
ordinary Brauer quotient to be nonzero.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable (I : InteriorAction (P := P) (A := A))

/-- Transport between twisted fixed submodules indexed by equal
automorphisms. -/
def twistedFixedEquivOfEq
    {φ ψ : MulAut P}
    (h : φ = ψ) :
    I.twistedFixedSubmodule (k := k) φ ≃ₗ[k]
      I.twistedFixedSubmodule (k := k) ψ := by
  subst ψ
  exact LinearEquiv.refl k _

omit [Fintype P] [SMulCommClass P k A] in
@[simp]
theorem coe_twistedFixedEquivOfEq
    {φ ψ : MulAut P}
    (h : φ = ψ)
    (a : I.twistedFixedSubmodule (k := k) φ) :
    ((I.twistedFixedEquivOfEq (k := k) h a :
        I.twistedFixedSubmodule (k := k) ψ) : A) =
      a := by
  subst ψ
  rfl

/-- Transport between twisted Brauer components indexed by equal
automorphisms. -/
def twistedBrauerComponentEquivOfEq
    {φ ψ : MulAut P}
    (h : φ = ψ) :
    I.TwistedBrauerComponent (k := k) φ ≃ₗ[k]
      I.TwistedBrauerComponent (k := k) ψ := by
  subst ψ
  exact LinearEquiv.refl k _

omit [SMulCommClass P k A] in
/-- Component transport commutes with the quotient projection. -/
@[simp]
theorem twistedBrauerComponentEquivOfEq_projection
    {φ ψ : MulAut P}
    (h : φ = ψ)
    (a : I.twistedFixedSubmodule (k := k) φ) :
    I.twistedBrauerComponentEquivOfEq (k := k) h
        (I.twistedBrauerProjection (k := k) φ a) =
      I.twistedBrauerProjection (k := k) ψ
        (I.twistedFixedEquivOfEq (k := k) h a) := by
  subst ψ
  rfl

omit [Fintype P] in
/-- The automorphism induced by a product of normalizer units is the
product of their induced automorphisms. -/
@[simp]
theorem normalizerMulAut_mul
    (hI : Function.Injective I.unit)
    (s t : I.unitNormalizer) :
    I.normalizerMulAut hI (s * t) =
      I.normalizerMulAut hI s *
        I.normalizerMulAut hI t :=
  map_mul (I.faithfulNormalizerAction hI) s t

omit [Fintype P] in
/-- The identity normalizer unit induces the identity automorphism. -/
@[simp]
theorem normalizerMulAut_one
    (hI : Function.Injective I.unit) :
    I.normalizerMulAut hI 1 = 1 :=
  map_one (I.faithfulNormalizerAction hI)

omit [Fintype P] in
/-- Inversion of a normalizer unit induces inversion of its
automorphism. -/
@[simp]
theorem normalizerMulAut_inv
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    I.normalizerMulAut hI s⁻¹ =
      (I.normalizerMulAut hI s)⁻¹ :=
  map_inv (I.faithfulNormalizerAction hI) s

/-- The twisted Brauer family pulled back along the normalizer action
on `P`. -/
abbrev UnitNormalizerTwistedBrauerFiber
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :=
  I.TwistedBrauerComponent (k := k)
    (I.normalizerMulAut hI s)

/-- Multiplication in the normalizer-pullback twisted Brauer family. -/
def unitNormalizerTwistedBrauerMul
    (hI : Function.Injective I.unit)
    (s t : I.unitNormalizer)
    (x : I.UnitNormalizerTwistedBrauerFiber (k := k) hI s)
    (y : I.UnitNormalizerTwistedBrauerFiber (k := k) hI t) :
    I.UnitNormalizerTwistedBrauerFiber (k := k) hI (s * t) :=
  I.twistedBrauerComponentEquivOfEq (k := k)
      (I.normalizerMulAut_mul hI s t).symm
    (I.twistedBrauerMul (k := k)
      (I.normalizerMulAut hI s)
      (I.normalizerMulAut hI t) x y)

omit [SMulCommClass P k A] in
/-- Normalizer representatives are multiplicative homogeneous
classes. -/
@[simp]
theorem unitNormalizerTwistedBrauerMul_class
    (hI : Function.Injective I.unit)
    (s t : I.unitNormalizer) :
    I.unitNormalizerTwistedBrauerMul (k := k) hI s t
        (I.unitNormalizerTwistedBrauerClass (k := k) hI s)
        (I.unitNormalizerTwistedBrauerClass (k := k) hI t) =
      I.unitNormalizerTwistedBrauerClass (k := k) hI (s * t) := by
  simp only [unitNormalizerTwistedBrauerMul,
    unitNormalizerTwistedBrauerClass]
  rw [
    twistedBrauerMul_projection,
    twistedBrauerComponentEquivOfEq_projection]
  apply congrArg
    (I.twistedBrauerProjection (k := k)
      (I.normalizerMulAut hI (s * t)))
  apply Subtype.ext
  simp

/-- Transport in the pullback family along equality of normalizer
units. -/
def unitNormalizerTwistedBrauerFiberEquivOfEq
    (hI : Function.Injective I.unit)
    {s t : I.unitNormalizer}
    (h : s = t) :
    I.UnitNormalizerTwistedBrauerFiber (k := k) hI s ≃ₗ[k]
      I.UnitNormalizerTwistedBrauerFiber (k := k) hI t :=
  I.twistedBrauerComponentEquivOfEq (k := k)
    (congrArg (I.normalizerMulAut hI) h)

omit [SMulCommClass P k A] in
/-- Pullback-fiber transport carries a normalizer class to the class
of the equal normalizer unit. -/
@[simp]
theorem unitNormalizerTwistedBrauerFiberEquivOfEq_class
    (hI : Function.Injective I.unit)
    {s t : I.unitNormalizer}
    (h : s = t) :
    I.unitNormalizerTwistedBrauerFiberEquivOfEq
        (k := k) hI h
        (I.unitNormalizerTwistedBrauerClass (k := k) hI s) =
      I.unitNormalizerTwistedBrauerClass (k := k) hI t := by
  subst t
  rfl

/-- The identity class in the normalizer-pullback twisted Brauer
family. -/
def unitNormalizerTwistedBrauerOne
    (hI : Function.Injective I.unit) :
    I.UnitNormalizerTwistedBrauerFiber (k := k) hI 1 :=
  I.unitNormalizerTwistedBrauerClass (k := k) hI 1

/-- Multiply fibers of `s` and `s⁻¹`, then identify the result with
the identity fiber. -/
def unitNormalizerTwistedBrauerMulInv
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer)
    (x : I.UnitNormalizerTwistedBrauerFiber (k := k) hI s)
    (y : I.UnitNormalizerTwistedBrauerFiber (k := k) hI s⁻¹) :
    I.UnitNormalizerTwistedBrauerFiber (k := k) hI 1 :=
  I.unitNormalizerTwistedBrauerFiberEquivOfEq
      (k := k) hI (mul_inv_cancel s)
    (I.unitNormalizerTwistedBrauerMul
      (k := k) hI s s⁻¹ x y)

/-- Multiply fibers of `s⁻¹` and `s`, then identify the result with
the identity fiber. -/
def unitNormalizerTwistedBrauerInvMul
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer)
    (x : I.UnitNormalizerTwistedBrauerFiber (k := k) hI s⁻¹)
    (y : I.UnitNormalizerTwistedBrauerFiber (k := k) hI s) :
    I.UnitNormalizerTwistedBrauerFiber (k := k) hI 1 :=
  I.unitNormalizerTwistedBrauerFiberEquivOfEq
      (k := k) hI (inv_mul_cancel s)
    (I.unitNormalizerTwistedBrauerMul
      (k := k) hI s⁻¹ s x y)

omit [SMulCommClass P k A] in
/-- The class induced by the group inverse is a right homogeneous
inverse. -/
@[simp]
theorem unitNormalizerTwistedBrauerClass_mul_inv
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    I.unitNormalizerTwistedBrauerMulInv (k := k) hI s
        (I.unitNormalizerTwistedBrauerClass (k := k) hI s)
        (I.unitNormalizerTwistedBrauerClass (k := k) hI s⁻¹) =
      I.unitNormalizerTwistedBrauerOne (k := k) hI := by
  rw [unitNormalizerTwistedBrauerMulInv,
    unitNormalizerTwistedBrauerMul_class,
    unitNormalizerTwistedBrauerFiberEquivOfEq_class]
  rfl

omit [SMulCommClass P k A] in
/-- The class induced by the group inverse is a left homogeneous
inverse. -/
@[simp]
theorem unitNormalizerTwistedBrauerClass_inv_mul
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    I.unitNormalizerTwistedBrauerInvMul (k := k) hI s
        (I.unitNormalizerTwistedBrauerClass (k := k) hI s⁻¹)
        (I.unitNormalizerTwistedBrauerClass (k := k) hI s) =
      I.unitNormalizerTwistedBrauerOne (k := k) hI := by
  rw [unitNormalizerTwistedBrauerInvMul,
    unitNormalizerTwistedBrauerMul_class,
    unitNormalizerTwistedBrauerFiberEquivOfEq_class]
  rfl

/-- A two-sided unit in the pullback-graded twisted Brauer family.
The inverse lies in the fiber indexed by the inverse normalizer
element. -/
structure UnitNormalizerTwistedBrauerHomogeneousUnit
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) where
  /-- The homogeneous value in degree `s`. -/
  val :
    I.UnitNormalizerTwistedBrauerFiber (k := k) hI s
  /-- The homogeneous inverse in degree `s⁻¹`. -/
  inv :
    I.UnitNormalizerTwistedBrauerFiber (k := k) hI s⁻¹
  /-- Right inverse identity. -/
  val_inv :
    I.unitNormalizerTwistedBrauerMulInv (k := k)
        hI s val inv =
      I.unitNormalizerTwistedBrauerOne (k := k) hI
  /-- Left inverse identity. -/
  inv_val :
    I.unitNormalizerTwistedBrauerInvMul (k := k)
        hI s inv val =
      I.unitNormalizerTwistedBrauerOne (k := k) hI

/-- Every interior normalizer unit gives a homogeneous unit, with
inverse represented by its group inverse. -/
def unitNormalizerTwistedBrauerHomogeneousUnit
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    I.UnitNormalizerTwistedBrauerHomogeneousUnit (k := k) hI s where
  val :=
    I.unitNormalizerTwistedBrauerClass (k := k) hI s
  inv :=
    I.unitNormalizerTwistedBrauerClass (k := k) hI s⁻¹
  val_inv :=
    I.unitNormalizerTwistedBrauerClass_mul_inv (k := k) hI s
  inv_val :=
    I.unitNormalizerTwistedBrauerClass_inv_mul (k := k) hI s

/-- After transporting the pullback identity fiber to degree `1`,
its distinguished class is the identity of the twisted Brauer
construction. -/
theorem unitNormalizerTwistedBrauerOne_eq_twistedBrauerOne
    (hI : Function.Injective I.unit) :
    I.twistedBrauerComponentEquivOfEq (k := k)
        (I.normalizerMulAut_one hI)
        (I.unitNormalizerTwistedBrauerOne (k := k) hI) =
      I.twistedBrauerOne (k := k) := by
  rw [unitNormalizerTwistedBrauerOne,
    unitNormalizerTwistedBrauerClass,
    twistedBrauerOne,
    twistedBrauerComponentEquivOfEq_projection]
  apply congrArg (I.twistedBrauerProjection (k := k) 1)
  apply Subtype.ext
  simp

/-- The pullback identity class maps to `1` in the ordinary algebra
Brauer quotient. -/
@[simp]
theorem twistedBrauerIdentityEquiv_unitNormalizerOne
    (hI : Function.Injective I.unit) :
    I.twistedBrauerIdentityEquiv (k := k)
        (I.twistedBrauerComponentEquivOfEq (k := k)
          (I.normalizerMulAut_one hI)
          (I.unitNormalizerTwistedBrauerOne (k := k) hI)) =
      1 := by
  rw [I.unitNormalizerTwistedBrauerOne_eq_twistedBrauerOne hI]
  exact I.twistedBrauerIdentityEquiv_one (k := k)

end InteriorAction
end Representation
