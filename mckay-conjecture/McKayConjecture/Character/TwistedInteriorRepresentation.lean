/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwistedInteriorFixedSubmodule
import Mathlib.RepresentationTheory.Invariants

/-!
# Twisted interior representations

For an interior action `I` of `P` on `A` and an automorphism `φ` of
`P`, the formula

`g • a = I(φ(g)) a I(g)⁻¹`

defines a linear representation of `P` on `A`.  Its invariant
submodule is exactly the `φ`-twisted fixed submodule introduced in
`TwistedInteriorFixedSubmodule`.

This representation lets the ordinary relative-trace and Brauer-module
API be reused componentwise in the extended Brauer construction.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A]

variable (I : InteriorAction (P := P) (A := A))

/-- The invertible linear operator
`a ↦ I(φ(g)) a I(g)⁻¹`. -/
def twistedInteriorLinearEquiv
    (φ : MulAut P)
    (g : P) :
    A ≃ₗ[k] A where
  toFun a :=
    (I.unit (φ g) : A) * a *
      (↑((I.unit g)⁻¹) : A)
  invFun a :=
    (↑((I.unit (φ g))⁻¹) : A) * a *
      (I.unit g : A)
  left_inv a := by simp [mul_assoc]
  right_inv a := by simp [mul_assoc]
  map_add' a b := by
    simp only [mul_add, add_mul]
  map_smul' r a := by
    simp only [Algebra.smul_def]
    calc
      (I.unit (φ g) : A) *
            (algebraMap k A r * a) *
          (↑((I.unit g)⁻¹) : A) =
          (algebraMap k A r * (I.unit (φ g) : A)) *
            a * (↑((I.unit g)⁻¹) : A) := by
        rw [← mul_assoc
          (I.unit (φ g) : A) (algebraMap k A r) a,
          (Algebra.commutes r
          (I.unit (φ g) : A)).symm]
      _ =
          algebraMap k A r *
            ((I.unit (φ g) : A) * a *
              (↑((I.unit g)⁻¹) : A)) := by
        simp only [mul_assoc]

@[simp]
theorem twistedInteriorLinearEquiv_apply
    (φ : MulAut P)
    (g : P)
    (a : A) :
    I.twistedInteriorLinearEquiv (k := k) φ g a =
      (I.unit (φ g) : A) * a *
        (↑((I.unit g)⁻¹) : A) :=
  rfl

/-- The linear representation associated with the `φ`-twisted
interior action. -/
def twistedInteriorRepresentation
    (φ : MulAut P) :
    Representation k P A where
  toFun g := I.twistedInteriorLinearEquiv (k := k) φ g
  map_one' := by
    apply LinearMap.ext
    intro a
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro a
    simp only [Module.End.mul_apply]
    simp [mul_assoc]

@[simp]
theorem twistedInteriorRepresentation_apply
    (φ : MulAut P)
    (g : P)
    (a : A) :
    I.twistedInteriorRepresentation (k := k) φ g a =
      (I.unit (φ g) : A) * a *
        (↑((I.unit g)⁻¹) : A) :=
  rfl

/-- The invariant submodule of the twisted interior representation is
the corresponding twisted fixed submodule. -/
theorem invariants_twistedInteriorRepresentation
    (φ : MulAut P) :
    invariants (I.twistedInteriorRepresentation (k := k) φ) =
      I.twistedFixedSubmodule (k := k) φ := by
  ext a
  constructor
  · intro ha
    rw [mem_twistedFixedSubmodule (k := k)]
    intro g
    have hg := ha g
    change
      (I.unit (φ g) : A) * a *
          (↑((I.unit g)⁻¹) : A) =
        a at hg
    calc
      a * (I.unit g : A) =
          ((I.unit (φ g) : A) * a *
              (↑((I.unit g)⁻¹) : A)) *
            (I.unit g : A) := by rw [hg]
      _ = (I.unit (φ g) : A) * a := by
        simp [mul_assoc]
  · intro ha g
    rw [mem_twistedFixedSubmodule (k := k)] at ha
    change
      (I.unit (φ g) : A) * a *
          (↑((I.unit g)⁻¹) : A) =
        a
    rw [← ha g]
    simp [mul_assoc]

end InteriorAction
end Representation
