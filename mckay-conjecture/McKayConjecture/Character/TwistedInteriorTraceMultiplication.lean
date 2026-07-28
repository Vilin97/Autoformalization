/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerRelativeTraceIntertwining
import McKayConjecture.Character.TwistedInteriorBrauerComponent

/-!
# Multiplication and twisted relative traces

Left multiplication by a globally `φ`-twisted fixed element carries a
`ψ`-twisted relative trace from `Q` to the corresponding
`φ * ψ`-twisted relative trace from the same subgroup.  This is the
first trace-product identity needed to descend the graded
multiplication to twisted Brauer components.
-/

noncomputable section

open scoped BigOperators

namespace Representation
namespace InteriorAction

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A]

variable (I : InteriorAction (P := P) (A := A))

noncomputable local instance twistedTraceLeftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- Multiplication by a globally `φ`-twisted fixed element sends
`Q`-invariants of the `ψ`-twisted representation to `Q`-invariants of
the `(φ * ψ)`-twisted representation. -/
def leftMulTwistedRestrictedInvariant
    {φ ψ : MulAut P}
    (a : I.twistedFixedSubmodule (k := k) φ)
    (Q : Subgroup P)
    (x :
      invariants
        ((I.twistedInteriorRepresentation (k := k) ψ).comp
          Q.subtype)) :
    invariants
      ((I.twistedInteriorRepresentation (k := k) (φ * ψ)).comp
        Q.subtype) where
  val := (a : A) * (x : A)
  property q := by
    have ha :
        (I.unit (φ (ψ (q : P))) : A) * (a : A) =
          (a : A) * (I.unit (ψ (q : P)) : A) :=
      (a.property (ψ (q : P))).symm
    have hx := x.property q
    change
      (I.unit (ψ (q : P)) : A) * (x : A) *
          (↑((I.unit (q : P))⁻¹) : A) =
        (x : A) at hx
    change
      (I.unit ((φ * ψ) (q : P)) : A) *
            ((a : A) * (x : A)) *
          (↑((I.unit (q : P))⁻¹) : A) =
        (a : A) * (x : A)
    rw [MulAut.mul_apply]
    calc
      (I.unit (φ (ψ (q : P))) : A) *
            ((a : A) * (x : A)) *
          (↑((I.unit (q : P))⁻¹) : A) =
          ((I.unit (φ (ψ (q : P))) : A) * (a : A)) *
            (x : A) *
              (↑((I.unit (q : P))⁻¹) : A) := by
        simp only [mul_assoc]
      _ =
          ((a : A) * (I.unit (ψ (q : P)) : A)) *
            ((x : A)) *
          (↑((I.unit (q : P))⁻¹) : A) := by
        rw [ha]
      _ =
          (a : A) *
            ((I.unit (ψ (q : P)) : A) * (x : A) *
              (↑((I.unit (q : P))⁻¹) : A)) := by
        simp only [mul_assoc]
      _ = (a : A) * (x : A) := by rw [hx]

omit [Fintype P] in
@[simp]
theorem coe_leftMulTwistedRestrictedInvariant
    {φ ψ : MulAut P}
    (a : I.twistedFixedSubmodule (k := k) φ)
    (Q : Subgroup P)
    (x :
      invariants
        ((I.twistedInteriorRepresentation (k := k) ψ).comp
          Q.subtype)) :
    (I.leftMulTwistedRestrictedInvariant
        (k := k) a Q x : A) =
      (a : A) * (x : A) :=
  rfl

/-- Left multiplication commutes with twisted relative trace, with
the grading automorphisms multiplied in the same order. -/
theorem twistedFixedMul_twistedRelativeTrace
    {φ ψ : MulAut P}
    (a : I.twistedFixedSubmodule (k := k) φ)
    (Q : Subgroup P)
    (x :
      invariants
        ((I.twistedInteriorRepresentation (k := k) ψ).comp
          Q.subtype)) :
    I.twistedFixedMul (k := k) a
        (I.twistedRelativeTrace (k := k) ψ Q x) =
      I.twistedRelativeTrace (k := k) (φ * ψ) Q
        (I.leftMulTwistedRestrictedInvariant
          (k := k) a Q x) := by
  apply Subtype.ext
  change
    (a : A) *
        (∑ c : P ⧸ Q,
          (I.unit (ψ c.out) : A) * (x : A) *
            (↑((I.unit c.out)⁻¹) : A)) =
      ∑ c : P ⧸ Q,
        (I.unit ((φ * ψ) c.out) : A) *
            ((a : A) * (x : A)) *
          (↑((I.unit c.out)⁻¹) : A)
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro c
  have ha := a.property (ψ c.out)
  calc
    (a : A) *
        ((I.unit (ψ c.out) : A) * (x : A) *
          (↑((I.unit c.out)⁻¹) : A)) =
        ((a : A) * (I.unit (ψ c.out) : A)) *
          (x : A) * (↑((I.unit c.out)⁻¹) : A) := by
      simp only [mul_assoc]
    _ =
        ((I.unit (φ (ψ c.out)) : A) * (a : A)) *
          (x : A) * (↑((I.unit c.out)⁻¹) : A) := by
      rw [ha]
    _ =
        (I.unit ((φ * ψ) c.out) : A) *
            ((a : A) * (x : A)) *
          (↑((I.unit c.out)⁻¹) : A) := by
      simp only [MulAut.mul_apply, mul_assoc]

/-- Consequently, the product of a twisted fixed element with a
proper relative trace vanishes in the product Brauer component. -/
theorem twistedBrauerProjection_twistedFixedMul_twistedRelativeTrace
    {φ ψ : MulAut P}
    (a : I.twistedFixedSubmodule (k := k) φ)
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x :
      invariants
        ((I.twistedInteriorRepresentation (k := k) ψ).comp
          Q.subtype)) :
    I.twistedBrauerProjection (k := k) (φ * ψ)
        (I.twistedFixedMul (k := k) a
          (I.twistedRelativeTrace (k := k) ψ Q x)) =
      0 := by
  rw [I.twistedFixedMul_twistedRelativeTrace
    (k := k) a Q x]
  exact
    I.twistedBrauerProjection_twistedRelativeTrace
      (k := k) (φ * ψ) Q hQ
      (I.leftMulTwistedRestrictedInvariant
        (k := k) a Q x)

/-- Right multiplication by a `ψ`-twisted fixed element, as a linear
map on the ambient algebra. -/
def rightMulTwistedLinearMap
    {ψ : MulAut P}
    (b : I.twistedFixedSubmodule (k := k) ψ) :
    A →ₗ[k] A :=
  LinearMap.mulRight k (b : A)

omit [Fintype P] in
@[simp]
theorem rightMulTwistedLinearMap_apply
    {ψ : MulAut P}
    (b : I.twistedFixedSubmodule (k := k) ψ)
    (a : A) :
    I.rightMulTwistedLinearMap (k := k) b a =
      a * (b : A) :=
  rfl

omit [Fintype P] in
/-- Right multiplication by a `ψ`-twisted fixed element intertwines
the `φ`-twisted representation with the `(φ * ψ)`-twisted
representation along `ψ⁻¹`. -/
theorem rightMulTwistedLinearMap_compatible
    {φ ψ : MulAut P}
    (b : I.twistedFixedSubmodule (k := k) ψ)
    (g : P)
    (a : A) :
    I.rightMulTwistedLinearMap (k := k) b
        (I.twistedInteriorRepresentation (k := k) φ g a) =
      I.twistedInteriorRepresentation (k := k) (φ * ψ)
        (ψ.symm g)
        (I.rightMulTwistedLinearMap (k := k) b a) := by
  have hb :
      (b : A) * (I.unit (ψ.symm g) : A) =
        (I.unit g : A) * (b : A) := by
    simpa using b.property (ψ.symm g)
  have hinv :
      (↑((I.unit g)⁻¹) : A) * (b : A) =
        (b : A) *
          (↑((I.unit (ψ.symm g))⁻¹) : A) := by
    calc
      (↑((I.unit g)⁻¹) : A) * (b : A) =
          (↑((I.unit g)⁻¹) : A) *
              ((b : A) * (I.unit (ψ.symm g) : A)) *
            (↑((I.unit (ψ.symm g))⁻¹) : A) := by
        simp [mul_assoc]
      _ =
          (↑((I.unit g)⁻¹) : A) *
              ((I.unit g : A) * (b : A)) *
            (↑((I.unit (ψ.symm g))⁻¹) : A) := by
        rw [hb]
      _ =
          (b : A) *
            (↑((I.unit (ψ.symm g))⁻¹) : A) := by
        simp
  change
    ((I.unit (φ g) : A) * a *
        (↑((I.unit g)⁻¹) : A)) * (b : A) =
      (I.unit ((φ * ψ) (ψ.symm g)) : A) *
          (a * (b : A)) *
        (↑((I.unit (ψ.symm g))⁻¹) : A)
  rw [MulAut.mul_apply, ψ.apply_symm_apply]
  rw [mul_assoc
    ((I.unit (φ g) : A) * a)
    (↑((I.unit g)⁻¹) : A) (b : A), hinv]
  simp only [mul_assoc]

/-- Transport a restricted twisted invariant through right
multiplication.  The subgroup is carried through `ψ⁻¹`. -/
def rightMulTwistedRestrictedInvariant
    {φ ψ : MulAut P}
    (b : I.twistedFixedSubmodule (k := k) ψ)
    (Q : Subgroup P)
    (x :
      invariants
        ((I.twistedInteriorRepresentation (k := k) φ).comp
          Q.subtype)) :
    invariants
      ((I.twistedInteriorRepresentation (k := k) (φ * ψ)).comp
        (Q.map ψ.symm.toMonoidHom).subtype) :=
  transportInvariantAlong
    (I.twistedInteriorRepresentation (k := k) φ)
    (I.twistedInteriorRepresentation (k := k) (φ * ψ))
    ψ.symm
    (I.rightMulTwistedLinearMap (k := k) b)
    (I.rightMulTwistedLinearMap_compatible (k := k) b)
    Q x

omit [Fintype P] in
@[simp]
theorem coe_rightMulTwistedRestrictedInvariant
    {φ ψ : MulAut P}
    (b : I.twistedFixedSubmodule (k := k) ψ)
    (Q : Subgroup P)
    (x :
      invariants
        ((I.twistedInteriorRepresentation (k := k) φ).comp
          Q.subtype)) :
    (I.rightMulTwistedRestrictedInvariant
        (k := k) b Q x : A) =
      (x : A) * (b : A) :=
  rfl

/-- Right multiplication carries a twisted trace from `Q` to a
twisted trace from the image of `Q` under `ψ⁻¹`. -/
theorem twistedRelativeTrace_twistedFixedMul
    {φ ψ : MulAut P}
    (Q : Subgroup P)
    (x :
      invariants
        ((I.twistedInteriorRepresentation (k := k) φ).comp
          Q.subtype))
    (b : I.twistedFixedSubmodule (k := k) ψ) :
    I.twistedFixedMul (k := k)
        (I.twistedRelativeTrace (k := k) φ Q x) b =
      I.twistedRelativeTrace (k := k) (φ * ψ)
        (Q.map ψ.symm.toMonoidHom)
        (I.rightMulTwistedRestrictedInvariant
          (k := k) b Q x) := by
  apply Subtype.ext
  exact
    relativeTraceValue_intertwining
      (I.twistedInteriorRepresentation (k := k) φ)
      (I.twistedInteriorRepresentation (k := k) (φ * ψ))
      ψ.symm
      (I.rightMulTwistedLinearMap (k := k) b)
      (I.rightMulTwistedLinearMap_compatible (k := k) b)
      Q x

/-- Consequently, a proper trace multiplied on the right by a twisted
fixed element vanishes in the product Brauer component. -/
theorem twistedBrauerProjection_twistedRelativeTrace_twistedFixedMul
    {φ ψ : MulAut P}
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x :
      invariants
        ((I.twistedInteriorRepresentation (k := k) φ).comp
          Q.subtype))
    (b : I.twistedFixedSubmodule (k := k) ψ) :
    I.twistedBrauerProjection (k := k) (φ * ψ)
        (I.twistedFixedMul (k := k)
          (I.twistedRelativeTrace (k := k) φ Q x) b) =
      0 := by
  rw [I.twistedRelativeTrace_twistedFixedMul
    (k := k) Q x b]
  apply
    I.twistedBrauerProjection_twistedRelativeTrace
      (k := k) (φ * ψ)
      (Q.map ψ.symm.toMonoidHom)
  change ψ.symm.mapSubgroup Q < ⊤
  rw [← (ψ.symm.mapSubgroup).map_top]
  exact (ψ.symm.mapSubgroup).lt_iff_lt.mpr hQ

end InteriorAction
end Representation
