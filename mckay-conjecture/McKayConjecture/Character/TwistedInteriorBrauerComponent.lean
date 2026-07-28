/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotient
import McKayConjecture.Character.TwistedInteriorRepresentation

/-!
# Twisted Brauer components of an interior action

The `φ`-component of the extended Brauer construction is the ordinary
Brauer quotient of the `φ`-twisted interior representation.  This file
packages that reuse and exposes relative traces and the quotient
projection directly on the twisted fixed submodule.

The multiplication between different components is deliberately left
for a separate file: proving that it descends requires the
componentwise trace-product calculation.
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

noncomputable local instance twistedInteriorLeftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- Identity-on-elements equivalence from invariants of the twisted
representation to the corresponding twisted fixed submodule. -/
def twistedInvariantsEquiv
    (φ : MulAut P) :
    invariants
        (I.twistedInteriorRepresentation (k := k) φ) ≃ₗ[k]
      I.twistedFixedSubmodule (k := k) φ :=
  LinearEquiv.ofEq _ _
    (I.invariants_twistedInteriorRepresentation (k := k) φ)

omit [Fintype P] in
@[simp]
theorem coe_twistedInvariantsEquiv
    (φ : MulAut P)
    (a :
      invariants
        (I.twistedInteriorRepresentation (k := k) φ)) :
    ((I.twistedInvariantsEquiv (k := k) φ a :
        I.twistedFixedSubmodule (k := k) φ) : A) =
      a :=
  rfl

omit [Fintype P] in
@[simp]
theorem coe_twistedInvariantsEquiv_symm
    (φ : MulAut P)
    (a : I.twistedFixedSubmodule (k := k) φ) :
    (((I.twistedInvariantsEquiv (k := k) φ).symm a :
        invariants
          (I.twistedInteriorRepresentation (k := k) φ)) : A) =
      a :=
  rfl

/-- Relative trace into a twisted fixed submodule. -/
def twistedRelativeTrace
    (φ : MulAut P)
    (Q : Subgroup P) :
    invariants
        ((I.twistedInteriorRepresentation (k := k) φ).comp
          Q.subtype) →ₗ[k]
      I.twistedFixedSubmodule (k := k) φ :=
  (I.twistedInvariantsEquiv (k := k) φ).toLinearMap.comp
    (relativeTrace
      (I.twistedInteriorRepresentation (k := k) φ) Q)

@[simp]
theorem twistedRelativeTrace_apply_coe
    (φ : MulAut P)
    (Q : Subgroup P)
    (a :
      invariants
        ((I.twistedInteriorRepresentation (k := k) φ).comp
          Q.subtype)) :
    ((I.twistedRelativeTrace (k := k) φ Q a :
        I.twistedFixedSubmodule (k := k) φ) : A) =
      ∑ c : P ⧸ Q,
        (I.unit (φ c.out) : A) * (a : A) *
          (↑((I.unit c.out)⁻¹) : A) :=
  rfl

/-- The `φ`-twisted Brauer component, defined using the existing
Brauer quotient of a linear representation. -/
abbrev TwistedBrauerComponent
    (φ : MulAut P) :=
  BrauerQuotient
    (I.twistedInteriorRepresentation (k := k) φ)

/-- Projection from twisted fixed elements to the corresponding
twisted Brauer component. -/
def twistedBrauerProjection
    (φ : MulAut P) :
    I.twistedFixedSubmodule (k := k) φ →ₗ[k]
      I.TwistedBrauerComponent (k := k) φ :=
  (brauerProjection
      (I.twistedInteriorRepresentation (k := k) φ)).comp
    (I.twistedInvariantsEquiv (k := k) φ).symm.toLinearMap

@[simp]
theorem twistedBrauerProjection_twistedRelativeTrace
    (φ : MulAut P)
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (a :
      invariants
        ((I.twistedInteriorRepresentation (k := k) φ).comp
          Q.subtype)) :
    I.twistedBrauerProjection (k := k) φ
        (I.twistedRelativeTrace (k := k) φ Q a) =
      0 := by
  change
    brauerProjection
        (I.twistedInteriorRepresentation (k := k) φ)
        (relativeTrace
          (I.twistedInteriorRepresentation (k := k) φ) Q a) =
      0
  exact
    brauerProjection_relativeTrace
      (I.twistedInteriorRepresentation (k := k) φ)
      Q hQ a

/-- The class of a normalizing unit in the component indexed by its
induced automorphism. -/
def unitNormalizerTwistedBrauerClass
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    I.TwistedBrauerComponent (k := k)
      (I.normalizerMulAut hI s) :=
  I.twistedBrauerProjection (k := k)
    (I.normalizerMulAut hI s)
    ⟨((s : Aˣ) : A),
      I.coe_unitNormalizer_mem_twistedFixedSubmodule
        (k := k) hI s⟩

section AlgebraAction

variable [SMulCommClass P k A]

omit [Fintype P] in
/-- At the identity automorphism, the twisted interior representation
is the prescribed algebra action. -/
theorem twistedInteriorRepresentation_one :
    I.twistedInteriorRepresentation (k := k) 1 =
      algebraActionRepresentation (k := k) (P := P) (A := A) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro a
  change
    (I.unit g : A) * a *
        (↑((I.unit g)⁻¹) : A) =
      g • a
  exact (I.smul_eq g a).symm

end AlgebraAction

end InteriorAction
end Representation
