/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeNormalizerExtension
import McKayConjecture.Character.GradedMonoidFamilyUnitAssembly
import McKayConjecture.Character.InteriorNormalizerFixedUnitQuotient
import McKayConjecture.Character.TwistedInteriorBrauerNormalizerUnits

/-!
# Collapsing the automorphism-graded Brauer family

The twisted Brauer components form a family graded by `Aut(P)`.  This
file states a concrete, stronger-than-elementwise splitting datum: a
linear map from every automorphism component to the ordinary Brauer
quotient, normalized on the identity component and compatible with all
homogeneous products.

Such a collapse cannot encode a desired normalizer homomorphism by
choosing its values separately for normalizer elements: it is indexed
only by the induced automorphism and is multiplicative on every pair
of elements in every pair of components.  Pulling it back along the
faithful normalizer action and applying the generic graded-family
assembly theorem produces a homomorphism

`N_{Aˣ}(P) → A(P)ˣ`.

Identity normalization then forces this homomorphism to extend the
ordinary Brauer projection on fixed-algebra units.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable (I : InteriorAction (P := P) (A := A))

/-- A normalized multiplicative collapse of all automorphism-graded
twisted Brauer components into the ordinary algebra Brauer quotient.

Requiring linear maps on whole components and compatibility with every
homogeneous product is strictly stronger than specifying values only
on normalizer representatives. -/
structure TwistedBrauerGradedCollapse where
  /-- The linear collapse in automorphism degree `φ`. -/
  map :
    ∀ φ : MulAut P,
      I.TwistedBrauerComponent (k := k) φ →ₗ[k]
        BrauerQuotientAlgebra (k := k) (P := P) (A := A)
  /-- In degree one, the collapse is the canonical identification
  with the ordinary Brauer quotient. -/
  map_identity :
    map 1 =
      (I.twistedBrauerIdentityEquiv (k := k)).toLinearMap
  /-- Collapse commutes with every homogeneous product. -/
  map_mul :
    ∀ (φ ψ : MulAut P)
      (x : I.TwistedBrauerComponent (k := k) φ)
      (y : I.TwistedBrauerComponent (k := k) ψ),
      map (φ * ψ)
          (I.twistedBrauerMul (k := k) φ ψ x y) =
        map φ x * map ψ y

namespace TwistedBrauerGradedCollapse

variable {I : InteriorAction (P := P) (A := A)}

/-- Identity normalization sends the distinguished twisted identity
to the ordinary quotient identity. -/
@[simp]
theorem map_twistedBrauerOne
    (C : I.TwistedBrauerGradedCollapse (k := k)) :
    C.map 1 (I.twistedBrauerOne (k := k)) = 1 := by
  rw [C.map_identity]
  exact I.twistedBrauerIdentityEquiv_one (k := k)

/-- A dependent collapse map commutes with canonical transport between
equal automorphism degrees. -/
@[simp]
theorem map_twistedBrauerComponentEquivOfEq
    (C : I.TwistedBrauerGradedCollapse (k := k))
    {φ ψ : MulAut P}
    (h : φ = ψ)
    (x : I.TwistedBrauerComponent (k := k) φ) :
    C.map ψ
        (I.twistedBrauerComponentEquivOfEq (k := k) h x) =
      C.map φ x := by
  subst ψ
  rfl

/-- The normalizer-pullback twisted Brauer family as a generic graded
monoid family. -/
def unitNormalizerGradedFamily
    (hI : Function.Injective I.unit) :
    GradedMonoidFamily.Data I.unitNormalizer where
  carrier :=
    I.UnitNormalizerTwistedBrauerFiber (k := k) hI
  one :=
    I.unitNormalizerTwistedBrauerOne (k := k) hI
  mul :=
    I.unitNormalizerTwistedBrauerMul (k := k) hI

/-- Normalizer representatives form a multiplicative section of the
normalizer-pullback graded family. -/
def unitNormalizerGradedSection
    (hI : Function.Injective I.unit) :
    GradedMonoidFamily.Section
      (unitNormalizerGradedFamily (k := k) hI) where
  val :=
    I.unitNormalizerTwistedBrauerClass (k := k) hI
  val_one := rfl
  val_mul := by
    intro s t
    exact
      I.unitNormalizerTwistedBrauerMul_class
        (k := k) hI s t

/-- A collapse indexed by automorphisms pulls back to a collapse of
the normalizer-graded family. -/
def unitNormalizerGradedFamilyCollapse
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (hI : Function.Injective I.unit) :
    GradedMonoidFamily.Collapse
      (unitNormalizerGradedFamily (k := k) hI)
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) where
  toFun := fun s ↦ C.map (I.normalizerMulAut hI s)
  map_one := by
    change
      C.map (I.normalizerMulAut hI 1)
          (I.unitNormalizerTwistedBrauerOne (k := k) hI) =
        1
    calc
      _ = C.map 1
          (I.twistedBrauerComponentEquivOfEq (k := k)
            (I.normalizerMulAut_one hI)
            (I.unitNormalizerTwistedBrauerOne (k := k) hI)) := by
              symm
              exact
                C.map_twistedBrauerComponentEquivOfEq
                  (I.normalizerMulAut_one hI) _
      _ = C.map 1 (I.twistedBrauerOne (k := k)) := by
            rw [
              I.unitNormalizerTwistedBrauerOne_eq_twistedBrauerOne
                hI]
      _ = 1 := C.map_twistedBrauerOne
  map_mul := by
    intro s t x y
    change
      C.map (I.normalizerMulAut hI (s * t))
          (I.unitNormalizerTwistedBrauerMul
            (k := k) hI s t x y) =
        C.map (I.normalizerMulAut hI s) x *
          C.map (I.normalizerMulAut hI t) y
    simp only [InteriorAction.unitNormalizerTwistedBrauerMul]
    rw [C.map_twistedBrauerComponentEquivOfEq]
    exact
      C.map_mul
        (I.normalizerMulAut hI s)
        (I.normalizerMulAut hI t) x y

/-- The unit-valued normalizer homomorphism assembled from a normalized
graded collapse. -/
def unitNormalizerUnitsHom
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (hI : Function.Injective I.unit) :
    I.unitNormalizer →*
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ :=
  (C.unitNormalizerGradedFamilyCollapse hI).sectionUnitsHom
    (unitNormalizerGradedSection (k := k) hI)

/-- The underlying value of the assembled normalizer unit is the
collapse of its homogeneous Brauer class. -/
@[simp]
theorem coe_unitNormalizerUnitsHom
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    (C.unitNormalizerUnitsHom hI s :
        BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      C.map (I.normalizerMulAut hI s)
        (I.unitNormalizerTwistedBrauerClass (k := k) hI s) :=
  rfl

omit [Fintype P] in
/-- A fixed-algebra unit induces the identity automorphism of `P`.
This makes precise why identity-degree normalization controls the
restriction of the assembled homomorphism. -/
@[simp]
theorem normalizerMulAut_fixedUnitToNormalizer
    (hI : Function.Injective I.unit)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    I.normalizerMulAut hI
        (I.fixedUnitToNormalizer (k := k) u) =
      1 := by
  change
    I.fixedUnitToNormalizer (k := k) u ∈
      (I.faithfulNormalizerAction hI).ker
  rw [I.mem_faithfulNormalizerAction_ker_iff hI]
  intro g
  exact I.fixedUnitToAmbient_mul_unit (k := k) u g

/-- After transport to degree one, the homogeneous class of a fixed
unit is exactly its ordinary algebra Brauer class. -/
theorem twistedBrauerIdentityEquiv_fixedUnitClass
    (hI : Function.Injective I.unit)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    I.twistedBrauerIdentityEquiv (k := k)
        (I.twistedBrauerComponentEquivOfEq (k := k)
          (normalizerMulAut_fixedUnitToNormalizer
            (k := k) hI u)
          (I.unitNormalizerTwistedBrauerClass (k := k) hI
            (I.fixedUnitToNormalizer (k := k) u))) =
      brauerAlgebraProjection (k := k) (P := P) (A := A) u := by
  rw [unitNormalizerTwistedBrauerClass]
  rw [I.twistedBrauerComponentEquivOfEq_projection]
  rw [I.twistedBrauerIdentityEquiv_projection]
  apply congrArg
    (brauerAlgebraProjection (k := k) (P := P) (A := A))
  apply Subtype.ext
  simp

/-- A normalized graded collapse sends the homogeneous class of every
fixed unit to its ordinary Brauer class. -/
theorem map_fixedUnitClass
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (hI : Function.Injective I.unit)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    C.map
        (I.normalizerMulAut hI
          (I.fixedUnitToNormalizer (k := k) u))
        (I.unitNormalizerTwistedBrauerClass (k := k) hI
          (I.fixedUnitToNormalizer (k := k) u)) =
      brauerAlgebraProjection (k := k) (P := P) (A := A) u := by
  let h :=
    normalizerMulAut_fixedUnitToNormalizer
      (I := I) (k := k) hI u
  calc
    _ = C.map 1
        (I.twistedBrauerComponentEquivOfEq (k := k) h
          (I.unitNormalizerTwistedBrauerClass (k := k) hI
            (I.fixedUnitToNormalizer (k := k) u))) := by
            symm
            exact C.map_twistedBrauerComponentEquivOfEq h _
    _ = I.twistedBrauerIdentityEquiv (k := k)
        (I.twistedBrauerComponentEquivOfEq (k := k) h
          (I.unitNormalizerTwistedBrauerClass (k := k) hI
            (I.fixedUnitToNormalizer (k := k) u))) := by
            rw [C.map_identity]
            rfl
    _ = brauerAlgebraProjection
          (k := k) (P := P) (A := A) u :=
      twistedBrauerIdentityEquiv_fixedUnitClass
        (I := I) (k := k) hI u

/-- On fixed units, the assembled normalizer homomorphism agrees as
an element of the ordinary Brauer quotient with the Brauer
projection. -/
@[simp]
theorem coe_unitNormalizerUnitsHom_fixedUnit
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (hI : Function.Injective I.unit)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    (C.unitNormalizerUnitsHom hI
        (I.fixedUnitToNormalizer (k := k) u) :
      BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      brauerAlgebraProjection (k := k) (P := P) (A := A) u :=
  C.map_fixedUnitClass hI u

/-- Unit-valued form of the fixed-unit comparison. -/
@[simp]
theorem unitNormalizerUnitsHom_fixedUnit
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (hI : Function.Injective I.unit)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    C.unitNormalizerUnitsHom hI
        (I.fixedUnitToNormalizer (k := k) u) =
      fixedUnitBrauerProjection (k := k) (P := P) (A := A) u := by
  apply Units.ext
  exact C.coe_unitNormalizerUnitsHom_fixedUnit hI u

/-- The assembled homomorphism extends the fixed-unit Brauer
homomorphism. -/
theorem unitNormalizerUnitsHom_comp_fixedUnitToNormalizer
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (hI : Function.Injective I.unit) :
    (C.unitNormalizerUnitsHom hI).comp
        (I.fixedUnitToNormalizer (k := k)) =
      fixedUnitBrauerProjection (k := k) (P := P) (A := A) := by
  apply MonoidHom.ext
  intro u
  exact C.unitNormalizerUnitsHom_fixedUnit hI u

end TwistedBrauerGradedCollapse
end InteriorAction
end Representation
