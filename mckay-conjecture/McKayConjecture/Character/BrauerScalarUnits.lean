/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeNormalizerExtension

/-!
# Scalar units in an interior Brauer quotient

The Glauberman application has a one-dimensional Brauer quotient:
`A(P) ≃ k`.  At the level needed for cocycle cancellation, this is an
identification of scalar units `kˣ` with `A(P)ˣ`.

This file defines the scalar-unit maps through the fixed algebra,
interior normalizer, and Brauer quotient, then packages the exact
identification used to pull a normalizer-extension value back to a
scalar.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [Field k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- Scalar units as units of the fixed subalgebra. -/
def scalarFixedUnit :
    kˣ →*
      (fixedSubalgebra (k := k) (P := P) (A := A))ˣ :=
  Units.map
    (algebraMap k
      (fixedSubalgebra (k := k) (P := P) (A := A))).toMonoidHom

omit [Fintype P] in
@[simp]
theorem coe_scalarFixedUnit
    (z : kˣ) :
    (scalarFixedUnit (k := k) (P := P) (A := A) z :
      fixedSubalgebra (k := k) (P := P) (A := A)) =
    algebraMap k
      (fixedSubalgebra (k := k) (P := P) (A := A)) z :=
  rfl

/-- Scalar units embedded in the interior normalizer. -/
def InteriorAction.scalarUnitNormalizer
    (I : InteriorAction (P := P) (A := A)) :
    kˣ →* I.unitNormalizer :=
  (I.fixedUnitToNormalizer (k := k)).comp
    (scalarFixedUnit (k := k) (P := P) (A := A))

/-- Scalar units projected to the Brauer quotient. -/
def scalarBrauerUnit :
    kˣ →*
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ :=
  (fixedUnitBrauerProjection (k := k) (P := P) (A := A)).comp
    (scalarFixedUnit (k := k) (P := P) (A := A))

/-- A specified identification of the Brauer-quotient units with
scalar units, agreeing with the canonical scalar map. -/
structure BrauerScalarIdentification where
  /-- Unit-group identification. -/
  equiv :
    kˣ ≃*
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ
  /-- The forward map is the canonical scalar map. -/
  equiv_toMonoidHom :
    equiv.toMonoidHom =
      scalarBrauerUnit (k := k) (P := P) (A := A)

namespace BrauerScalarIdentification

variable
  (Z : BrauerScalarIdentification (k := k) (P := P) (A := A))

/-- Construct the scalar-unit identification from a ring equivalence
`A(P) ≃ k` that sends every canonical scalar unit to itself. -/
def ofRingEquiv
    (e :
      BrauerQuotientAlgebra (k := k) (P := P) (A := A) ≃+* k)
    (hscalar :
      ∀ z : kˣ,
        Units.mapEquiv e.toMulEquiv
            (scalarBrauerUnit (k := k) (P := P) (A := A) z) =
          z) :
    BrauerScalarIdentification (k := k) (P := P) (A := A) where
  equiv := (Units.mapEquiv e.toMulEquiv).symm
  equiv_toMonoidHom := by
    apply MonoidHom.ext
    intro z
    apply (Units.mapEquiv e.toMulEquiv).injective
    change
      Units.mapEquiv e.toMulEquiv
          ((Units.mapEquiv e.toMulEquiv).symm z) =
        Units.mapEquiv e.toMulEquiv
          (scalarBrauerUnit (k := k) (P := P) (A := A) z)
    rw [MulEquiv.apply_symm_apply, hscalar]

@[simp]
theorem equiv_apply
    (z : kˣ) :
    Z.equiv z =
      scalarBrauerUnit (k := k) (P := P) (A := A) z :=
  congrArg (fun f ↦ f z) Z.equiv_toMonoidHom

@[simp]
theorem symm_scalarBrauerUnit
    (z : kˣ) :
    Z.equiv.symm
        (scalarBrauerUnit (k := k) (P := P) (A := A) z) =
      z := by
  rw [← Z.equiv_apply, Z.equiv.symm_apply_apply]

end BrauerScalarIdentification

namespace BrauerNormalizerExtension

variable
  {I : InteriorAction (P := P) (A := A)}
  (E : BrauerNormalizerExtension (k := k) I)

@[simp]
theorem hom_scalarUnitNormalizer
    (z : kˣ) :
    E.hom (I.scalarUnitNormalizer (k := k) z) =
      scalarBrauerUnit (k := k) (P := P) (A := A) z := by
  exact E.hom_fixedUnitToNormalizer
    (scalarFixedUnit (k := k) (P := P) (A := A) z)

end BrauerNormalizerExtension
end Representation
