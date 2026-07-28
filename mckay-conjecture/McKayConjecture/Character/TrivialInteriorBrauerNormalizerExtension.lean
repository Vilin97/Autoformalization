/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeNormalizerExtension
import McKayConjecture.Character.InteriorNormalizerConjugation

/-!
# Brauer normalizer extensions for trivial interior actions

If the implementing homomorphism of an interior action is trivial, then
the prescribed action on the algebra is trivial as well.  Thus every
algebra unit is a fixed unit, and the Brauer projection itself extends
from fixed units to the entire interior normalizer.

This is the elementary base case of the Puig--Turull normalizer-extension
construction.  No Dade-algebra or primitivity hypothesis is needed.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

namespace InteriorAction

variable (I : InteriorAction (P := P) (A := A))

/-- A trivial implementing homomorphism forces the prescribed action on
the algebra to be trivial. -/
theorem smul_eq_self_of_unit_eq_one
    (hunit : I.unit = 1)
    (g : P) (a : A) :
    g • a = a := by
  have hg : I.unit g = 1 := by
    rw [hunit]
    rfl
  rw [I.smul_eq, hg]
  simp

/-- Regard every algebra element as fixed when the interior
implementing homomorphism is trivial. -/
def toFixedSubalgebraAlgHomOfUnitEqOne
    (hunit : I.unit = 1) :
    A →ₐ[k] fixedSubalgebra (k := k) (P := P) (A := A) where
  toFun a :=
    ⟨a, fun g ↦ I.smul_eq_self_of_unit_eq_one hunit g a⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_toFixedSubalgebraAlgHomOfUnitEqOne
    (hunit : I.unit = 1)
    (a : A) :
    (I.toFixedSubalgebraAlgHomOfUnitEqOne hunit a :
      fixedSubalgebra (k := k) (P := P) (A := A)) =
      a :=
  rfl

/-- Convert an interior-normalizer unit to a fixed-algebra unit when
the implementing homomorphism is trivial. -/
def unitNormalizerToFixedUnitOfUnitEqOne
    (hunit : I.unit = 1) :
    I.unitNormalizer →*
      (fixedSubalgebra (k := k) (P := P) (A := A))ˣ :=
  (Units.map
      (I.toFixedSubalgebraAlgHomOfUnitEqOne hunit).toMonoidHom).comp
    I.unitNormalizer.subtype

@[simp]
theorem coe_unitNormalizerToFixedUnitOfUnitEqOne
    (hunit : I.unit = 1)
    (s : I.unitNormalizer) :
    (((I.unitNormalizerToFixedUnitOfUnitEqOne hunit s :
          (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
        fixedSubalgebra (k := k) (P := P) (A := A)) : A) =
      ((s : Aˣ) : A) :=
  rfl

@[simp]
theorem unitNormalizerToFixedUnitOfUnitEqOne_fixedUnitToNormalizer
    (hunit : I.unit = 1)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    I.unitNormalizerToFixedUnitOfUnitEqOne hunit
        (I.fixedUnitToNormalizer (k := k) u) =
      u := by
  apply Units.ext
  apply Subtype.ext
  rfl

end InteriorAction

variable [Fintype P]

/-- The explicit Brauer normalizer extension for an interior action
with trivial implementing homomorphism. -/
def brauerNormalizerExtensionOfUnitEqOne
    (I : InteriorAction (P := P) (A := A))
    (hunit : I.unit = 1) :
    BrauerNormalizerExtension (k := k) I where
  hom :=
    (fixedUnitBrauerProjection
      (k := k) (P := P) (A := A)).comp
        (I.unitNormalizerToFixedUnitOfUnitEqOne hunit)
  extends_fixedUnit := by
    ext u
    simp
  conjugation_compatible := by
    intro s c
    let sFixed :
        (fixedSubalgebra (k := k) (P := P) (A := A))ˣ :=
      I.unitNormalizerToFixedUnitOfUnitEqOne hunit s
    refine
      ⟨I.normalizerConjFixedAlgEquiv (k := k) s c,
        rfl, ?_⟩
    change
      brauerAlgebraProjection (k := k) (P := P) (A := A)
            (↑(sFixed⁻¹) :
              fixedSubalgebra (k := k) (P := P) (A := A)) *
          brauerAlgebraProjection (k := k) (P := P) (A := A) c *
        brauerAlgebraProjection (k := k) (P := P) (A := A)
          (sFixed :
            fixedSubalgebra (k := k) (P := P) (A := A)) =
        brauerAlgebraProjection (k := k) (P := P) (A := A)
          (I.normalizerConjFixedAlgEquiv (k := k) s c)
    rw [← map_mul, ← map_mul]
    congr 1

/-- Proposition form of the explicit construction for a trivial
interior action. -/
theorem hasBrauerNormalizerExtension_of_unit_eq_one
    (I : InteriorAction (P := P) (A := A))
    (hunit : I.unit = 1) :
    HasBrauerNormalizerExtension (k := k) I :=
  ⟨brauerNormalizerExtensionOfUnitEqOne I hunit⟩

/-- For a subsingleton acting group, every interior action has an
explicit Brauer normalizer extension. -/
def brauerNormalizerExtensionOfSubsingleton
    [Subsingleton P]
    (I : InteriorAction (P := P) (A := A)) :
    BrauerNormalizerExtension (k := k) I :=
  brauerNormalizerExtensionOfUnitEqOne I (Subsingleton.elim I.unit 1)

/-- Proposition form of the subsingleton-group base case. -/
theorem hasBrauerNormalizerExtension_of_subsingleton
    [Subsingleton P]
    (I : InteriorAction (P := P) (A := A)) :
    HasBrauerNormalizerExtension (k := k) I :=
  ⟨brauerNormalizerExtensionOfSubsingleton I⟩

end Representation
