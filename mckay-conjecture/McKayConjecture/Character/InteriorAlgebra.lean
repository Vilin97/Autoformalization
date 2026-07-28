/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebra
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Interior actions and their unit normalizers

An interior action of `P` on an algebra `A` is implemented by a
homomorphism `P → Aˣ`.  Dade's normalizer-extension theorem concerns
the normalizer of the image of this homomorphism inside `Aˣ`.

This file defines that normalizer and proves that every unit of the
fixed algebra embeds into it.  The proof is the elementary observation
that a fixed unit centralizes every implementing unit.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- A group action on an algebra together with chosen units that
implement the action by conjugation. -/
structure InteriorAction where
  /-- Implementing unit for each group element. -/
  unit : P →* Aˣ
  /-- The prescribed action is conjugation by the implementing unit. -/
  smul_eq :
    ∀ (g : P) (a : A),
      g • a =
        (unit g : A) * a * (↑((unit g)⁻¹) : A)

namespace InteriorAction

variable (I : InteriorAction (P := P) (A := A))

/-- Image of the implementing homomorphism. -/
abbrev unitRange : Subgroup Aˣ :=
  I.unit.range

/-- Normalizer of the implementing units in the full unit group of
the algebra. -/
abbrev unitNormalizer : Subgroup Aˣ :=
  Subgroup.normalizer (I.unitRange : Set Aˣ)

/-- Forget that a unit belongs to the fixed subalgebra. -/
def fixedUnitToAmbient :
    (fixedSubalgebra (k := k) (P := P) (A := A))ˣ →*
      Aˣ :=
  Units.map
    (fixedSubalgebra
      (k := k) (P := P) (A := A)).val.toRingHom.toMonoidHom

@[simp]
theorem coe_fixedUnitToAmbient
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    (fixedUnitToAmbient (k := k) (P := P) (A := A) u : A) =
      (u : A) :=
  rfl

/-- A fixed unit commutes with every implementing unit. -/
theorem fixedUnitToAmbient_mul_unit
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ)
    (g : P) :
    fixedUnitToAmbient (k := k) (P := P) (A := A) u *
        I.unit g =
      I.unit g *
        fixedUnitToAmbient (k := k) (P := P) (A := A) u := by
  apply Units.ext
  change
    (u : A) * (I.unit g : A) =
      (I.unit g : A) * (u : A)
  have hfixed :
      g • (u : A) = (u : A) :=
    u.val.property g
  rw [I.smul_eq] at hfixed
  calc
    (u : A) * (I.unit g : A) =
        ((I.unit g : A) * (u : A) *
          (↑((I.unit g)⁻¹) : A)) *
            (I.unit g : A) := by
              rw [hfixed]
    _ = (I.unit g : A) * (u : A) := by
          rw [mul_assoc, Units.inv_mul, mul_one]

/-- The ambient image of a fixed unit lies in the centralizer of the
interior image. -/
theorem fixedUnitToAmbient_mem_centralizer
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    fixedUnitToAmbient (k := k) (P := P) (A := A) u ∈
      Subgroup.centralizer (I.unitRange : Set Aˣ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rcases ht with ⟨g, rfl⟩
  exact (I.fixedUnitToAmbient_mul_unit u g).symm

/-- Every fixed unit normalizes the interior image. -/
theorem fixedUnitToAmbient_mem_unitNormalizer
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    fixedUnitToAmbient (k := k) (P := P) (A := A) u ∈
      I.unitNormalizer :=
  Subgroup.centralizer_le_normalizer
    (I.unitRange : Set Aˣ)
    (I.fixedUnitToAmbient_mem_centralizer u)

/-- Embedding of fixed-algebra units into the unit normalizer. -/
def fixedUnitToNormalizer :
    (fixedSubalgebra (k := k) (P := P) (A := A))ˣ →*
      I.unitNormalizer :=
  (fixedUnitToAmbient
      (k := k) (P := P) (A := A)).codRestrict
    I.unitNormalizer
    I.fixedUnitToAmbient_mem_unitNormalizer

@[simp]
theorem coe_fixedUnitToNormalizer
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    ((I.fixedUnitToNormalizer u : I.unitNormalizer) : Aˣ) =
      fixedUnitToAmbient (k := k) (P := P) (A := A) u :=
  rfl

end InteriorAction
end Representation
