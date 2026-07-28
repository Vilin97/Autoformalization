/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerScalarUnits

/-!
# Correcting a projective normalizer lift

Assume the Brauer quotient has been identified with the scalar field
and the Brauer map extends to the interior normalizer.  Applying that
extension to a projective normalizer lift turns its factor set into an
explicit scalar coboundary.  Rescaling by the inverse scalar therefore
produces an honest group homomorphism.

This is the cocycle-cancellation calculation at the heart of the magic
representation construction.
-/

noncomputable section

namespace Representation

variable {k P A H : Type}
variable [Field k] [Group P] [Fintype P] [Group H]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- A normalized projective lift into the unit normalizer. -/
structure ProjectiveNormalizerLift
    (I : InteriorAction (P := P) (A := A)) where
  /-- Chosen normalizer unit for every group element. -/
  operator : H → I.unitNormalizer
  /-- Scalar factor set of the chosen operators. -/
  factor : H → H → kˣ
  /-- Normalization at the identity. -/
  operator_one : operator 1 = 1
  /-- Projective multiplication law. -/
  operator_mul :
    ∀ g h,
      operator g * operator h =
        I.scalarUnitNormalizer (k := k) (factor g h) *
          operator (g * h)

namespace InteriorAction

variable (I : InteriorAction (P := P) (A := A))

omit [Fintype P] in
/-- Scalar units commute with all elements of the interior
normalizer. -/
theorem scalarUnitNormalizer_commute
    (z : kˣ) (n : I.unitNormalizer) :
    I.scalarUnitNormalizer (k := k) z * n =
      n * I.scalarUnitNormalizer (k := k) z := by
  apply Subtype.ext
  apply Units.ext
  change
    algebraMap k A (z : k) * ((n : Aˣ) : A) =
      ((n : Aˣ) : A) * algebraMap k A (z : k)
  exact Algebra.commutes (z : k) ((n : Aˣ) : A)

end InteriorAction

namespace ProjectiveNormalizerLift

variable
  {I : InteriorAction (P := P) (A := A)}
  (T : ProjectiveNormalizerLift (k := k) (H := H) I)
  (E : BrauerNormalizerExtension (k := k) I)
  (Z : BrauerScalarIdentification (k := k) (P := P) (A := A))

/-- Scalar obtained by applying the normalizer extension and pulling
the result back through `A(P)ˣ ≃ kˣ`. -/
def brauerScalar (g : H) : kˣ :=
  Z.equiv.symm (E.hom (T.operator g))

@[simp]
theorem equiv_brauerScalar
    (g : H) :
    Z.equiv (T.brauerScalar E Z g) =
      E.hom (T.operator g) :=
  Z.equiv.apply_symm_apply _

/-- Applying the extension to projective multiplication expresses the
factor set as the coboundary of `brauerScalar`. -/
theorem brauerScalar_mul
    (g h : H) :
    T.brauerScalar E Z g * T.brauerScalar E Z h =
      T.factor g h * T.brauerScalar E Z (g * h) := by
  apply Z.equiv.injective
  rw [map_mul, map_mul, T.equiv_brauerScalar,
    T.equiv_brauerScalar, T.equiv_brauerScalar]
  rw [← E.hom.map_mul, T.operator_mul, E.hom.map_mul,
    E.hom_scalarUnitNormalizer]
  exact
    congrArg
      (fun f ↦ f (T.factor g h))
      Z.equiv_toMonoidHom.symm ▸ rfl

/-- Corrected operator obtained by dividing by the Brauer scalar. -/
def correctedOperator (g : H) : I.unitNormalizer :=
  I.scalarUnitNormalizer (k := k) (T.brauerScalar E Z g)⁻¹ *
    T.operator g

/-- The corrected operators multiply honestly. -/
theorem correctedOperator_mul
    (g h : H) :
    T.correctedOperator E Z (g * h) =
      T.correctedOperator E Z g *
        T.correctedOperator E Z h := by
  let sg := T.brauerScalar E Z g
  let sh := T.brauerScalar E Z h
  let sgh := T.brauerScalar E Z (g * h)
  let α := T.factor g h
  have hs : sg * sh = α * sgh :=
    T.brauerScalar_mul E Z g h
  have hscalar :
      sg⁻¹ * sh⁻¹ * α = sgh⁻¹ := by
    calc
      sg⁻¹ * sh⁻¹ * α = (sh * sg)⁻¹ * α := by
        simp only [mul_inv_rev]
      _ = (sg * sh)⁻¹ * α := by
        rw [mul_comm sh sg]
      _ = (α * sgh)⁻¹ * α := by
        rw [hs]
      _ = sgh⁻¹ * α⁻¹ * α := by
        rw [mul_inv_rev]
      _ = sgh⁻¹ := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
  have hop :
      T.operator g * T.operator h =
        I.scalarUnitNormalizer (k := k) α *
          T.operator (g * h) := by
    simpa only [α] using T.operator_mul g h
  change
    I.scalarUnitNormalizer (k := k) sgh⁻¹ *
        T.operator (g * h) =
      (I.scalarUnitNormalizer (k := k) sg⁻¹ *
          T.operator g) *
        (I.scalarUnitNormalizer (k := k) sh⁻¹ *
          T.operator h)
  calc
    I.scalarUnitNormalizer (k := k) sgh⁻¹ *
        T.operator (g * h) =
      I.scalarUnitNormalizer (k := k)
          (sg⁻¹ * sh⁻¹ * α) *
        T.operator (g * h) := by
          rw [hscalar]
    _ =
      (I.scalarUnitNormalizer (k := k) sg⁻¹ *
        I.scalarUnitNormalizer (k := k) sh⁻¹ *
        I.scalarUnitNormalizer (k := k) α) *
          T.operator (g * h) := by
            rw [map_mul, map_mul]
    _ =
      (I.scalarUnitNormalizer (k := k) sg⁻¹ *
        I.scalarUnitNormalizer (k := k) sh⁻¹) *
          (T.operator g * T.operator h) := by
            rw [hop]
            simp only [mul_assoc]
    _ =
      I.scalarUnitNormalizer (k := k) sg⁻¹ *
        (I.scalarUnitNormalizer (k := k) sh⁻¹ *
          T.operator g) *
        T.operator h := by
          simp only [mul_assoc]
    _ =
      I.scalarUnitNormalizer (k := k) sg⁻¹ *
        (T.operator g *
          I.scalarUnitNormalizer (k := k) sh⁻¹) *
        T.operator h := by
          rw [I.scalarUnitNormalizer_commute sh⁻¹ (T.operator g)]
    _ =
      (I.scalarUnitNormalizer (k := k) sg⁻¹ *
          T.operator g) *
        (I.scalarUnitNormalizer (k := k) sh⁻¹ *
          T.operator h) := by
            simp only [mul_assoc]

/-- The corrected operators form an honest group homomorphism. -/
def correctedHom : H →* I.unitNormalizer where
  toFun := T.correctedOperator E Z
  map_one' := by
    change
      I.scalarUnitNormalizer (k := k)
          (Z.equiv.symm (E.hom (T.operator 1)))⁻¹ *
        T.operator 1 =
      1
    rw [T.operator_one, E.hom.map_one, map_one, inv_one,
      map_one, one_mul]
  map_mul' g h :=
    T.correctedOperator_mul E Z g h

end ProjectiveNormalizerLift
end Representation
