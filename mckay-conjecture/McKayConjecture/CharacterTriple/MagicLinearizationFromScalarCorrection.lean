/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.MagicLinearization

/-!
# Magic linearization from a scalar correction

A normalized projective representation becomes honest as soon as its
factor is written as the coboundary of an explicit scalar function.
This file performs the correction directly on the chosen linear
operators.

Keeping this coefficient-independent construction separate is useful
for modular-to-characteristic-zero arguments: a normalizer theorem may
produce the scalar function over one field, after which a homomorphism
of unit groups transports it to the field of the projective action.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K G V : Type}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]

/-- Correct one chosen projective operator by the inverse of its
splitting scalar. -/
def scalarCorrectedOperator
    (Q : ProjectiveRepresentation K G V)
    (b : G → Kˣ)
    (g : G) :
    V ≃ₗ[K] V :=
  scalarLinearEquiv K V (b g)⁻¹ * Q.operator g

/-- The scalar-corrected operators multiply honestly when `b` splits
the projective factor. -/
theorem scalarCorrectedOperator_mul
    (Q : ProjectiveRepresentation K G V)
    (b : G → Kˣ)
    (b_mul :
      ∀ g h,
        b g * b h =
          Q.factor g h * b (g * h))
    (g h : G) :
    scalarCorrectedOperator Q b (g * h) =
      scalarCorrectedOperator Q b g *
        scalarCorrectedOperator Q b h := by
  let bg := b g
  let bh := b h
  let bgh := b (g * h)
  let α := Q.factor g h
  have hb : bg * bh = α * bgh :=
    b_mul g h
  have hscalar :
      bg⁻¹ * bh⁻¹ * α = bgh⁻¹ := by
    calc
      bg⁻¹ * bh⁻¹ * α = (bh * bg)⁻¹ * α := by
        simp only [mul_inv_rev]
      _ = (bg * bh)⁻¹ * α := by
        rw [mul_comm bh bg]
      _ = (α * bgh)⁻¹ * α := by
        rw [hb]
      _ = bgh⁻¹ * α⁻¹ * α := by
        rw [mul_inv_rev]
      _ = bgh⁻¹ := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
  have hop :
      Q.operator g * Q.operator h =
        scalarLinearEquiv K V α *
          Q.operator (g * h) := by
    simpa only [α] using Q.map_mul g h
  change
    scalarLinearEquiv K V bgh⁻¹ *
        Q.operator (g * h) =
      (scalarLinearEquiv K V bg⁻¹ * Q.operator g) *
        (scalarLinearEquiv K V bh⁻¹ * Q.operator h)
  calc
    scalarLinearEquiv K V bgh⁻¹ *
        Q.operator (g * h) =
      scalarLinearEquiv K V (bg⁻¹ * bh⁻¹ * α) *
        Q.operator (g * h) := by
          rw [hscalar]
    _ =
      (scalarLinearEquiv K V bg⁻¹ *
        scalarLinearEquiv K V bh⁻¹ *
        scalarLinearEquiv K V α) *
          Q.operator (g * h) := by
            rw [scalarLinearEquiv_mul,
              scalarLinearEquiv_mul]
    _ =
      (scalarLinearEquiv K V bg⁻¹ *
        scalarLinearEquiv K V bh⁻¹) *
          (Q.operator g * Q.operator h) := by
            rw [hop]
            simp only [mul_assoc]
    _ =
      scalarLinearEquiv K V bg⁻¹ *
        (scalarLinearEquiv K V bh⁻¹ *
          Q.operator g) *
        Q.operator h := by
          simp only [mul_assoc]
    _ =
      scalarLinearEquiv K V bg⁻¹ *
        (Q.operator g *
          scalarLinearEquiv K V bh⁻¹) *
        Q.operator h := by
          rw [scalarLinearEquiv_comm K V bh⁻¹
            (Q.operator g)]
    _ =
      (scalarLinearEquiv K V bg⁻¹ * Q.operator g) *
        (scalarLinearEquiv K V bh⁻¹ * Q.operator h) := by
          simp only [mul_assoc]

/-- The scalar-corrected operators form an honest linear action. -/
def scalarCorrectedLinearAction
    (Q : ProjectiveRepresentation K G V)
    (hQ : Q.IsNormalized)
    (b : G → Kˣ)
    (b_one : b 1 = 1)
    (b_mul :
      ∀ g h,
        b g * b h =
          Q.factor g h * b (g * h)) :
    G →* (V ≃ₗ[K] V) where
  toFun := scalarCorrectedOperator Q b
  map_one' := by
    change
      scalarLinearEquiv K V (b 1)⁻¹ *
          Q.operator 1 =
        1
    rw [b_one, hQ]
    simp
  map_mul' :=
    scalarCorrectedOperator_mul Q b b_mul

/-- An explicit scalar splitting of the factor of a normalized
projective representation supplies a magic linearization. -/
def magicLinearizationOfScalarCorrection
    (Q : ProjectiveRepresentation K G V)
    (hQ : Q.IsNormalized)
    (b : G → Kˣ)
    (b_one : b 1 = 1)
    (b_mul :
      ∀ g h,
        b g * b h =
          Q.factor g h * b (g * h)) :
    MagicLinearization Q where
  action :=
    scalarCorrectedLinearAction Q hQ b b_one b_mul
  scalar := b
  operator_eq := by
    intro g v
    change
      Q.operator g v =
        (b g : K) •
          (scalarLinearEquiv K V (b g)⁻¹ *
            Q.operator g) v
    simp only [LinearEquiv.mul_apply,
      scalarLinearEquiv_apply, Units.val_inv_eq_inv_val,
      smul_smul]
    simp

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
