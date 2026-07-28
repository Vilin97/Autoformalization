/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PPrimeDeterminantRoot

/-!
# Determinant normalization of a finite-order intertwiner

If an invertible endomorphism `P` has order dividing `n` and the
dimension of its space is coprime to `n`, there is a central scalar
multiple of `P` which still has `n`-th power one and has determinant
one.  The scalar is obtained by Bézout inversion.

This is the extra normalization needed before the cyclic twisted trace
can satisfy the signed-irreducibility theorem.  Merely requiring
`P ^ n = 1` leaves an arbitrary `n`-th-root-of-unity ambiguity.
-/

noncomputable section

namespace McKayConjecture
namespace RepresentationTheory

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable [FiniteDimensional ℂ V]

/-- Determinant as a homomorphism on units of the endomorphism ring. -/
def endomorphismUnitDeterminant :
    (Module.End ℂ V)ˣ →* ℂˣ :=
  LinearEquiv.det.comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv
      ℂ V).toMonoidHom

@[simp]
theorem endomorphismUnitDeterminant_coe
    (P : (Module.End ℂ V)ˣ) :
    ((endomorphismUnitDeterminant P : ℂˣ) : ℂ) =
      LinearMap.det
        (P : Module.End ℂ V) := by
  simp [endomorphismUnitDeterminant,
    LinearEquiv.coe_det]

/-- Scalar units embedded in the units of the endomorphism ring. -/
def scalarEndomorphismUnit :
    ℂˣ →* (Module.End ℂ V)ˣ :=
  Units.map
    (algebraMap ℂ (Module.End ℂ V)).toMonoidHom

@[simp]
theorem scalarEndomorphismUnit_val
    (z : ℂˣ) :
    ((scalarEndomorphismUnit (V := V) z :
      (Module.End ℂ V)ˣ) : Module.End ℂ V) =
      algebraMap ℂ (Module.End ℂ V) (z : ℂ) :=
  rfl

/-- Scalar units commute with every invertible endomorphism. -/
theorem scalarEndomorphismUnit_comm
    (z : ℂˣ) (P : (Module.End ℂ V)ˣ) :
    scalarEndomorphismUnit (V := V) z * P =
      P * scalarEndomorphismUnit (V := V) z := by
  apply Units.ext
  simp only [Units.val_mul,
    scalarEndomorphismUnit_val]
  exact Algebra.commutes (z : ℂ)
    (P : Module.End ℂ V)

/-- The determinant of a scalar unit is the scalar raised to the
dimension. -/
@[simp]
theorem endomorphismUnitDeterminant_scalar
    (z : ℂˣ) :
    endomorphismUnitDeterminant
        (scalarEndomorphismUnit (V := V) z) =
      z ^ Module.finrank ℂ V := by
  apply Units.ext
  simp only [endomorphismUnitDeterminant,
    MonoidHom.comp_apply, LinearEquiv.coe_det]
  change
    LinearMap.det
        (algebraMap ℂ (Module.End ℂ V) (z : ℂ)) =
      (z : ℂ) ^ Module.finrank ℂ V
  rw [Algebra.algebraMap_eq_smul_one]
  change
    LinearMap.det
        ((z : ℂ) •
          (LinearMap.id : Module.End ℂ V)) =
      (z : ℂ) ^ Module.finrank ℂ V
  rw [LinearMap.det_smul, LinearMap.det_id,
    mul_one]

/-- The Bézout scalar which kills the determinant of `P`. -/
def determinantNormalizingScalar
    (P : (Module.End ℂ V)ˣ) (n : ℕ) :
    ℂˣ :=
  endomorphismUnitDeterminant P ^
    (-(n.gcdB (Module.finrank ℂ V)))

/-- The determinant-normalized central scalar multiple of `P`. -/
def determinantNormalizedUnit
    (P : (Module.End ℂ V)ˣ) (n : ℕ) :
    (Module.End ℂ V)ˣ :=
  scalarEndomorphismUnit
      (determinantNormalizingScalar P n) *
    P

/-- The normalizing scalar still has `n`-th power one. -/
theorem determinantNormalizingScalar_pow_eq_one
    (P : (Module.End ℂ V)ˣ) (n : ℕ)
    (hPn : P ^ n = 1) :
    determinantNormalizingScalar P n ^ n = 1 := by
  let delta : ℂˣ :=
    endomorphismUnitDeterminant P
  have hdelta :
      delta ^ n = 1 := by
    change
      endomorphismUnitDeterminant P ^ n = 1
    rw [← map_pow, hPn, map_one]
  change
    (delta ^ (-(n.gcdB
      (Module.finrank ℂ V)))) ^ n = 1
  rw [← zpow_natCast, ← zpow_mul,
    mul_comm, zpow_mul, zpow_natCast,
    hdelta, one_zpow]

/-- Determinant normalization preserves the `n`-th-power identity. -/
theorem determinantNormalizedUnit_pow_eq_one
    (P : (Module.End ℂ V)ˣ) (n : ℕ)
    (hPn : P ^ n = 1) :
    determinantNormalizedUnit P n ^ n = 1 := by
  have hcomm :
      Commute
        (scalarEndomorphismUnit
          (determinantNormalizingScalar P n)) P :=
    scalarEndomorphismUnit_comm
      (determinantNormalizingScalar P n) P
  rw [determinantNormalizedUnit,
    hcomm.mul_pow,
    ← map_pow,
    determinantNormalizingScalar_pow_eq_one P n hPn,
    hPn, map_one, one_mul]

/-- Under the coprime-dimension hypothesis, the normalized unit has
determinant one. -/
theorem endomorphismUnitDeterminant_determinantNormalizedUnit
    (P : (Module.End ℂ V)ˣ) (n : ℕ)
    (hcoprime :
      n.Coprime (Module.finrank ℂ V))
    (hPn : P ^ n = 1) :
    endomorphismUnitDeterminant
        (determinantNormalizedUnit P n) =
      1 := by
  let d : ℕ := Module.finrank ℂ V
  let delta : ℂˣ :=
    endomorphismUnitDeterminant P
  have hdelta :
      delta ^ n = 1 := by
    change
      endomorphismUnitDeterminant P ^ n = 1
    rw [← map_pow, hPn, map_one]
  have hroot :
      delta = (delta ^ d) ^ n.gcdB d :=
    IrreducibleCharacter.eq_pow_gcdB_of_pow_eq_one
      delta n d hcoprime hdelta
  rw [determinantNormalizedUnit, map_mul,
    endomorphismUnitDeterminant_scalar]
  change
    (delta ^ (-(n.gcdB d))) ^ d * delta = 1
  have hpower :
      (delta ^ (-(n.gcdB d))) ^ d =
        (delta ^ d) ^ (-(n.gcdB d)) := by
    rw [← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast]
  calc
    (delta ^ (-(n.gcdB d))) ^ d * delta =
        (delta ^ d) ^ (-(n.gcdB d)) *
          delta := by rw [hpower]
    _ = (delta ^ d) ^ (-(n.gcdB d)) *
          (delta ^ d) ^ n.gcdB d := by
      rw [← hroot]
    _ = 1 := by group

end RepresentationTheory
end McKayConjecture
