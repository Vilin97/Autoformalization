/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.RootsOfUnity.Basic
import McKayConjecture.CharacterTriple.ProjectiveRepresentation

/-!
# Finite-image normalization of projective representations

For a finite-dimensional projective representation over an algebraically
closed field, rescale every chosen operator to determinant one.  A further
normalization at the identity preserves determinant one.  Taking
determinants in the projective multiplication law then shows that every
factor value is an `n`th root of unity, where `n` is the representation
dimension.

This supplies the finite coefficient group needed to replace a projective
representation by an honest representation of a finite central extension.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple

section UnitRoots

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The power map on the units of an algebraically closed field is
surjective in every positive degree. -/
theorem exists_unit_pow_eq
    (a : Kˣ) {n : ℕ} (hn : 0 < n) :
    ∃ b : Kˣ, b ^ n = a := by
  obtain ⟨b, hb⟩ :=
    IsAlgClosed.exists_pow_nat_eq (a : K) hn
  have hb0 : b ≠ 0 := by
    intro hzero
    have ha0 : (a : K) = 0 := by
      rw [← hb, hzero, zero_pow hn.ne']
    exact a.ne_zero ha0
  refine ⟨Units.mk0 b hb0, ?_⟩
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using hb

/-- A fixed `n`th root of a unit, selected noncomputably. -/
def unitNthRoot (a : Kˣ) (n : ℕ) (hn : 0 < n) : Kˣ :=
  Classical.choose (exists_unit_pow_eq a hn)

@[simp]
theorem unitNthRoot_pow
    (a : Kˣ) (n : ℕ) (hn : 0 < n) :
    unitNthRoot a n hn ^ n = a :=
  Classical.choose_spec (exists_unit_pow_eq a hn)

end UnitRoots

namespace ProjectiveRepresentation

variable {K : Type u} {G : Type v} {V : Type w}
variable [Field K] [IsAlgClosed K] [Group G]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]
variable [Nontrivial V]

omit [IsAlgClosed K] [Module.Finite K V] [Nontrivial V] in
/-- The determinant of a scalar linear automorphism is the scalar raised to
the dimension. -/
theorem det_scalarLinearEquiv
    (c : Kˣ) :
    LinearEquiv.det (scalarLinearEquiv K V c) =
      c ^ Module.finrank K V := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change
    LinearMap.det
        ((c : K) • (LinearMap.id : V →ₗ[K] V)) =
      (c : K) ^ Module.finrank K V
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]

omit [IsAlgClosed K] in
/-- The dimension of a nontrivial finite-dimensional vector space is
positive. -/
theorem finrank_pos :
    0 < Module.finrank K V :=
  Module.finrank_pos_iff.mpr inferInstance

/-- The scalar used to rescale one projective operator to determinant one. -/
def determinantRescaling
    (P : ProjectiveRepresentation K G V) (g : G) : Kˣ :=
  unitNthRoot
    (LinearEquiv.det (P.operator g))⁻¹
    (Module.finrank K V) finrank_pos

@[simp]
theorem determinantRescaling_pow
    (P : ProjectiveRepresentation K G V) (g : G) :
    P.determinantRescaling g ^ Module.finrank K V =
      (LinearEquiv.det (P.operator g))⁻¹ :=
  unitNthRoot_pow _ _ finrank_pos

/-- Rescale every chosen operator so that its determinant is one. -/
def determinantNormalize
    (P : ProjectiveRepresentation K G V) :
    ProjectiveRepresentation K G V :=
  P.rescale P.determinantRescaling

@[simp]
theorem determinantNormalize_operator_det
    (P : ProjectiveRepresentation K G V) (g : G) :
    LinearEquiv.det (P.determinantNormalize.operator g) = 1 := by
  rw [determinantNormalize, rescale_operator,
    (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).map_mul,
    det_scalarLinearEquiv, determinantRescaling_pow]
  exact inv_mul_cancel _

/-- Normalize the identity lift after determinant normalization.  The
identity correction is itself an `n`th root of unity, so all operators still
have determinant one. -/
def finiteFactorNormalize
    (P : ProjectiveRepresentation K G V) :
    ProjectiveRepresentation K G V :=
  P.determinantNormalize.normalize

theorem finiteFactorNormalize_isNormalized
    (P : ProjectiveRepresentation K G V) :
    P.finiteFactorNormalize.IsNormalized :=
  P.determinantNormalize.normalize_isNormalized

theorem determinantNormalize_factor_pow
    (P : ProjectiveRepresentation K G V) (g h : G) :
    P.determinantNormalize.factor g h ^
        Module.finrank K V = 1 := by
  have hdet :=
    congrArg
      (LinearEquiv.det :
        (V ≃ₗ[K] V) →* Kˣ)
      (P.determinantNormalize.map_mul g h)
  rw [
    (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).map_mul,
    (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).map_mul,
    determinantNormalize_operator_det,
    determinantNormalize_operator_det,
    determinantNormalize_operator_det,
    det_scalarLinearEquiv,
    one_mul, mul_one] at hdet
  simpa using hdet.symm

@[simp]
theorem finiteFactorNormalize_operator_det
    (P : ProjectiveRepresentation K G V) (g : G) :
    LinearEquiv.det (P.finiteFactorNormalize.operator g) = 1 := by
  rw [finiteFactorNormalize, normalize, rescale_operator,
    (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).map_mul,
    det_scalarLinearEquiv, determinantNormalize_operator_det]
  have hroot :=
    P.determinantNormalize_factor_pow 1 1
  simp only [inv_pow, hroot, inv_one, one_mul]

theorem finiteFactorNormalize_factor_pow
    (P : ProjectiveRepresentation K G V) (g h : G) :
    P.finiteFactorNormalize.factor g h ^
        Module.finrank K V = 1 := by
  have hdet :=
    congrArg
      (LinearEquiv.det :
        (V ≃ₗ[K] V) →* Kˣ)
      (P.finiteFactorNormalize.map_mul g h)
  rw [
    (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).map_mul,
    (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).map_mul,
    finiteFactorNormalize_operator_det,
    finiteFactorNormalize_operator_det,
    finiteFactorNormalize_operator_det,
    det_scalarLinearEquiv,
    one_mul, mul_one] at hdet
  simpa using hdet.symm

/-- The finite-image normalized factor set, with values bundled in the
finite group of `n`th roots of unity. -/
def finiteFactorSet
    (P : ProjectiveRepresentation K G V) :
    FactorSet G (rootsOfUnity (Module.finrank K V) K) where
  toFun g h :=
    ⟨P.finiteFactorNormalize.factor g h,
      P.finiteFactorNormalize_factor_pow g h⟩
  cocycle' g h k := by
    apply Subtype.ext
    exact P.finiteFactorNormalize.factor_cocycle g h k

@[simp]
theorem finiteFactorSet_coe
    (P : ProjectiveRepresentation K G V) (g h : G) :
    ((P.finiteFactorSet g h :
        rootsOfUnity (Module.finrank K V) K) : Kˣ) =
      P.finiteFactorNormalize.factor g h :=
  rfl

/-- The finite-image factor set is normalized. -/
theorem finiteFactorSet_isNormalized
    (P : ProjectiveRepresentation K G V) :
    P.finiteFactorSet.IsNormalized := by
  have hnormalized :
      P.finiteFactorNormalize.factorSet.IsNormalized :=
    P.finiteFactorNormalize.factorSet_isNormalized
      P.finiteFactorNormalize_isNormalized
  constructor
  · intro g
    apply Subtype.ext
    exact hnormalized.1 g
  · intro g
    apply Subtype.ext
    exact hnormalized.2 g

end ProjectiveRepresentation

end CharacterTriple
end McKayConjecture
