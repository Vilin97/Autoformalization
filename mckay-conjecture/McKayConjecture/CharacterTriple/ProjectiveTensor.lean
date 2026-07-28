/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetGroup
import McKayConjecture.CharacterTriple.ProjectiveRepresentation
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RepresentationTheory.Character

/-!
# Tensor products and duals of projective representations

The tensor product of projective representations has the product factor set.
The contragredient projective representation has the inverse factor set.
Consequently, tensoring a projective representation with a contragredient
one having the same factor set produces an honest linear representation.

These operations are the algebraic engine behind character-triple
correspondences: an associated projective representation carries the fixed
normal-subgroup character, while a projective multiplicity representation
with inverse factor set cancels its obstruction.
-/

noncomputable section

open scoped TensorProduct

universe u v w x

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} {G : Type v} {V : Type w} {W : Type x}
  [Field K] [Group G]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Tensor two projective representations pointwise.  Their scalar
obstructions multiply. -/
def tensor (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W) :
    ProjectiveRepresentation K G (V ⊗[K] W) where
  operator g := TensorProduct.congr (P.operator g) (Q.operator g)
  factor g h := P.factor g h * Q.factor g h
  map_mul g h := by
    rw [← TensorProduct.congr_mul, P.map_mul, Q.map_mul]
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro v w
    change
      ((P.factor g h : K) • P.operator (g * h) v) ⊗ₜ[K]
          ((Q.factor g h : K) • Q.operator (g * h) w) =
        ((P.factor g h * Q.factor g h : Kˣ) : K) •
          (P.operator (g * h) v ⊗ₜ[K] Q.operator (g * h) w)
    simpa only [Units.val_mul] using
      (TensorProduct.smul_tmul_smul
        (P.factor g h : K) (Q.factor g h : K)
        (P.operator (g * h) v) (Q.operator (g * h) w))

@[simp]
theorem tensor_operator (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W) (g : G) :
    (P.tensor Q).operator g =
      TensorProduct.congr (P.operator g) (Q.operator g) :=
  rfl

@[simp]
theorem tensor_factor (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W) (g h : G) :
    (P.tensor Q).factor g h = P.factor g h * Q.factor g h :=
  rfl

/-- Two projective representations have inverse factor sets when their
pointwise scalar obstructions are mutual inverses. -/
def HasInverseFactorSet
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W) : Prop :=
  ∀ g h, Q.factor g h = (P.factor g h)⁻¹

theorem HasInverseFactorSet.factor_mul
    {P : ProjectiveRepresentation K G V}
    {Q : ProjectiveRepresentation K G W}
    (hPQ : P.HasInverseFactorSet Q) (g h : G) :
    P.factor g h * Q.factor g h = 1 := by
  rw [hPQ]
  exact mul_inv_cancel _

section FactorSets

variable [Nontrivial V] [Nontrivial W] [Nontrivial (V ⊗[K] W)]

/-- The factor set of a tensor product is the product in the abelian group of
factor sets. -/
theorem tensor_factorSet
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W) :
    (P.tensor Q).factorSet = P.factorSet * Q.factorSet := by
  apply FactorSet.ext
  intro g h
  rfl

omit [Nontrivial (V ⊗[K] W)] in
/-- Inverse-factor compatibility is equality with the inverse in the factor
set group. -/
theorem hasInverseFactorSet_iff_factorSet_eq_inv
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W) :
    P.HasInverseFactorSet Q ↔ Q.factorSet = P.factorSet⁻¹ := by
  constructor
  · intro hPQ
    apply FactorSet.ext
    intro g h
    exact hPQ g h
  · intro hPQ g h
    exact congrArg (fun α : FactorSet G Kˣ ↦ α g h) hPQ

end FactorSets

/-- If the two factors cancel pointwise, the tensor product is an ordinary
linear action. -/
def tensorLinearAction
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W)
    (hfactor : ∀ g h, P.factor g h * Q.factor g h = 1) :
    G →* ((V ⊗[K] W) ≃ₗ[K] (V ⊗[K] W)) where
  toFun g := (P.tensor Q).operator g
  map_one' := by
    have h := (P.tensor Q).map_mul 1 1
    have h' :
        (P.tensor Q).operator 1 * (P.tensor Q).operator 1 =
          (P.tensor Q).operator 1 := by
      simpa only [tensor_factor, hfactor, map_one, one_mul, mul_one] using h
    apply mul_left_cancel (a := (P.tensor Q).operator 1)
    simpa only [mul_one] using h'
  map_mul' g h := by
    symm
    simpa only [tensor_factor, hfactor, map_one, one_mul] using
      (P.tensor Q).map_mul g h

@[simp]
theorem tensorLinearAction_apply
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W)
    (hfactor : ∀ g h, P.factor g h * Q.factor g h = 1)
    (g : G) :
    P.tensorLinearAction Q hfactor g =
      TensorProduct.congr (P.operator g) (Q.operator g) :=
  rfl

/-- The ordinary tensor action obtained from projective representations with
inverse factor sets. -/
def cancelTensorLinearAction
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W)
    (hPQ : P.HasInverseFactorSet Q) :
    G →* ((V ⊗[K] W) ≃ₗ[K] (V ⊗[K] W)) :=
  P.tensorLinearAction Q hPQ.factor_mul

@[simp]
theorem cancelTensorLinearAction_apply
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W)
    (hPQ : P.HasInverseFactorSet Q) (g : G) :
    P.cancelTensorLinearAction Q hPQ g =
      TensorProduct.congr (P.operator g) (Q.operator g) :=
  rfl

/-- The contragredient projective representation.  Inverting the operator
before transposing makes the assignment covariant in the group element; its
factor set is the pointwise inverse. -/
def contragredient (P : ProjectiveRepresentation K G V) :
    ProjectiveRepresentation K G (Module.Dual K V) where
  operator g := (P.operator g).symm.dualMap
  factor g h := (P.factor g h)⁻¹
  map_mul g h := by
    ext φ v
    simp only [LinearEquiv.mul_apply, LinearEquiv.dualMap_apply,
      scalarLinearEquiv_apply]
    have hmul := congrArg
      (fun f : V ≃ₗ[K] V ↦ f⁻¹) (P.map_mul g h)
    have happ := DFunLike.congr_fun hmul v
    simp only [mul_inv_rev, LinearEquiv.mul_apply] at happ
    have happ' :
        (P.operator h).symm ((P.operator g).symm v) =
          (P.operator (g * h)).symm
            ((scalarLinearEquiv K V (P.factor g h))⁻¹ v) :=
      happ
    rw [happ']
    have hscalar :
        (scalarLinearEquiv K V (P.factor g h))⁻¹ v =
          ((P.factor g h : K)⁻¹ • v) := by
      rw [← map_inv]
      rw [scalarLinearEquiv_apply, Units.val_inv_eq_inv_val]
    calc
      φ ((P.operator (g * h)).symm
          ((scalarLinearEquiv K V (P.factor g h))⁻¹ v)) =
          φ ((P.operator (g * h)).symm
            ((P.factor g h : K)⁻¹ • v)) := by rw [hscalar]
      _ = φ ((P.factor g h : K)⁻¹ •
          (P.operator (g * h)).symm v) := by
            rw [LinearEquiv.map_smul]
      _ = (P.factor g h : K)⁻¹ •
          φ ((P.operator (g * h)).symm v) := by
            rw [map_smul]
      _ = (↑((P.factor g h)⁻¹) : K) •
          φ ((P.operator (g * h)).symm v) := by
            rw [Units.val_inv_eq_inv_val]
      _ = ((↑((P.factor g h)⁻¹) : K) •
          (P.operator (g * h)).symm.dualMap φ) v := by
            rw [LinearMap.smul_apply, LinearEquiv.dualMap_apply]

@[simp]
theorem contragredient_operator
    (P : ProjectiveRepresentation K G V) (g : G) :
    P.contragredient.operator g = (P.operator g).symm.dualMap :=
  rfl

@[simp]
theorem contragredient_factor
    (P : ProjectiveRepresentation K G V) (g h : G) :
    P.contragredient.factor g h = (P.factor g h)⁻¹ :=
  rfl

/-- The contragredient has the inverse factor set. -/
theorem contragredient_factorSet
    (P : ProjectiveRepresentation K G V)
    [Nontrivial V] [Nontrivial (Module.Dual K V)] :
    P.contragredient.factorSet = P.factorSet⁻¹ := by
  apply FactorSet.ext
  intro g h
  rfl

theorem hasInverseFactorSet_contragredient
    (P : ProjectiveRepresentation K G V) :
    P.HasInverseFactorSet P.contragredient := by
  intro g h
  rfl

/-- A projective representation tensored with its contragredient is an
ordinary linear representation. -/
def endomorphismLinearAction (P : ProjectiveRepresentation K G V) :
    G →* ((V ⊗[K] Module.Dual K V) ≃ₗ[K]
      (V ⊗[K] Module.Dual K V)) :=
  P.tensorLinearAction P.contragredient (by
    intro g h
    simp)

@[simp]
theorem endomorphismLinearAction_apply
    (P : ProjectiveRepresentation K G V) (g : G) :
    P.endomorphismLinearAction g =
      TensorProduct.congr (P.operator g)
        (P.operator g).symm.dualMap :=
  rfl

section Trace

variable [Module.Finite K V] [Module.Finite K W]

/-- The trace function of the chosen lifts of a projective representation.
It is not, in general, an ordinary character because the lifts multiply only
up to the factor set. -/
def traceFunction (P : ProjectiveRepresentation K G V) : G → K :=
  fun g ↦ LinearMap.trace K V (P.operator g)

omit [Module.Finite K V] [Module.Finite K W] in
@[simp]
theorem traceFunction_apply
    (P : ProjectiveRepresentation K G V) (g : G) :
    P.traceFunction g = LinearMap.trace K V (P.operator g) :=
  rfl

/-- Projective trace functions multiply under tensor product, exactly as
ordinary characters do. -/
theorem traceFunction_tensor
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W) :
    (P.tensor Q).traceFunction = P.traceFunction * Q.traceFunction := by
  funext g
  exact LinearMap.trace_tensorProduct'
    (P.operator g : V →ₗ[K] V) (Q.operator g : W →ₗ[K] W)

/-- The character of the cancelled tensor action is the product of the two
projective trace functions. -/
theorem cancelTensorLinearAction_character
    (P : ProjectiveRepresentation K G V)
    (Q : ProjectiveRepresentation K G W)
    (hPQ : P.HasInverseFactorSet Q) :
    Representation.character
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (P.cancelTensorLinearAction Q hPQ) :
        Representation K G (V ⊗[K] W)) =
        P.traceFunction * Q.traceFunction := by
  funext g
  exact LinearMap.trace_tensorProduct'
    (P.operator g : V →ₗ[K] V) (Q.operator g : W →ₗ[K] W)

end Trace

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
