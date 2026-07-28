/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products of endomorphism algebras

For finite-dimensional vector spaces `V` and `W`, the canonical map

`End_k(V) ⊗ End_k(W) → End_k(V ⊗ W)`

sends `f ⊗ g` to `TensorProduct.map f g`.  Mathlib provides the
underlying linear equivalence as `TensorProduct.homTensorHomEquiv`.
This file records that the equivalence preserves multiplication and
the unit, and packages it as an algebra equivalence.
-/

noncomputable section

open scoped TensorProduct

namespace Representation

universe u v w

variable {k : Type u} {V : Type v} {W : Type w}
variable [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The canonical linear equivalence from the tensor product of
endomorphism spaces to the endomorphism space of the tensor product. -/
abbrev endomorphismTensorProductLinearEquiv :
    (Module.End k V) ⊗[k] (Module.End k W) ≃ₗ[k]
      Module.End k (V ⊗[k] W) :=
  homTensorHomEquiv k V W V W

@[simp]
theorem endomorphismTensorProductLinearEquiv_tmul
  (f : Module.End k V) (g : Module.End k W) :
    endomorphismTensorProductLinearEquiv (f ⊗ₜ[k] g) =
      TensorProduct.map f g := by
  rw [homTensorHomEquiv_apply,
    TensorProduct.homTensorHomMap_apply]

/-- The canonical endomorphism tensor map preserves multiplication. -/
theorem endomorphismTensorProductLinearEquiv_mul
    (x y : (Module.End k V) ⊗[k] (Module.End k W)) :
    endomorphismTensorProductLinearEquiv (x * y) =
      endomorphismTensorProductLinearEquiv x *
        endomorphismTensorProductLinearEquiv y := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul f' g' =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul,
            endomorphismTensorProductLinearEquiv_tmul,
            TensorProduct.map_mul]
      | add y z hy hz =>
          simp only [mul_add, map_add, hy, hz, mul_add]
  | add x z hx hz =>
      simp only [add_mul, map_add, hx, hz, add_mul]

/-- The canonical endomorphism tensor map preserves the identity. -/
theorem endomorphismTensorProductLinearEquiv_one :
    endomorphismTensorProductLinearEquiv
        (1 : (Module.End k V) ⊗[k] (Module.End k W)) =
      1 := by
  rw [Algebra.TensorProduct.one_def,
    endomorphismTensorProductLinearEquiv_tmul,
    TensorProduct.map_one]

/-- The canonical algebra homomorphism from the tensor product of
endomorphism algebras to the endomorphism algebra of the tensor
product. -/
def endomorphismTensorProductAlgHom :
    (Module.End k V) ⊗[k] (Module.End k W) →ₐ[k]
      Module.End k (V ⊗[k] W) :=
  AlgHom.ofLinearMap
    endomorphismTensorProductLinearEquiv.toLinearMap
    endomorphismTensorProductLinearEquiv_one
    endomorphismTensorProductLinearEquiv_mul

@[simp]
theorem endomorphismTensorProductAlgHom_tmul
    (f : Module.End k V) (g : Module.End k W) :
    endomorphismTensorProductAlgHom (f ⊗ₜ[k] g) =
      TensorProduct.map f g :=
  endomorphismTensorProductLinearEquiv_tmul f g

/-- Canonical finite-dimensional algebra equivalence
`End(V) ⊗ End(W) ≃ End(V ⊗ W)`. -/
def endomorphismTensorProductAlgEquiv :
    (Module.End k V) ⊗[k] (Module.End k W) ≃ₐ[k]
      Module.End k (V ⊗[k] W) :=
  AlgEquiv.ofBijective
    endomorphismTensorProductAlgHom
    endomorphismTensorProductLinearEquiv.bijective

@[simp]
theorem endomorphismTensorProductAlgEquiv_tmul
    (f : Module.End k V) (g : Module.End k W) :
    endomorphismTensorProductAlgEquiv (f ⊗ₜ[k] g) =
      TensorProduct.map f g :=
  endomorphismTensorProductAlgHom_tmul f g

end Representation
