/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Endomorphisms of a finite-dimensional dual space

Transposition sends an endomorphism of `V` to an endomorphism of
`V*`.  It is linear and reverses multiplication.  For
finite-dimensional vector spaces it is bijective, so after placing an
opposite algebra on the source it gives the canonical algebra
equivalence

`End_k(V)ᵐᵒᵖ ≃ₐ[k] End_k(V*)`.
-/

noncomputable section

namespace Representation

variable {k V : Type}
variable [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Transposition as a linear equivalence between the two
endomorphism spaces.  Its inverse uses the canonical
finite-dimensional identification `V ≃ V**`. -/
def endomorphismDualLinearEquiv :
    Module.End k V ≃ₗ[k]
      Module.End k (Module.Dual k V) where
  __ := Module.Dual.transpose
  invFun F :=
    (Module.evalEquiv k V).symm.toLinearMap.comp
      (F.dualMap.comp (Module.evalEquiv k V).toLinearMap)
  left_inv f := by
    apply LinearMap.ext
    intro v
    apply (Module.evalEquiv k V).injective
    apply LinearMap.ext
    intro phi
    change
      (Module.evalEquiv k V
        ((Module.evalEquiv k V).symm
          ((Module.Dual.transpose f).dualMap
            (Module.evalEquiv k V v)))) phi =
        Module.evalEquiv k V (f v) phi
    rw [(Module.evalEquiv k V).apply_symm_apply]
    rfl
  right_inv F := by
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro v
    change
      phi ((Module.evalEquiv k V).symm
        (F.dualMap (Module.evalEquiv k V v))) =
        F phi v
    rw [Module.apply_evalEquiv_symm_apply]
    rfl

@[simp]
theorem endomorphismDualLinearEquiv_apply
    (f : Module.End k V) :
    endomorphismDualLinearEquiv f = f.dualMap :=
  rfl

@[simp]
theorem endomorphismDualLinearEquiv_apply_apply
    (f : Module.End k V)
    (phi : Module.Dual k V) (v : V) :
    endomorphismDualLinearEquiv f phi v = phi (f v) :=
  rfl

/-- The linear equivalence from the opposite endomorphism algebra to
the endomorphism algebra of the dual. -/
def endomorphismDualOppositeLinearEquiv :
    (Module.End k V)ᵐᵒᵖ ≃ₗ[k]
      Module.End k (Module.Dual k V) :=
  (MulOpposite.opLinearEquiv k).symm.trans
    endomorphismDualLinearEquiv

@[simp]
theorem endomorphismDualOppositeLinearEquiv_apply
    (f : (Module.End k V)ᵐᵒᵖ) :
    endomorphismDualOppositeLinearEquiv f = f.unop.dualMap :=
  rfl

/-- Transposition reverses composition. -/
theorem endomorphismDualLinearEquiv_mul
    (f g : Module.End k V) :
    endomorphismDualLinearEquiv (f * g) =
      endomorphismDualLinearEquiv g *
        endomorphismDualLinearEquiv f := by
  exact Module.Dual.transpose_comp f g

/-- Transposition preserves the identity endomorphism. -/
theorem endomorphismDualLinearEquiv_one :
    endomorphismDualLinearEquiv
        (1 : Module.End k V) =
      1 := by
  exact LinearMap.dualMap_id

/-- Transposition, with the opposite multiplication on its source,
as an algebra homomorphism. -/
def endomorphismDualOppositeAlgHom :
    (Module.End k V)ᵐᵒᵖ →ₐ[k]
      Module.End k (Module.Dual k V) :=
  AlgHom.ofLinearMap
    endomorphismDualOppositeLinearEquiv.toLinearMap
    (by
      change endomorphismDualLinearEquiv
        (1 : Module.End k V) = 1
      exact endomorphismDualLinearEquiv_one)
    (by
      intro f g
      change
        endomorphismDualLinearEquiv (g.unop * f.unop) =
          endomorphismDualLinearEquiv f.unop *
            endomorphismDualLinearEquiv g.unop
      exact endomorphismDualLinearEquiv_mul g.unop f.unop)

@[simp]
theorem endomorphismDualOppositeAlgHom_apply
    (f : (Module.End k V)ᵐᵒᵖ) :
    endomorphismDualOppositeAlgHom f = f.unop.dualMap :=
  rfl

/-- Canonical algebra equivalence
`End_k(V)ᵐᵒᵖ ≃ₐ[k] End_k(V*)`. -/
def endomorphismDualOppositeAlgEquiv :
    (Module.End k V)ᵐᵒᵖ ≃ₐ[k]
      Module.End k (Module.Dual k V) :=
  AlgEquiv.ofBijective
    endomorphismDualOppositeAlgHom
    endomorphismDualOppositeLinearEquiv.bijective

@[simp]
theorem endomorphismDualOppositeAlgEquiv_apply
    (f : (Module.End k V)ᵐᵒᵖ) :
    endomorphismDualOppositeAlgEquiv f = f.unop.dualMap :=
  rfl

/-- The inverse orientation of the canonical endomorphism-dual
algebra equivalence. -/
def endomorphismDualAlgEquivOpposite :
    Module.End k (Module.Dual k V) ≃ₐ[k]
      (Module.End k V)ᵐᵒᵖ :=
  endomorphismDualOppositeAlgEquiv.symm

end Representation
