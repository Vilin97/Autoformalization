/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismInteriorAction
import McKayConjecture.Character.EndomorphismTensorProduct

/-!
# Equivariance of the endomorphism tensor-product equivalence

The canonical equivalence

`End(V) ⊗ End(W) ≃ End(V ⊗ W)`

intertwines factorwise conjugation with conjugation by the diagonal
tensor-product action.  The pure-tensor formula established here is
the input needed to transport pointed permutation bases.
-/

noncomputable section

open scoped TensorProduct

namespace Representation

variable {k P V W : Type}
variable [Field k] [Group P]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The diagonal tensor product of two linear group actions. -/
def tensorProductLinearAction
    (rho : P →* (V ≃ₗ[k] V))
    (sigma : P →* (W ≃ₗ[k] W)) :
    P →* ((V ⊗[k] W) ≃ₗ[k] (V ⊗[k] W)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv
      k (V ⊗[k] W)).toMonoidHom.comp
    ((linearActionRepresentation rho).tprod
      (linearActionRepresentation sigma)).toHomUnits

omit [FiniteDimensional k V] [FiniteDimensional k W] in
@[simp]
theorem tensorProductLinearAction_apply_tmul
    (rho : P →* (V ≃ₗ[k] V))
    (sigma : P →* (W ≃ₗ[k] W))
    (g : P) (v : V) (w : W) :
    tensorProductLinearAction rho sigma g (v ⊗ₜ[k] w) =
      rho g v ⊗ₜ[k] sigma g w := by
  change
    ((linearActionRepresentation rho).tprod
      (linearActionRepresentation sigma)) g (v ⊗ₜ[k] w) =
        rho g v ⊗ₜ[k] sigma g w
  simp only [Representation.tprod_apply, TensorProduct.map_tmul,
    linearActionRepresentation_apply]
  rfl

omit [FiniteDimensional k V] [FiniteDimensional k W] in
@[simp]
theorem tensorProductLinearAction_symm_apply_tmul
    (rho : P →* (V ≃ₗ[k] V))
    (sigma : P →* (W ≃ₗ[k] W))
    (g : P) (v : V) (w : W) :
    (tensorProductLinearAction rho sigma g).symm (v ⊗ₜ[k] w) =
      (rho g).symm v ⊗ₜ[k] (sigma g).symm w := by
  have htensor :
      (tensorProductLinearAction rho sigma g).symm =
        tensorProductLinearAction rho sigma g⁻¹ := by
    symm
    exact map_inv (tensorProductLinearAction rho sigma) g
  have hrho : (rho g).symm = rho g⁻¹ := by
    symm
    exact map_inv rho g
  have hsigma : (sigma g).symm = sigma g⁻¹ := by
    symm
    exact map_inv sigma g
  rw [htensor, hrho, hsigma]
  exact tensorProductLinearAction_apply_tmul
    rho sigma g⁻¹ v w

omit [FiniteDimensional k V] in
@[simp]
theorem linearActionUnit_apply
    (rho : P →* (V ≃ₗ[k] V))
    (g : P) (v : V) :
    (linearActionUnit rho g : Module.End k V) v =
      rho g v :=
  rfl

omit [FiniteDimensional k V] in
@[simp]
theorem linearActionUnit_inv_apply
    (rho : P →* (V ≃ₗ[k] V))
    (g : P) (v : V) :
    (↑((linearActionUnit rho g)⁻¹) : Module.End k V) v =
      (rho g).symm v :=
  rfl

omit [FiniteDimensional k V] in
/-- Pointwise formula for the conjugation action on an endomorphism. -/
@[simp]
theorem endomorphismConjugation_smul_apply
    (rho : P →* (V ≃ₗ[k] V))
    (g : P) (f : Module.End k V) (v : V) :
    letI := endomorphismConjugationMulSemiringAction rho
    (g • f) v =
      rho g (f ((rho g).symm v)) := by
  letI := endomorphismConjugationMulSemiringAction rho
  simp only [endomorphismConjugation_smul,
    Module.End.mul_apply, linearActionUnit_apply,
    linearActionUnit_inv_apply]

omit [FiniteDimensional k V] [FiniteDimensional k W] in
/-- The factorwise conjugation action on the tensor product of the two
endomorphism spaces. -/
def endomorphismTensorProductFactorAction
    (rho : P →* (V ≃ₗ[k] V))
    (sigma : P →* (W ≃ₗ[k] W)) :
    letI := endomorphismConjugationMulSemiringAction rho
    letI := endomorphismConjugation_smulCommClass rho
    letI := endomorphismConjugationMulSemiringAction sigma
    letI := endomorphismConjugation_smulCommClass sigma
    P →* (((Module.End k V) ⊗[k] (Module.End k W)) ≃ₗ[k]
      ((Module.End k V) ⊗[k] (Module.End k W))) := by
  letI := endomorphismConjugationMulSemiringAction rho
  letI := endomorphismConjugation_smulCommClass rho
  letI := endomorphismConjugationMulSemiringAction sigma
  letI := endomorphismConjugation_smulCommClass sigma
  exact tensorProductLinearAction
    (DistribMulAction.toModuleAut k (Module.End k V))
    (DistribMulAction.toModuleAut k (Module.End k W))

omit [FiniteDimensional k V] [FiniteDimensional k W] in
@[simp]
theorem endomorphismTensorProductFactorAction_apply_tmul
    (rho : P →* (V ≃ₗ[k] V))
    (sigma : P →* (W ≃ₗ[k] W))
    (g : P) (f : Module.End k V) (h : Module.End k W) :
    letI := endomorphismConjugationMulSemiringAction rho
    letI := endomorphismConjugation_smulCommClass rho
    letI := endomorphismConjugationMulSemiringAction sigma
    letI := endomorphismConjugation_smulCommClass sigma
    endomorphismTensorProductFactorAction rho sigma g
        (f ⊗ₜ[k] h) =
      (g • f) ⊗ₜ[k] (g • h) := by
  letI := endomorphismConjugationMulSemiringAction rho
  letI := endomorphismConjugation_smulCommClass rho
  letI := endomorphismConjugationMulSemiringAction sigma
  letI := endomorphismConjugation_smulCommClass sigma
  change
    tensorProductLinearAction
        (DistribMulAction.toModuleAut k (Module.End k V))
        (DistribMulAction.toModuleAut k (Module.End k W)) g
        (f ⊗ₜ[k] h) =
      (g • f) ⊗ₜ[k] (g • h)
  rw [tensorProductLinearAction_apply_tmul]
  rfl

/-- The canonical endomorphism-algebra tensor equivalence intertwines
factorwise conjugation with conjugation by the diagonal tensor action,
on pure tensors. -/
theorem endomorphismTensorProductAlgEquiv_conjugation_tmul
    (rho : P →* (V ≃ₗ[k] V))
    (sigma : P →* (W ≃ₗ[k] W))
    (g : P) (f : Module.End k V) (h : Module.End k W) :
    letI := endomorphismConjugationMulSemiringAction rho
    letI := endomorphismConjugationMulSemiringAction sigma
    letI :=
      endomorphismConjugationMulSemiringAction
        (tensorProductLinearAction rho sigma)
    g • endomorphismTensorProductAlgEquiv (f ⊗ₜ[k] h) =
      endomorphismTensorProductAlgEquiv
        ((g • f) ⊗ₜ[k] (g • h)) := by
  letI := endomorphismConjugationMulSemiringAction rho
  letI := endomorphismConjugationMulSemiringAction sigma
  letI :=
    endomorphismConjugationMulSemiringAction
      (tensorProductLinearAction rho sigma)
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul v w =>
      simp only [endomorphismTensorProductAlgEquiv_tmul,
        endomorphismConjugation_smul_apply,
        tensorProductLinearAction_symm_apply_tmul,
        TensorProduct.map_tmul,
        tensorProductLinearAction_apply_tmul]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- The canonical endomorphism-algebra tensor equivalence is
equivariant for factorwise conjugation on its source and conjugation
by the diagonal tensor action on its target. -/
theorem endomorphismTensorProductAlgEquiv_conjugation
    (rho : P →* (V ≃ₗ[k] V))
    (sigma : P →* (W ≃ₗ[k] W))
    (g : P)
    (x : (Module.End k V) ⊗[k] (Module.End k W)) :
    letI := endomorphismConjugationMulSemiringAction rho
    letI := endomorphismConjugation_smulCommClass rho
    letI := endomorphismConjugationMulSemiringAction sigma
    letI := endomorphismConjugation_smulCommClass sigma
    letI :=
      endomorphismConjugationMulSemiringAction
        (tensorProductLinearAction rho sigma)
    g • endomorphismTensorProductAlgEquiv x =
      endomorphismTensorProductAlgEquiv
        (endomorphismTensorProductFactorAction rho sigma g x) := by
  letI := endomorphismConjugationMulSemiringAction rho
  letI := endomorphismConjugation_smulCommClass rho
  letI := endomorphismConjugationMulSemiringAction sigma
  letI := endomorphismConjugation_smulCommClass sigma
  letI :=
    endomorphismConjugationMulSemiringAction
      (tensorProductLinearAction rho sigma)
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul f h =>
      simpa only [
        endomorphismTensorProductFactorAction_apply_tmul] using
        endomorphismTensorProductAlgEquiv_conjugation_tmul
          rho sigma g f h
  | add x y hx hy =>
      simp only [map_add, smul_add, hx, hy]

end Representation
