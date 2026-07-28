/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveTensor

/-!
# Scalar extraction from finite tensor operators

A coordinatewise scalar multiple of a family of linear equivalences induces
the product scalar times the tensor of the unscaled equivalences.  This
operator identity is the zero-safe analogue of extracting scalars from a
product of traces.
-/

noncomputable section

open scoped BigOperators TensorProduct

universe u v w

namespace McKayConjecture
namespace CharacterTriple

variable {K : Type u} [Field K]
variable {ι : Type v} [Fintype ι]
variable {V : ι → Type w}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Coordinatewise unit scalars factor out of a finite dependent tensor of
linear equivalences as their product. -/
theorem piTensorCongr_scalar_mul
    (c : ι → Kˣ)
    (f : ∀ i, V i ≃ₗ[K] V i) :
    PiTensorProduct.congr
        (fun i ↦ scalarLinearEquiv K (V i) (c i) * f i) =
      scalarLinearEquiv K (⨂[K] i, V i) (∏ i, c i) *
        PiTensorProduct.congr f := by
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change
    PiTensorProduct.congr
        (fun i ↦ scalarLinearEquiv K (V i) (c i) * f i)
        (PiTensorProduct.tprod K x) =
      (scalarLinearEquiv K (⨂[K] i, V i) (∏ i, c i) *
        PiTensorProduct.congr f)
        (PiTensorProduct.tprod K x)
  rw [PiTensorProduct.congr_tprod, LinearEquiv.mul_apply,
    PiTensorProduct.congr_tprod, scalarLinearEquiv_apply]
  simp_rw [LinearEquiv.mul_apply, scalarLinearEquiv_apply]
  rw [(PiTensorProduct.tprod K).map_smul_univ]
  simp

end CharacterTriple
end McKayConjecture
