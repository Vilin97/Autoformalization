/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveTensor
import McKayConjecture.CharacterTriple.FiniteTensorPermutation

/-!
# Traces of fixed-coordinate tensor-permutation operators

When a group element fixes every coordinate, its tensor-permutation operator
is just the dependent tensor of its coordinate transports.  Consequently
its trace is the product of their traces.
-/

noncomputable section

open scoped BigOperators TensorProduct

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace FiniteTensorPermutationCocycle

variable {K : Type u} [Field K]
variable {A : Type v} [Group A]
variable {ι : Type w} [Fintype ι] [MulAction A ι]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A tensor-permutation operator has no reindexing contribution when the
group element fixes every coordinate. -/
theorem operator_eq_congr_of_fixed
    (C : FiniteTensorPermutationCocycle
      (K := K) (A := A) (ι := ι) V)
    (a : A) (hfixed : ∀ i : ι, a • i = i) :
    C.operator a =
      PiTensorProduct.congr (C.transport a) := by
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change
    C.operator a (PiTensorProduct.tprod K x) =
      PiTensorProduct.congr (C.transport a)
        (PiTensorProduct.tprod K x)
  rw [C.operator_tprod, PiTensorProduct.congr_tprod]
  congr 1
  funext i
  have hinv : a⁻¹ • i = i := by
    calc
      a⁻¹ • i = a⁻¹ • (a • i) := by rw [hfixed i]
      _ = i := inv_smul_smul a i
  rw [hinv]

/-- Trace formula for a fixed-coordinate tensor-permutation operator. -/
theorem trace_operator_of_fixed
    [Module.Finite K V]
    (C : FiniteTensorPermutationCocycle
      (K := K) (A := A) (ι := ι) V)
    (a : A) (hfixed : ∀ i : ι, a • i = i) :
    LinearMap.trace K (⨂[K] _i : ι, V) (C.operator a) =
      ∏ i, LinearMap.trace K V (C.transport a i) := by
  rw [C.operator_eq_congr_of_fixed a hfixed]
  exact
    ProjectiveRepresentation.trace_piTensorMap
      (fun i ↦ (C.transport a i : V →ₗ[K] V))

end FiniteTensorPermutationCocycle
end CharacterTriple
end McKayConjecture
