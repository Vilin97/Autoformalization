/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismFixedIntertwiner
import McKayConjecture.Character.PermutationModuleBasis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The permutation basis on an endomorphism algebra

A permutation basis of a linear module induces a permutation basis of
its endomorphism algebra, indexed by ordered pairs of basis indices.
The group acts diagonally on those pairs and by conjugation on
endomorphisms.
-/

noncomputable section

namespace Representation
namespace PermutationModuleBasis

variable {k P V ι : Type}
variable [Field k] [Group P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis
  (k := k) (P := P) (V := V) (ι := ι))

noncomputable local instance endomorphismPermutationBasisIndexFintype :
    Fintype ι :=
  Fintype.ofFinite ι

noncomputable local instance endomorphismPermutationBasisIndexDecidableEq :
    DecidableEq ι :=
  Classical.decEq ι

local instance endomorphismConjugationAction :
    MulSemiringAction P (Module.End k V) :=
  endomorphismConjugationMulSemiringAction
    (representationLinearAction
      (Representation.ofDistribMulAction k P V))

local instance endomorphismConjugationScalarComm :
    SMulCommClass P k (Module.End k V) :=
  endomorphismConjugation_smulCommClass
    (representationLinearAction
      (Representation.ofDistribMulAction k P V))

/-- Conjugation carries a matrix unit to the matrix unit obtained by
acting diagonally on its two indices. -/
theorem smul_end_basis
    (g : P) (ij : ι × ι) :
    g • B.basis.end ij =
      B.basis.end (g • ij) := by
  apply B.basis.ext
  intro t
  rw [endomorphismConjugation_smul
    (representationLinearAction B.representation)]
  have hinv :
      (↑((linearActionUnit
          (representationLinearAction B.representation) g)⁻¹) :
        Module.End k V) =
        B.representation g⁻¹ := by
    rw [← map_inv]
    exact
      linearActionUnit_representationLinearAction
        B.representation g⁻¹
  rw [hinv]
  simp only [Module.End.mul_apply,
    linearActionUnit_representationLinearAction,
    representation_apply]
  rw [B.smul_basis, B.basis.end_apply_apply]
  by_cases h : ij.2 = g⁻¹ • t
  · have ht : g • ij.2 = t := by
      rw [h, smul_smul, mul_inv_cancel, one_smul]
    rw [if_pos h, B.smul_basis,
      B.basis.end_apply_apply]
    simp [ht]
  · have ht : g • ij.2 ≠ t := by
      intro hgt
      apply h
      calc
        ij.2 = g⁻¹ • (g • ij.2) := by simp
        _ = g⁻¹ • t := by rw [hgt]
    rw [if_neg h, smul_zero,
      B.basis.end_apply_apply]
    simp [ht]

/-- The matrix units of a permutation basis form a permutation basis
of the endomorphism algebra for the conjugation action. -/
def endomorphism :
    PermutationModuleBasis
      (k := k) (P := P) (V := Module.End k V)
      (ι := ι × ι) where
  basis := B.basis.end
  smul_basis := B.smul_end_basis

@[simp]
theorem endomorphism_basis_apply
    (ij : ι × ι) :
    B.endomorphism.basis ij = B.basis.end ij :=
  rfl

end PermutationModuleBasis
end Representation
