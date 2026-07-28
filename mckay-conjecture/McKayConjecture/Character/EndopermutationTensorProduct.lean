/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismTensorProductEquivariance
import McKayConjecture.Character.EndopermutationModule
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor products of pointed endopermutation modules

The tensor product of two pointed endopermutation modules has diagonal
linear action.  Tensoring their stable endomorphism-algebra bases and
transporting across

`End(V) ⊗ End(W) ≃ End(V ⊗ W)`

gives a stable basis containing the identity.  This proves tensor
closure for the constructive pointed form of endopermutation modules.
-/

noncomputable section

open scoped TensorProduct

namespace Representation
namespace PointedEndopermutationModule

variable {p : ℕ} [Fact p.Prime]
variable {k P V W : Type}
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Nontrivial V]
variable [AddCommGroup W] [Module k W]
variable [FiniteDimensional k W] [Nontrivial W]

variable
  (M : PointedEndopermutationModule p k P V)
  (N : PointedEndopermutationModule p k P W)

/-- Product action on the paired indices of the two pointed
endomorphism-algebra permutation bases. -/
def tensorPermutationIndexAction :
    letI :=
      endomorphismConjugationMulSemiringAction M.action
    letI :=
      endomorphismConjugation_smulCommClass M.action
    letI :=
      endomorphismConjugationMulSemiringAction N.action
    letI :=
      endomorphismConjugation_smulCommClass N.action
    P →* Equiv.Perm
      (M.permutationBasis.index × N.permutationBasis.index) := by
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  letI :=
    endomorphismConjugationMulSemiringAction N.action
  letI :=
    endomorphismConjugation_smulCommClass N.action
  exact
    { toFun := fun g =>
        (M.permutationBasis.indexAction g).prodCongr
          (N.permutationBasis.indexAction g)
      map_one' := by
        apply Equiv.Perm.ext
        intro ij
        simp
      map_mul' := by
        intro g h
        apply Equiv.Perm.ext
        rintro ⟨i, j⟩
        simp }

/-- The pointed permutation basis on `End(V ⊗ W)` obtained by
tensoring the two input bases and transporting across the canonical
endomorphism-algebra equivalence. -/
def tensorProductPermutationBasis :
    let tensorAction :=
      tensorProductLinearAction M.action N.action
    letI :=
      endomorphismConjugationMulSemiringAction tensorAction
    letI :=
      endomorphismConjugation_smulCommClass tensorAction
    PointedPermutationAlgebraBasis
      (k := k) (P := P)
      (A := Module.End k (V ⊗[k] W)) := by
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  letI :=
    endomorphismConjugationMulSemiringAction N.action
  letI :=
    endomorphismConjugation_smulCommClass N.action
  let tensorAction :=
    tensorProductLinearAction M.action N.action
  letI :=
    endomorphismConjugationMulSemiringAction tensorAction
  letI :=
    endomorphismConjugation_smulCommClass tensorAction
  exact
    { index :=
        M.permutationBasis.index × N.permutationBasis.index
      indexAction :=
        tensorPermutationIndexAction (M := M) (N := N)
      basis :=
        (M.permutationBasis.basis.tensorProduct
          N.permutationBasis.basis).map
            endomorphismTensorProductAlgEquiv.toLinearEquiv
      smul_basis := fun g ij ↦ by
        simp only [Module.Basis.map_apply,
          Module.Basis.tensorProduct_apply']
        change
          g • endomorphismTensorProductAlgEquiv
              (M.permutationBasis.basis ij.1 ⊗ₜ[k]
                N.permutationBasis.basis ij.2) =
            endomorphismTensorProductAlgEquiv
              (M.permutationBasis.basis
                    ((tensorPermutationIndexAction
                      (M := M) (N := N) g ij).1) ⊗ₜ[k]
                N.permutationBasis.basis
                    ((tensorPermutationIndexAction
                      (M := M) (N := N) g ij).2))
        rw [
          endomorphismTensorProductAlgEquiv_conjugation_tmul
            M.action N.action]
        rw [M.permutationBasis.smul_basis,
          N.permutationBasis.smul_basis]
        rfl
      oneIndex :=
        (M.permutationBasis.oneIndex,
          N.permutationBasis.oneIndex)
      basis_oneIndex := by
        rw [Module.Basis.map_apply,
          Module.Basis.tensorProduct_apply']
        rw [M.permutationBasis.basis_oneIndex,
          N.permutationBasis.basis_oneIndex]
        exact map_one endomorphismTensorProductAlgEquiv }

/-- The tensor product of two nonzero finite-dimensional vector spaces
is nonzero. -/
theorem tensorProductNontrivial :
    Nontrivial (V ⊗[k] W) :=
  Module.nontrivial_of_finrank_pos (R := k) <| by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

/-- Tensor closure of pointed endopermutation modules. -/
def tensorProduct :
    letI : Nontrivial (V ⊗[k] W) :=
      tensorProductNontrivial (k := k) (V := V) (W := W)
    PointedEndopermutationModule p k P (V ⊗[k] W) := by
  letI : Nontrivial (V ⊗[k] W) :=
    tensorProductNontrivial (k := k) (V := V) (W := W)
  exact
    { action := tensorProductLinearAction M.action N.action
      isPGroup := M.isPGroup
      permutationBasis := M.tensorProductPermutationBasis N }

end PointedEndopermutationModule
end Representation
