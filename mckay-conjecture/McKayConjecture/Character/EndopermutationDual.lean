/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismDualEquivariance
import McKayConjecture.Character.EndopermutationModule

/-!
# Duals of pointed endopermutation modules

Transposition carries a pointed permutation basis of `End(V)` to one
of `End(V*)`.  Its equivariance for the contragredient action proves
that finite-dimensional pointed endopermutation modules are closed
under duality.
-/

noncomputable section

namespace Representation
namespace PointedEndopermutationModule

variable {p : ℕ} [Fact p.Prime]
variable {k P V : Type}
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Nontrivial V]

variable (M : PointedEndopermutationModule p k P V)

/-- The dual of a nonzero finite-dimensional vector space is
nonzero. -/
theorem dualNontrivial :
    Nontrivial (Module.Dual k V) :=
  Module.nontrivial_of_finrank_pos (R := k) <| by
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_pos

/-- The pointed permutation basis of `End(V*)` obtained by
transposing the pointed permutation basis of `End(V)`. -/
def dualPermutationBasis :
    let dualAction := contragredientLinearAction M.action
    letI :=
      endomorphismConjugationMulSemiringAction dualAction
    letI :=
      endomorphismConjugation_smulCommClass dualAction
    PointedPermutationAlgebraBasis
      (k := k) (P := P)
      (A := Module.End k (Module.Dual k V)) := by
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  let dualAction :=
    contragredientLinearAction M.action
  letI :=
    endomorphismConjugationMulSemiringAction dualAction
  letI :=
    endomorphismConjugation_smulCommClass dualAction
  exact
    { index := M.permutationBasis.index
      indexAction := M.permutationBasis.indexAction
      basis :=
        M.permutationBasis.basis.map
          endomorphismDualLinearEquiv
      smul_basis := fun g i ↦ by
        rw [Module.Basis.map_apply]
        rw [endomorphismDualLinearEquiv_conjugation M.action]
        rw [M.permutationBasis.smul_basis]
        rw [Module.Basis.map_apply]
      oneIndex := M.permutationBasis.oneIndex
      basis_oneIndex := by
        rw [Module.Basis.map_apply]
        rw [M.permutationBasis.basis_oneIndex]
        exact endomorphismDualLinearEquiv_one }

/-- Dual closure of finite-dimensional pointed endopermutation
modules. -/
def dual :
    letI : Nontrivial (Module.Dual k V) :=
      dualNontrivial (k := k) (V := V)
    PointedEndopermutationModule p k P
      (Module.Dual k V) := by
  letI : Nontrivial (Module.Dual k V) :=
    dualNontrivial (k := k) (V := V)
  exact
    { action := contragredientLinearAction M.action
      isPGroup := M.isPGroup
      permutationBasis := M.dualPermutationBasis }

end PointedEndopermutationModule
end Representation
