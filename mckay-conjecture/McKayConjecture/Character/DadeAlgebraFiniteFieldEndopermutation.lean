/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraFiniteFieldModel
import McKayConjecture.Character.EndopermutationModule

/-!
# Endopermutation modules attached to finite-field Dade algebras

Transporting the pointed permutation basis of a Dade algebra through
its finite-field endomorphism model makes the honestly lifted module
into a pointed endopermutation module.
-/

noncomputable section

namespace Representation

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [Finite k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

namespace DadeAlgebra
namespace FiniteFieldModel

variable
  (M : FiniteFieldModel k A)
  (S : DadeAlgebra p k P A)

/-- The transported algebra basis on the split endomorphism algebra is
stable under conjugation by the lifted linear action. -/
def pointedPermutationAlgebraBasis :
    letI :=
      endomorphismConjugationMulSemiringAction
        (M.liftedLinearAction S.isPGroup)
    letI :=
      endomorphismConjugation_smulCommClass
        (M.liftedLinearAction S.isPGroup)
    PointedPermutationAlgebraBasis
      (k := k) (P := P)
      (A := Module.End k M.ModuleSpace) := by
  let rho := M.liftedLinearAction S.isPGroup
  letI :=
    endomorphismConjugationMulSemiringAction rho
  letI :=
    endomorphismConjugation_smulCommClass rho
  exact
    { index := S.permutationBasis.index
      indexAction := S.permutationBasis.indexAction
      basis :=
        S.permutationBasis.basis.map
          M.algEquiv.toLinearEquiv
      smul_basis := by
        intro g i
        change
          g • M.algEquiv (S.permutationBasis.basis i) =
            M.algEquiv
              (S.permutationBasis.basis
                (S.permutationBasis.indexAction g i))
        rw [M.algEquiv_smul S.isPGroup]
        rw [S.permutationBasis.smul_basis]
      oneIndex := S.permutationBasis.oneIndex
      basis_oneIndex := by
        change
          M.algEquiv
              (S.permutationBasis.basis
                S.permutationBasis.oneIndex) =
            1
        rw [S.permutationBasis.basis_oneIndex]
        exact map_one M.algEquiv }

/-- The split module of a Dade algebra over a finite field, equipped
with the honest action lifting the transported algebra action, is a
pointed endopermutation module. -/
def pointedEndopermutationModule :
    PointedEndopermutationModule
      p k P M.ModuleSpace where
  action := M.liftedLinearAction S.isPGroup
  isPGroup := S.isPGroup
  permutationBasis := M.pointedPermutationAlgebraBasis S

end FiniteFieldModel

/-- Canonical chosen pointed endopermutation realization of a
finite-field Dade algebra. -/
def finiteFieldPointedEndopermutationModule
    (S : DadeAlgebra p k P A) :
    PointedEndopermutationModule
      p k P S.finiteFieldModel.ModuleSpace :=
  S.finiteFieldModel.pointedEndopermutationModule S

end DadeAlgebra
end Representation
