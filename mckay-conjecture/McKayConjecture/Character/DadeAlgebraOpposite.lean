/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebra
import Mathlib.LinearAlgebra.Basis.MulOpposite

/-!
# Opposite Dade algebras

The opposite of a permutation algebra has the opposite stable basis:
apply `MulOpposite.op` to every basis vector and keep the same action
on the index set.  Centrality, simplicity, and finite dimensionality
are all preserved.  Consequently Dade algebras are closed under
passage to the opposite algebra.

This is the elementary opposite-algebra input used in the proof of
Thévenaz, *G-Algebras and Modular Representation Theory*,
Theorem 28.6(a).
-/

noncomputable section

namespace Representation

/-- A semiring action acts on the opposite ring by applying the
original action before `MulOpposite.op`. -/
instance oppositeMulSemiringAction
    {P A : Type}
    [Monoid P] [Semiring A] [MulSemiringAction P A] :
    MulSemiringAction P Aᵐᵒᵖ where
  smul := (· • ·)
  one_smul x := by
    apply MulOpposite.unop_injective
    simp
  mul_smul g h x := by
    apply MulOpposite.unop_injective
    exact mul_smul g h (MulOpposite.unop x)
  smul_zero g := by
    apply MulOpposite.unop_injective
    simp
  smul_add g x y := by
    apply MulOpposite.unop_injective
    simp
  smul_one g := by
    apply MulOpposite.unop_injective
    simp
  smul_mul g x y := by
    apply MulOpposite.unop_injective
    simp

namespace PointedPermutationAlgebraBasis

variable {k P A : Type}
variable [Field k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- The stable pointed basis obtained by applying `MulOpposite.op` to
every vector of a pointed permutation-algebra basis. -/
def opposite
    (B : PointedPermutationAlgebraBasis
      (k := k) (P := P) (A := A)) :
    PointedPermutationAlgebraBasis
      (k := k) (P := P) (A := Aᵐᵒᵖ) where
  index := B.index
  indexAction := B.indexAction
  basis := B.basis.mulOpposite
  smul_basis := by
    intro g i
    apply MulOpposite.unop_injective
    simpa using B.smul_basis g i
  oneIndex := B.oneIndex
  basis_oneIndex := by
    apply MulOpposite.unop_injective
    simpa using B.basis_oneIndex

omit [Fintype P] [SMulCommClass P k A] in
@[simp]
theorem opposite_basis_apply
    (B : PointedPermutationAlgebraBasis
      (k := k) (P := P) (A := A))
    (i : B.index) :
    B.opposite.basis i =
      MulOpposite.op (B.basis i) :=
  rfl

omit [Fintype P] [SMulCommClass P k A] in
@[simp]
theorem opposite_oneIndex
    (B : PointedPermutationAlgebraBasis
      (k := k) (P := P) (A := A)) :
    B.opposite.oneIndex = B.oneIndex :=
  rfl

end PointedPermutationAlgebraBasis

namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- Dade algebras are closed under passage to the opposite algebra. -/
def opposite
    (S : DadeAlgebra p k P A) :
    DadeAlgebra p k P Aᵐᵒᵖ := by
  letI : Algebra.IsCentral k A := S.isCentral
  letI : IsSimpleRing A := S.isSimple
  letI : FiniteDimensional k A := S.finiteDimensional
  exact
    { isCentral := inferInstance
      isSimple := inferInstance
      finiteDimensional := inferInstance
      isPGroup := S.isPGroup
      permutationBasis := S.permutationBasis.opposite }

end DadeAlgebra
end Representation
