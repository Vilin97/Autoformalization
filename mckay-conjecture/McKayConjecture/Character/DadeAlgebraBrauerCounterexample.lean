/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerTrivialGroup
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# A higher-dimensional Dade-algebra Brauer quotient

This file gives a concrete counterexample to automatic
one-dimensionality.  Let the trivial group act trivially on the
two-by-two matrix algebra over a field of characteristic `p`.  Extend
the linearly independent set `{1}` to a basis; the trivial action
permutes this basis and fixes its distinguished unit vector.  Thus the
matrix algebra is a Dade algebra in the precise sense used by this
development.

Its Brauer quotient is the whole four-dimensional matrix algebra.  In
particular, central simplicity, finite-dimensionality, and the pointed
permutation-basis condition do not imply a scalar Brauer quotient.
-/

noncomputable section

namespace Representation
namespace DadeAlgebra

/-- The trivial action of a monoid on a semiring, kept as an explicit
definition so that it does not compete with action instances elsewhere. -/
@[instance_reducible]
def trivialMulSemiringAction
    (P A : Type*) [Monoid P] [Semiring A] :
    MulSemiringAction P A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- The trivial action commutes with scalar multiplication. -/
theorem trivialSMulCommClass
    (P k A : Type*)
    [Monoid P] [Semiring k] [Semiring A] [Module k A] :
    letI : MulSemiringAction P A :=
      trivialMulSemiringAction P A
    SMulCommClass P k A :=
  letI : MulSemiringAction P A :=
    trivialMulSemiringAction P A
  ⟨fun _ _ _ ↦ rfl⟩

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A] [Nontrivial A]

/-- A vector-space basis containing `1`, regarded as a pointed
permutation algebra basis for the trivial action. -/
def pointedPermutationBasisOfTrivialAction :
    letI : MulSemiringAction P A :=
      trivialMulSemiringAction P A
    letI : SMulCommClass P k A :=
      trivialSMulCommClass P k A
    PointedPermutationAlgebraBasis
      (k := k) (P := P) (A := A) := by
  letI : MulSemiringAction P A :=
    trivialMulSemiringAction P A
  letI : SMulCommClass P k A :=
    trivialSMulCommClass P k A
  let hOne :
      LinearIndepOn k id ({1} : Set A) :=
    (linearIndepOn_singleton_iff k).2 one_ne_zero
  let index :=
    hOne.extend (Set.subset_univ ({1} : Set A))
  let oneIndex : index :=
    ⟨1, hOne.subset_extend
      (Set.subset_univ ({1} : Set A)) (by simp)⟩
  exact
    { index := index
      indexAction := 1
      basis := Module.Basis.extend hOne
      smul_basis := fun _ _ ↦ rfl
      oneIndex := oneIndex
      basis_oneIndex :=
        Module.Basis.extend_apply_self hOne oneIndex }

/-- Any finite-dimensional central simple algebra becomes a Dade
algebra for a trivial `p`-group action. -/
def ofTrivialAction
    (hcentral : Algebra.IsCentral k A)
    (hsimple : IsSimpleRing A)
    (hfinite : FiniteDimensional k A)
    (hP : IsPGroup p P) :
    letI : MulSemiringAction P A :=
      trivialMulSemiringAction P A
    letI : SMulCommClass P k A :=
      trivialSMulCommClass P k A
    DadeAlgebra p k P A := by
  letI : MulSemiringAction P A :=
    trivialMulSemiringAction P A
  letI : SMulCommClass P k A :=
    trivialSMulCommClass P k A
  exact
    { isCentral := hcentral
      isSimple := hsimple
      finiteDimensional := hfinite
      isPGroup := hP
      permutationBasis :=
        pointedPermutationBasisOfTrivialAction
          (k := k) (P := P) (A := A) }

section MatrixCounterexample

variable (q : ℕ) [hq : Fact q.Prime]
variable (k : Type) [Field k] [hchar : CharP k q]

noncomputable local instance : Fintype Unit :=
  Fintype.ofFinite Unit

local instance :
    MulSemiringAction Unit (Matrix (Fin 2) (Fin 2) k) :=
  trivialMulSemiringAction Unit
    (Matrix (Fin 2) (Fin 2) k)

local instance :
    SMulCommClass Unit k (Matrix (Fin 2) (Fin 2) k) :=
  trivialSMulCommClass Unit k
    (Matrix (Fin 2) (Fin 2) k)

/-- The two-by-two matrix algebra with trivial group action, packaged
as a Dade algebra. -/
def matrixTwoTrivial :
    DadeAlgebra q k Unit
      (Matrix (Fin 2) (Fin 2) k) :=
  ofTrivialAction
    (p := q) (k := k) (P := Unit)
    (A := Matrix (Fin 2) (Fin 2) k)
    inferInstance inferInstance inferInstance
    (IsPGroup.iff_card.mpr ⟨0, by simp⟩)

include q hchar

/-- The Brauer quotient of the concrete matrix Dade algebra has
dimension four. -/
theorem finrank_brauerQuotientAlgebra_matrixTwoTrivial :
    Module.finrank k
        (BrauerQuotientAlgebra
          (k := k) (P := Unit)
          (A := Matrix (Fin 2) (Fin 2) k)) =
      4 := by
  rw [
    finrank_brauerQuotientAlgebra_eq_finrank_of_subsingleton_group
      (matrixTwoTrivial q k)]
  simp [Module.finrank_matrix]

/-- Therefore the concrete matrix Dade algebra is not
Brauer-primitive. -/
theorem matrixTwoTrivial_not_isBrauerPrimitive :
    ¬ (matrixTwoTrivial q k).IsBrauerPrimitive := by
  apply
    not_isBrauerPrimitive_of_subsingleton_group
      (matrixTwoTrivial q k)
  simp [Module.finrank_matrix]

/-- In particular, its Brauer quotient is not one-dimensional. -/
theorem finrank_brauerQuotientAlgebra_matrixTwoTrivial_ne_one :
    Module.finrank k
        (BrauerQuotientAlgebra
          (k := k) (P := Unit)
          (A := Matrix (Fin 2) (Fin 2) k)) ≠
      1 := by
  rw [
    finrank_brauerQuotientAlgebra_matrixTwoTrivial
      (q := q) (k := k)]
  decide

end MatrixCounterexample

end DadeAlgebra
end Representation
