/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationAlgebraBasis
import McKayConjecture.Character.PermutationModuleBrauerQuotientBasis
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# The Brauer quotient basis of a permutation algebra

This file transfers the permutation-module calculation of the Brauer
quotient to the multiplicative Brauer quotient of an algebra.  The
underlying `k`-submodule of the Brauer trace ideal is identified with
the linear Brauer trace submodule.  Consequently the images of the
globally fixed algebra-basis vectors form a basis of the algebra
Brauer quotient.
-/

noncomputable section

namespace Representation
namespace PointedPermutationAlgebraBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable
  (B : PointedPermutationAlgebraBasis
    (k := k) (P := P) (A := A))

attribute [local instance]
  PermutationModuleBasis.brauerQuotientBasisIndexFintype

/-- The action on the indices encoded by a pointed permutation algebra
basis. -/
@[instance_reducible]
def indexMulAction : MulAction P B.index where
  smul g i := B.indexAction g i
  one_smul i := by
    change B.indexAction 1 i = i
    rw [map_one]
    rfl
  mul_smul g h i := by
    change B.indexAction (g * h) i =
      B.indexAction g (B.indexAction h i)
    rw [map_mul]
    rfl

/-- A pointed permutation algebra basis, regarded as a permutation
basis of the underlying module. -/
abbrev toPermutationModuleBasis :
    letI : MulAction P B.index :=
      indexMulAction (B := B)
    PermutationModuleBasis
      (k := k) (P := P) (V := A) (ι := B.index) := by
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  exact
    { basis := B.basis
      smul_basis := B.smul_basis }

omit [Finite P] in
/-- The representation attached to the underlying permutation basis
is the algebra-action representation. -/
theorem toPermutationModuleBasis_representation :
    letI : MulAction P B.index :=
      indexMulAction (B := B)
    (toPermutationModuleBasis (B := B)).representation =
      algebraActionRepresentation
        (k := k) (P := P) (A := A) := by
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  ext g a
  rfl

/-- The Brauer trace ideal, regarded only as a `k`-submodule of the
fixed algebra. -/
def brauerTraceIdealAsSubmodule :
    Submodule k
      (fixedSubalgebra (k := k) (P := P) (A := A)) :=
  (brauerTraceIdeal
    (k := k) (P := P) (A := A)).restrictScalars k

/-- The image ideal of one algebra relative trace has the same
underlying `k`-submodule as the corresponding linear trace range. -/
theorem fixedRelativeTraceIdealAsSubmodule
    (Q : Subgroup P) :
    (fixedRelativeTraceIdeal
      (k := k) (P := P) (A := A) Q).restrictScalars k =
      relativeTraceRange
        (algebraActionRepresentation
          (k := k) (P := P) (A := A)) Q := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, x.property⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, x.property⟩, rfl⟩

/-- The algebra trace ideal and the linear trace submodule have the
same underlying `k`-submodule. -/
theorem brauerTraceIdealSubmodule_eq_brauerTraceSubmodule :
    brauerTraceIdealAsSubmodule (k := k) (P := P) (A := A) =
      brauerTraceSubmodule
        (algebraActionRepresentation
          (k := k) (P := P) (A := A)) := by
  simp only [brauerTraceIdealAsSubmodule, brauerTraceIdeal,
    brauerTraceSubmodule, Submodule.restrictScalars_iSup]
  congr with Q

/-- The multiplicative algebra Brauer quotient and the Brauer quotient
of the underlying linear representation are canonically linearly
equivalent. -/
def brauerQuotientAlgebraEquivBrauerQuotient :
    BrauerQuotientAlgebra (k := k) (P := P) (A := A) ≃ₗ[k]
      BrauerQuotient
        (algebraActionRepresentation
          (k := k) (P := P) (A := A)) :=
  (Submodule.Quotient.restrictScalarsEquiv k
      (brauerTraceIdeal
        (k := k) (P := P) (A := A))).symm.trans
    (Submodule.quotEquivOfEq
      (brauerTraceIdealAsSubmodule
        (k := k) (P := P) (A := A))
      (brauerTraceSubmodule
        (algebraActionRepresentation
          (k := k) (P := P) (A := A)))
      (brauerTraceIdealSubmodule_eq_brauerTraceSubmodule
        (k := k) (P := P) (A := A)))

/-- A fixed-algebra element, explicitly packaged as an invariant vector
of the algebra-action representation. -/
def toAlgebraActionInvariant
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    invariants
      (algebraActionRepresentation
        (k := k) (P := P) (A := A)) :=
  ⟨x, x.property⟩

/-- The quotient comparison carries the algebra projection to the
linear Brauer projection. -/
@[simp]
theorem brauerQuotientAlgebraEquivBrauerQuotient_projection
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    brauerQuotientAlgebraEquivBrauerQuotient
        (k := k) (P := P) (A := A)
        (brauerAlgebraProjection
          (k := k) (P := P) (A := A) x) =
      brauerProjection
        (algebraActionRepresentation
          (k := k) (P := P) (A := A))
        (toAlgebraActionInvariant
          (k := k) (P := P) (A := A) x) := by
  rfl

/-- Transport invariant vectors along equality of representation
packages. -/
def invariantsEquivOfRepresentationEq
    {V : Type} [AddCommGroup V] [Module k V]
    {rho sigma : Representation k P V}
    (h : rho = sigma) :
    invariants rho ≃ₗ[k] invariants sigma := by
  subst sigma
  exact LinearEquiv.refl k _

/-- Transport Brauer quotients along equality of representation
packages. -/
def brauerQuotientEquivOfRepresentationEq
    {V : Type} [AddCommGroup V] [Module k V]
    {rho sigma : Representation k P V}
    (h : rho = sigma) :
    BrauerQuotient rho ≃ₗ[k] BrauerQuotient sigma := by
  subst sigma
  exact LinearEquiv.refl k _

/-- Transport along representation equality commutes with the Brauer
projection. -/
@[simp]
theorem brauerQuotientEquivOfRepresentationEq_projection
    {V : Type} [AddCommGroup V] [Module k V]
    {rho sigma : Representation k P V}
    (h : rho = sigma)
    (x : invariants rho) :
    brauerQuotientEquivOfRepresentationEq h
        (brauerProjection rho x) =
      brauerProjection sigma
        (invariantsEquivOfRepresentationEq h x) := by
  subst sigma
  rfl

/-- Indices of algebra-basis vectors fixed by the whole group. -/
abbrev FixedIndex :=
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  MulAction.fixedPoints P B.index

variable [Finite B.index]

noncomputable local instance permutationAlgebraFixedIndexFintype :
    Fintype B.FixedIndex :=
  Fintype.ofFinite B.FixedIndex

/-- A globally fixed algebra-basis vector, regarded as an element of
the fixed subalgebra. -/
def fixedBasisElement
    (i : B.FixedIndex) :
    fixedSubalgebra (k := k) (P := P) (A := A) :=
  ⟨B.basis i, fun g => by
    letI : MulAction P B.index :=
      indexMulAction (B := B)
    rw [B.smul_basis]
    apply congrArg B.basis
    have hi := i.property g
    change B.indexAction g (i : B.index) = i at hi
    exact hi⟩

omit [Finite P] [Finite B.index] in
@[simp]
theorem fixedBasisElement_coe
    (i : B.FixedIndex) :
    (B.fixedBasisElement i : A) = B.basis i :=
  rfl

/-- A fixed-algebra element, viewed as an invariant vector for the
permutation-basis representation. -/
def toPermutationInvariant
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    letI : MulAction P B.index :=
      indexMulAction (B := B)
    invariants
      (toPermutationModuleBasis (B := B)).representation := by
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  exact ⟨x, x.property⟩

/-- The quotient comparison with codomain written using the
permutation-basis representation itself.  Naming this transport keeps
the two propositionally equal representation packages from leaking
into downstream dependent types. -/
def brauerQuotientAlgebraEquivPermutationBrauerQuotient :
    letI : MulAction P B.index :=
      indexMulAction (B := B)
    BrauerQuotientAlgebra (k := k) (P := P) (A := A) ≃ₗ[k]
      BrauerQuotient
        (toPermutationModuleBasis (B := B)).representation :=
  (brauerQuotientAlgebraEquivBrauerQuotient
      (k := k) (P := P) (A := A)).trans
    (brauerQuotientEquivOfRepresentationEq
      B.toPermutationModuleBasis_representation.symm)

omit [Finite B.index] in
/-- The representation-specific quotient comparison carries the
algebra projection to the linear Brauer projection. -/
@[simp]
theorem brauerQuotientAlgebraEquivPermutationBrauerQuotient_projection
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    letI : MulAction P B.index :=
      indexMulAction (B := B)
    B.brauerQuotientAlgebraEquivPermutationBrauerQuotient
        (brauerAlgebraProjection
          (k := k) (P := P) (A := A) x) =
      brauerProjection
        (toPermutationModuleBasis (B := B)).representation
        (B.toPermutationInvariant x) := by
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  rw [brauerQuotientAlgebraEquivPermutationBrauerQuotient,
    LinearEquiv.trans_apply,
    brauerQuotientAlgebraEquivBrauerQuotient_projection,
    brauerQuotientEquivOfRepresentationEq_projection]
  congr 1

/-- Basis of the algebra Brauer quotient indexed by the globally fixed
vectors in the pointed permutation basis. -/
def brauerQuotientAlgebraFixedBasis
    (hP : IsPGroup p P) :
    Module.Basis B.FixedIndex k
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) := by
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  exact
    ((toPermutationModuleBasis (B := B)).brauerQuotientFixedBasis hP).map
      B.brauerQuotientAlgebraEquivPermutationBrauerQuotient.symm

/-- A basis vector in the algebra Brauer quotient is the image of the
corresponding globally fixed algebra-basis vector. -/
@[simp]
theorem brauerQuotientAlgebraFixedBasis_apply
    (hP : IsPGroup p P)
    (i : B.FixedIndex) :
    B.brauerQuotientAlgebraFixedBasis hP i =
      brauerAlgebraProjection
        (k := k) (P := P) (A := A)
        (B.fixedBasisElement i) := by
  apply
    B.brauerQuotientAlgebraEquivPermutationBrauerQuotient.injective
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  change
    B.brauerQuotientAlgebraEquivPermutationBrauerQuotient
        (B.brauerQuotientAlgebraEquivPermutationBrauerQuotient.symm
          ((toPermutationModuleBasis
            (B := B)).brauerQuotientFixedBasis hP i)) =
      _
  rw [LinearEquiv.apply_symm_apply]
  rw [PermutationModuleBasis.brauerQuotientFixedBasis_apply]
  rw [B.brauerQuotientAlgebraEquivPermutationBrauerQuotient_projection]
  rfl

/-- Dimension form of the permutation-algebra Brauer quotient
theorem. -/
theorem finrank_brauerQuotientAlgebra_eq_card_fixedIndex
    (hP : IsPGroup p P) :
    Module.finrank k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      Fintype.card B.FixedIndex :=
  Module.finrank_eq_card_basis
    (B.brauerQuotientAlgebraFixedBasis hP)

end PointedPermutationAlgebraBasis
end Representation
