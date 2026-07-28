/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverEnumeration
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverRepresentation

/-!
# Matrix certificates for representations of the sixfold cover of `A₆`

This file is the small trusted bridge between exact generator-matrix
calculations and honest representations of the canonical universal cover.
A row certificate records the four scalar presentation relations and the two
relation-module identities.  The matrices are then proved invertible, packaged
in `GL`, descended through the presentation, and transported to the canonical
free-presentation universal cover.

The interface is independent of a particular character table.  In particular,
generated relation files can be consumed one row at a time without duplicating
the presentation descent argument.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Exact matrix input for one representation row of the sixfold-cover
presentation.

The four scalars are the images of `a²`, `b⁴`, `(ab)⁵`, and `(ab²)⁵`.
Their 120th-power identities both certify invertibility of the generator
matrices and cover every cyclotomic specialization used by the ambient
`5'`-table. -/
structure AlternatingSixSchurMatrixRowCertificate
    (n : Type) [Fintype n] [DecidableEq n] where
  /-- Image of the first noncentral presentation generator. -/
  matrixA : Matrix n n ℂ
  /-- Image of the second noncentral presentation generator. -/
  matrixB : Matrix n n ℂ
  /-- Scalar values of the four named central relators. -/
  relatorScalar : Fin 4 → ℂ
  /-- Every relator scalar is a 120th root of unity. -/
  relatorScalar_pow_one :
    ∀ i : Fin 4, relatorScalar i ^ 120 = 1
  /-- The first generator has the prescribed central square. -/
  matrixA_sq :
    matrixA ^ 2 =
      relatorScalar 0 • (1 : Matrix n n ℂ)
  /-- The second generator has the prescribed central fourth power. -/
  matrixB_fourth :
    matrixB ^ 4 =
      relatorScalar 1 • (1 : Matrix n n ℂ)
  /-- The product of the two generators has the prescribed fifth power. -/
  matrixAB_fifth :
    (matrixA * matrixB) ^ 5 =
      relatorScalar 2 • (1 : Matrix n n ℂ)
  /-- The product `a b²` has the prescribed fifth power. -/
  matrixABSquared_fifth :
    (matrixA * matrixB ^ 2) ^ 5 =
      relatorScalar 3 • (1 : Matrix n n ℂ)
  /-- The first relation-module row, on the four scalar values. -/
  lattice_one :
    relatorScalar 0 ^ 3 *
          relatorScalar 2 ^ (-2 : ℤ) *
        relatorScalar 3 =
      1
  /-- The second relation-module row, on the four scalar values. -/
  lattice_two :
    relatorScalar 1 ^ 4 *
          relatorScalar 2 ^ 3 *
        relatorScalar 3 ^ (-3 : ℤ) =
      1

namespace AlternatingSixSchurMatrixRowCertificate

variable {n : Type} [Fintype n] [DecidableEq n]

variable (C : AlternatingSixSchurMatrixRowCertificate n)

private theorem relatorScalar_ne_zero (i : Fin 4) :
    C.relatorScalar i ≠ 0 := by
  intro hi
  have h := C.relatorScalar_pow_one i
  rw [hi] at h
  norm_num at h

/-- The scalar of a named central relator, regarded as a complex unit. -/
def relatorUnit (i : Fin 4) : ℂˣ :=
  Units.mk0 (C.relatorScalar i) (C.relatorScalar_ne_zero i)

@[simp]
theorem relatorUnit_val (i : Fin 4) :
    (C.relatorUnit i : ℂ) = C.relatorScalar i :=
  rfl

private theorem scalarMatrix_pow_one (i : Fin 4) :
    (C.relatorScalar i • (1 : Matrix n n ℂ)) ^ 120 = 1 := by
  rw [← Algebra.algebraMap_eq_smul_one, ← map_pow,
    C.relatorScalar_pow_one, map_one]

/-- The first generator matrix has a finite positive power equal to one. -/
theorem matrixA_pow_twoHundredForty :
    C.matrixA ^ 240 = 1 := by
  calc
    C.matrixA ^ 240 = (C.matrixA ^ 2) ^ 120 := by
      rw [show 240 = 2 * 120 by norm_num, pow_mul]
    _ = (C.relatorScalar 0 • (1 : Matrix n n ℂ)) ^ 120 := by
      rw [C.matrixA_sq]
    _ = 1 := C.scalarMatrix_pow_one 0

/-- The second generator matrix has a finite positive power equal to one. -/
theorem matrixB_pow_fourHundredEighty :
    C.matrixB ^ 480 = 1 := by
  calc
    C.matrixB ^ 480 = (C.matrixB ^ 4) ^ 120 := by
      rw [show 480 = 4 * 120 by norm_num, pow_mul]
    _ = (C.relatorScalar 1 • (1 : Matrix n n ℂ)) ^ 120 := by
      rw [C.matrixB_fourth]
    _ = 1 := C.scalarMatrix_pow_one 1

/-- The first generator matrix, certified as an element of `GL`. -/
def matrixAGL : Matrix.GeneralLinearGroup n ℂ :=
  matrixGeneralLinearOfPowEqOne
    C.matrixA 240 (by norm_num) C.matrixA_pow_twoHundredForty

/-- The second generator matrix, certified as an element of `GL`. -/
def matrixBGL : Matrix.GeneralLinearGroup n ℂ :=
  matrixGeneralLinearOfPowEqOne
    C.matrixB 480 (by norm_num) C.matrixB_pow_fourHundredEighty

/-- A named central relator scalar, certified as an element of `GL`. -/
def relatorGL (i : Fin 4) : Matrix.GeneralLinearGroup n ℂ :=
  Matrix.GeneralLinearGroup.scalar n (C.relatorUnit i)

@[simp]
theorem matrixAGL_val :
    (C.matrixAGL : Matrix n n ℂ) = C.matrixA :=
  rfl

@[simp]
theorem matrixBGL_val :
    (C.matrixBGL : Matrix n n ℂ) = C.matrixB :=
  rfl

@[simp]
theorem relatorGL_val (i : Fin 4) :
    (C.relatorGL i : Matrix n n ℂ) =
      C.relatorScalar i • (1 : Matrix n n ℂ) := by
  change
    Matrix.scalar n (C.relatorScalar i) =
      C.relatorScalar i • (1 : Matrix n n ℂ)
  exact (Matrix.smul_one_eq_diagonal (C.relatorScalar i)).symm

/-- The four checked matrix identities hold after packaging all matrices in
`GL`. -/
theorem matrixAGL_sq :
    C.matrixAGL ^ 2 = C.relatorGL 0 := by
  apply Units.ext
  simpa using C.matrixA_sq

theorem matrixBGL_fourth :
    C.matrixBGL ^ 4 = C.relatorGL 1 := by
  apply Units.ext
  simpa using C.matrixB_fourth

theorem matrixAGL_mul_matrixBGL_fifth :
    (C.matrixAGL * C.matrixBGL) ^ 5 = C.relatorGL 2 := by
  apply Units.ext
  simpa using C.matrixAB_fifth

theorem matrixAGL_mul_matrixBGL_sq_fifth :
    (C.matrixAGL * C.matrixBGL ^ 2) ^ 5 = C.relatorGL 3 := by
  apply Units.ext
  simpa using C.matrixABSquared_fifth

private theorem relatorUnit_lattice_one :
    C.relatorUnit 0 ^ 3 *
          C.relatorUnit 2 ^ (-2 : ℤ) *
        C.relatorUnit 3 =
      1 := by
  apply Units.ext
  simpa using C.lattice_one

private theorem relatorUnit_lattice_two :
    C.relatorUnit 1 ^ 4 *
          C.relatorUnit 2 ^ 3 *
        C.relatorUnit 3 ^ (-3 : ℤ) =
      1 := by
  apply Units.ext
  simpa using C.lattice_two

private theorem relatorGL_lattice_one :
    C.relatorGL 0 ^ 3 *
          C.relatorGL 2 ^ (-2 : ℤ) *
        C.relatorGL 3 =
      1 := by
  simpa only [relatorGL, map_pow, map_zpow, map_mul, map_one] using
    congrArg (Matrix.GeneralLinearGroup.scalar n)
      C.relatorUnit_lattice_one

private theorem relatorGL_lattice_two :
    C.relatorGL 1 ^ 4 *
          C.relatorGL 2 ^ 3 *
        C.relatorGL 3 ^ (-3 : ℤ) =
      1 := by
  simpa only [relatorGL, map_pow, map_zpow, map_mul, map_one] using
    congrArg (Matrix.GeneralLinearGroup.scalar n)
      C.relatorUnit_lattice_two

/-- The six `GL` values assigned to the Schur-cover presentation
generators. -/
def generator :
    Fin 6 → Matrix.GeneralLinearGroup n ℂ :=
  Fin.cases C.matrixAGL
    (Fin.cases C.matrixBGL C.relatorGL)

@[simp]
theorem generator_zero :
    C.generator 0 = C.matrixAGL :=
  rfl

@[simp]
theorem generator_one :
    C.generator 1 = C.matrixBGL :=
  rfl

@[simp]
theorem generator_add_two (i : Fin 4) :
    C.generator ⟨i.val + 2, by omega⟩ = C.relatorGL i := by
  fin_cases i <;> rfl

@[simp]
theorem generator_two :
    C.generator 2 = C.relatorGL 0 := by
  simpa using C.generator_add_two 0

@[simp]
theorem generator_three :
    C.generator 3 = C.relatorGL 1 := by
  simpa using C.generator_add_two 1

@[simp]
theorem generator_four :
    C.generator 4 = C.relatorGL 2 := by
  simpa using C.generator_add_two 2

@[simp]
theorem generator_five :
    C.generator 5 = C.relatorGL 3 := by
  simpa using C.generator_add_two 3

/-- The exact matrix row, viewed as a checked representation datum for the
six-generator presentation. -/
def presentationData :
    AlternatingSixSchurRepresentationData
      (Matrix.GeneralLinearGroup n ℂ) where
  generator := C.generator
  baseRelator_eq i := by
    fin_cases i
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using C.matrixAGL_sq
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using C.matrixBGL_fourth
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          C.matrixAGL_mul_matrixBGL_fifth
    · simpa [alternatingSixSchurBaseRelator,
        alternatingSixSchurFreeA, alternatingSixSchurFreeB,
        alternatingSixSchurGenerator] using
          C.matrixAGL_mul_matrixBGL_sq_fifth
  centrality i j := by
    rw [C.generator_add_two]
    exact
      Matrix.GeneralLinearGroup.scalar_commute
        (C.relatorUnit i) (C.generator j)
  lattice_one := by
    simpa using C.relatorGL_lattice_one
  lattice_two := by
    simpa using C.relatorGL_lattice_two

/-- The `GL`-valued representation of the presented Schur cover supplied by
an exact matrix row. -/
def presentedGLRepresentation :
    AlternatingSixSchurPresentedGroup →*
      Matrix.GeneralLinearGroup n ℂ :=
  C.presentationData.toMonoidHom

/-- The exact `GL`-valued representation of the canonical universal cover
obtained by transport from the Schur presentation. -/
def universalCoverGLRepresentation :
    AlternatingSixUniversalCover →*
      Matrix.GeneralLinearGroup n ℂ :=
  C.presentedGLRepresentation.comp
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension).symm.toMonoidHom

/-- The honest complex representation of the presented Schur cover supplied
by an exact matrix row. -/
def presentedRepresentation :
    Representation ℂ AlternatingSixSchurPresentedGroup (n → ℂ) :=
  C.presentationData.toMatrixRepresentation

/-- The honest complex representation of the canonical universal cover
obtained from the exact matrix row. -/
def universalCoverRepresentation :
    Representation ℂ AlternatingSixUniversalCover (n → ℂ) :=
  C.presentedRepresentation.comp
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension).symm.toMonoidHom

@[simp]
theorem presentedRepresentation_a :
    C.presentedRepresentation alternatingSixSchurPresentedA =
      Matrix.GeneralLinearGroup.toLin C.matrixAGL := by
  simp [presentedRepresentation,
    AlternatingSixSchurRepresentationData.toMatrixRepresentation,
    presentationData]

@[simp]
theorem presentedRepresentation_b :
    C.presentedRepresentation alternatingSixSchurPresentedB =
      Matrix.GeneralLinearGroup.toLin C.matrixBGL := by
  simp [presentedRepresentation,
    AlternatingSixSchurRepresentationData.toMatrixRepresentation,
    presentationData]

end AlternatingSixSchurMatrixRowCertificate
end InductiveMcKay
end McKayConjecture
