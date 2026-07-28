/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Basic
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverPresentation

/-!
# Representations of the `A₆` Schur-cover presentation

This file isolates the common descent argument for concrete
representations of the six-generator Schur-cover presentation.  A
certificate consists of the images of the six generators, the four
defining-relator identities, centrality of the four relator values, and
the two relation-module identities.  The certificate then descends
uniformly to the presented group.

Keeping this interface independent of matrices lets finite permutation,
matrix, and projective certificates share the same trusted descent
argument.
-/

noncomputable section

open scoped commutatorElement

namespace McKayConjecture
namespace GroupTheory

/-- Checked images of the six generators of the `A₆` Schur-cover
presentation in an arbitrary group. -/
structure AlternatingSixSchurRepresentationData
    (H : Type*) [Group H] where
  /-- Images of `a`, `b`, and the four named central relator values. -/
  generator : Fin 6 → H
  /-- The four base relators have the four advertised images. -/
  baseRelator_eq :
    ∀ i : Fin 4,
      FreeGroup.lift generator
          (alternatingSixSchurBaseRelator i) =
        generator ⟨i.val + 2, by omega⟩
  /-- Each advertised relator value is central on the chosen
  generators. -/
  centrality :
    ∀ (i : Fin 4) (j : Fin 6),
      Commute
        (generator ⟨i.val + 2, by omega⟩)
        (generator j)
  /-- The first relation-module row. -/
  lattice_one :
    generator 2 ^ 3 *
          generator 4 ^ (-2 : ℤ) *
        generator 5 = 1
  /-- The second relation-module row. -/
  lattice_two :
    generator 3 ^ 4 *
          generator 4 ^ 3 *
        generator 5 ^ (-3 : ℤ) = 1

namespace AlternatingSixSchurRepresentationData

variable {H : Type*} [Group H]

/-- Transport a checked presentation certificate along a group
homomorphism. -/
def map
    {K : Type*} [Group K]
    (d : AlternatingSixSchurRepresentationData H)
    (f : H →* K) :
    AlternatingSixSchurRepresentationData K where
  generator i := f (d.generator i)
  baseRelator_eq i := by
    have hlift
        (word : FreeGroup (Fin 6)) :
        FreeGroup.lift (fun j ↦ f (d.generator j)) word =
          f (FreeGroup.lift d.generator word) := by
      symm
      exact
        FreeGroup.lift_unique
          (f.comp (FreeGroup.lift d.generator))
          (by simp)
    rw [hlift, d.baseRelator_eq]
  centrality i j :=
    (d.centrality i j).map f
  lattice_one := by
    simpa using congrArg f d.lattice_one
  lattice_two := by
    simpa using congrArg f d.lattice_two

@[simp]
theorem map_generator
    {K : Type*} [Group K]
    (d : AlternatingSixSchurRepresentationData H)
    (f : H →* K)
    (i : Fin 6) :
    (d.map f).generator i = f (d.generator i) :=
  rfl

/-- A checked generator certificate kills every defining relator. -/
theorem kills_relators
    (d : AlternatingSixSchurRepresentationData H) :
    ∀ relator ∈ alternatingSixSchurRelators,
      FreeGroup.lift d.generator relator = 1 := by
  intro relator hrelator
  rcases hrelator with hdefinition | hrest
  · rcases hdefinition with ⟨i, rfl⟩ | ⟨index, rfl⟩
    · simp only [alternatingSixSchurDefinitionRelator,
        map_mul, map_inv]
      rw [d.baseRelator_eq i]
      simp [alternatingSixSchurFreeK,
        alternatingSixSchurGenerator]
    · rcases index with ⟨i, j⟩
      simp [alternatingSixSchurCentralityRelator,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator,
        map_commutatorElement]
      exact
        commutatorElement_eq_one_iff_commute.mpr
          (d.centrality i j)
  · rcases hrest with rfl | hsecond
    · simpa [alternatingSixSchurLatticeRelatorOne,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator] using
          d.lattice_one
    · have hsecond' :
        relator = alternatingSixSchurLatticeRelatorTwo := by
        simpa using hsecond
      subst relator
      simpa [alternatingSixSchurLatticeRelatorTwo,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator] using
          d.lattice_two

/-- The homomorphism from the presented cover supplied by a checked
generator certificate. -/
def toMonoidHom
    (d : AlternatingSixSchurRepresentationData H) :
    AlternatingSixSchurPresentedGroup →* H :=
  PresentedGroup.toGroup d.kills_relators

@[simp]
theorem toMonoidHom_generator
    (d : AlternatingSixSchurRepresentationData H)
    (i : Fin 6) :
    d.toMonoidHom (alternatingSixSchurPresentedGenerator i) =
      d.generator i := by
  simp [toMonoidHom, alternatingSixSchurPresentedGenerator]

@[simp]
theorem toMonoidHom_a
    (d : AlternatingSixSchurRepresentationData H) :
    d.toMonoidHom alternatingSixSchurPresentedA =
      d.generator 0 := by
  simp [alternatingSixSchurPresentedA]

@[simp]
theorem toMonoidHom_b
    (d : AlternatingSixSchurRepresentationData H) :
    d.toMonoidHom alternatingSixSchurPresentedB =
      d.generator 1 := by
  simp [alternatingSixSchurPresentedB]

@[simp]
theorem toMonoidHom_k
    (d : AlternatingSixSchurRepresentationData H)
    (i : Fin 4) :
    d.toMonoidHom (alternatingSixSchurPresentedK i) =
      d.generator ⟨i.val + 2, by omega⟩ := by
  simp [alternatingSixSchurPresentedK]

/-- A matrix-valued Schur-cover certificate, regarded as a linear
representation on coordinate vectors. -/
def toMatrixRepresentation
    {R n : Type*}
    [CommRing R] [Fintype n] [DecidableEq n]
    (d :
      AlternatingSixSchurRepresentationData
        (Matrix.GeneralLinearGroup n R)) :
    Representation R AlternatingSixSchurPresentedGroup (n → R) :=
  (Units.coeHom ((n → R) →ₗ[R] (n → R))).comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      d.toMonoidHom)

end AlternatingSixSchurRepresentationData

/-- Package a matrix of finite positive order as an element of the
general linear group.  This avoids a separate determinant calculation in
finite matrix certificates. -/
def matrixGeneralLinearOfPowEqOne
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (m : ℕ)
    (hm : m ≠ 0) (hA : A ^ m = 1) :
    Matrix.GeneralLinearGroup n R :=
  { val := A
    inv := A ^ (m - 1)
    val_inv := by
      calc
        A * A ^ (m - 1) =
            A ^ ((m - 1) + 1) := by
              rw [pow_succ']
        _ = A ^ m := by
              congr 1
              omega
        _ = 1 := hA
    inv_val := by
      calc
        A ^ (m - 1) * A =
            A ^ ((m - 1) + 1) := by
              rw [pow_succ]
        _ = A ^ m := by
              congr 1
              omega
        _ = 1 := hA }

@[simp]
theorem matrixGeneralLinearOfPowEqOne_val
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (m : ℕ)
    (hm : m ≠ 0) (hA : A ^ m = 1) :
    ((matrixGeneralLinearOfPowEqOne A m hm hA :
        Matrix.GeneralLinearGroup n R) :
      Matrix n n R) =
      A :=
  rfl

end GroupTheory
end McKayConjecture
