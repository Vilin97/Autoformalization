/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Central simple algebras over finite fields split

Wedderburn--Artin writes a finite-dimensional simple algebra as a
matrix algebra over a finite-dimensional division algebra.  Over a
finite base field that division algebra is finite, hence commutative
by Wedderburn's little theorem.  Centrality then forces it to equal
the base field.

This is the splitting result needed to replace an abstract Dade
algebra over a finite field by a full endomorphism algebra.
-/

noncomputable section

namespace Representation

universe u v

variable (k : Type u) (A : Type v)
variable [Field k] [Finite k]
variable [Ring A] [Algebra k A]

/-- A finite-dimensional central simple algebra over a finite field
is a matrix algebra over that field. -/
theorem exists_algEquiv_matrix_of_finiteField
    [Algebra.IsCentral k A] [IsSimpleRing A]
    [FiniteDimensional k A] :
    ∃ (n : ℕ) (_ : NeZero n),
      Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) k) := by
  letI : IsArtinianRing A :=
    IsArtinianRing.of_finite k A
  obtain ⟨n, hn, D, hDdivision, hDalgebra, hDfinite, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  letI : NeZero n := hn
  letI : DivisionRing D := hDdivision
  letI : Algebra k D := hDalgebra
  letI : Module.Finite k D := hDfinite
  letI : Finite D :=
    Module.finite_of_finite k
  have hcomm (x y : D) : x * y = y * x := by
    letI : Field D :=
      Finite.divisionRing_to_field D
    exact mul_comm x y
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv k A
      (Matrix (Fin n) (Fin n) D) e
  have hsurjective :
      Function.Surjective (algebraMap k D) := by
    intro x
    have hscalar :
        Matrix.scalar (Fin n) x ∈
          Subalgebra.center k (Matrix (Fin n) (Fin n) D) := by
      rw [Subalgebra.mem_center_iff]
      intro M
      exact
        (Matrix.scalar_commute x
          (fun y ↦ hcomm x y) M).symm
    have hbot :
        Matrix.scalar (Fin n) x ∈
          (⊥ :
            Subalgebra k (Matrix (Fin n) (Fin n) D)) :=
      Algebra.IsCentral.out hscalar
    rw [Algebra.mem_bot] at hbot
    obtain ⟨a, ha⟩ := hbot
    let i : Fin n :=
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    refine ⟨a, ?_⟩
    have hii := congrFun (congrFun ha i) i
    simpa [Matrix.scalar_apply, Matrix.algebraMap_matrix_apply] using hii
  have hmap :
      Function.Bijective (algebraMap k D) :=
    ⟨FaithfulSMul.algebraMap_injective k D, hsurjective⟩
  exact
    ⟨n, hn,
      ⟨e.trans
        (.mapMatrix
          (.symm
            (.ofBijective
              (Algebra.ofId k D) hmap)))⟩⟩

/-- Endomorphism-algebra form of finite-field central-simple
splitting. -/
theorem exists_algEquiv_endomorphism_of_finiteField
    [Algebra.IsCentral k A] [IsSimpleRing A]
    [FiniteDimensional k A] :
    ∃ (n : ℕ) (_ : NeZero n),
      Nonempty
        (A ≃ₐ[k] Module.End k (Fin n → k)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    exists_algEquiv_matrix_of_finiteField k A
  exact
    ⟨n, hn, ⟨e.trans Matrix.toLinAlgEquiv'⟩⟩

end Representation
