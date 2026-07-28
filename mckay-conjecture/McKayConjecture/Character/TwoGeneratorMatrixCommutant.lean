/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismFinrankSimplicity
import McKayConjecture.Character.SimpleCharacterRowCertificate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/-!
# Simplicity from a two-generator scalar commutant

This file turns a concrete common-commutant calculation for two matrices into
categorical simplicity of the corresponding finite-group representation.  The
matrix statement is transported through `LinearMap.toMatrix'`; no matrix
calculation is treated as an assertion about intertwiners without that
transport.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture

namespace Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {R : Type} [CommRing R] [NoZeroDivisors R]

/-- An off-diagonal entry of a matrix commuting with a diagonal matrix
vanishes when the corresponding diagonal entries are distinct. -/
theorem entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    (X : Matrix ι ι R) (diagonalEntry : ι → R)
    (commutes :
      X * Matrix.diagonal diagonalEntry =
        Matrix.diagonal diagonalEntry * X)
    (i j : ι)
    (distinct : diagonalEntry j ≠ diagonalEntry i) :
    X i j = 0 := by
  have hentry := congrFun (congrFun commutes i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hproduct :
      X i j * (diagonalEntry j - diagonalEntry i) = 0 := by
    linear_combination hentry
  exact (mul_eq_zero.mp hproduct).resolve_right
    (sub_ne_zero.mpr distinct)

/-- A convenient three-dimensional scalar-commutant criterion.  A checked
eigenbasis for the second matrix makes every common-commutant element
diagonal; two nonzero entries in the zeroth row of the transformed first
matrix connect the other two eigenspaces to the zeroth one. -/
theorem scalar_commutant_of_three_eigenvalues
    {K : Type} [Field K]
    (matrixA matrixB eigenbasis eigenbasisInverse :
      Matrix (Fin 3) (Fin 3) K)
    (eigenvalue : Fin 3 → K)
    (inverse_mul_eigenbasis :
      eigenbasisInverse * eigenbasis = 1)
    (eigenbasis_mul_inverse :
      eigenbasis * eigenbasisInverse = 1)
    (matrixB_mul_eigenbasis :
      matrixB * eigenbasis =
        eigenbasis * Matrix.diagonal eigenvalue)
    (eigenvalue_injective : Function.Injective eigenvalue)
    (transformedA_entry01_ne :
      (eigenbasisInverse * matrixA * eigenbasis) 0 1 ≠ 0)
    (transformedA_entry02_ne :
      (eigenbasisInverse * matrixA * eigenbasis) 0 2 ≠ 0) :
    ∀ X : Matrix (Fin 3) (Fin 3) K,
      X * matrixA = matrixA * X →
      X * matrixB = matrixB * X →
      ∃ c : K, X = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  intro X commutesA commutesB
  let diagonalMatrix : Matrix (Fin 3) (Fin 3) K :=
    Matrix.diagonal eigenvalue
  let transformedA : Matrix (Fin 3) (Fin 3) K :=
    eigenbasisInverse * matrixA * eigenbasis
  let Y : Matrix (Fin 3) (Fin 3) K :=
    eigenbasisInverse * X * eigenbasis
  have hQB :
      eigenbasisInverse * matrixB =
        diagonalMatrix * eigenbasisInverse := by
    calc
      eigenbasisInverse * matrixB =
          eigenbasisInverse * matrixB *
            (eigenbasis * eigenbasisInverse) := by
        rw [eigenbasis_mul_inverse, mul_one]
      _ = eigenbasisInverse *
          (matrixB * eigenbasis) * eigenbasisInverse := by
        noncomm_ring
      _ = eigenbasisInverse *
          (eigenbasis * diagonalMatrix) *
            eigenbasisInverse := by
        rw [matrixB_mul_eigenbasis]
      _ = (eigenbasisInverse * eigenbasis) *
          diagonalMatrix * eigenbasisInverse := by
        noncomm_ring
      _ = diagonalMatrix * eigenbasisInverse := by
        rw [inverse_mul_eigenbasis, one_mul]
  have commutesDiagonal :
      Y * diagonalMatrix = diagonalMatrix * Y := by
    calc
      Y * diagonalMatrix =
          eigenbasisInverse * X *
            (eigenbasis * diagonalMatrix) := by
        simp [Y, mul_assoc]
      _ = eigenbasisInverse * X *
          (matrixB * eigenbasis) := by
        rw [matrixB_mul_eigenbasis]
      _ = eigenbasisInverse *
          (X * matrixB) * eigenbasis := by
        noncomm_ring
      _ = eigenbasisInverse *
          (matrixB * X) * eigenbasis := by
        rw [commutesB]
      _ = (eigenbasisInverse * matrixB) *
          X * eigenbasis := by
        noncomm_ring
      _ = (diagonalMatrix * eigenbasisInverse) *
          X * eigenbasis := by
        rw [hQB]
      _ = diagonalMatrix * Y := by
        simp [Y, mul_assoc]
  have commutesTransformedA :
      Y * transformedA = transformedA * Y := by
    calc
      Y * transformedA =
          (eigenbasisInverse * X * eigenbasis) *
            (eigenbasisInverse * matrixA * eigenbasis) := by
        rfl
      _ = eigenbasisInverse * X *
          (eigenbasis * eigenbasisInverse) *
            matrixA * eigenbasis := by
        noncomm_ring
      _ = eigenbasisInverse * X * matrixA * eigenbasis := by
        rw [eigenbasis_mul_inverse, mul_one]
      _ = eigenbasisInverse *
          (X * matrixA) * eigenbasis := by
        noncomm_ring
      _ = eigenbasisInverse *
          (matrixA * X) * eigenbasis := by
        rw [commutesA]
      _ = eigenbasisInverse * matrixA * X * eigenbasis := by
        noncomm_ring
      _ = eigenbasisInverse * matrixA *
          (eigenbasis * eigenbasisInverse) *
            X * eigenbasis := by
        rw [eigenbasis_mul_inverse, mul_one]
      _ = (eigenbasisInverse * matrixA * eigenbasis) *
          (eigenbasisInverse * X * eigenbasis) := by
        noncomm_ring
      _ = transformedA * Y := by
        rfl
  have offDiagonal
      (i j : Fin 3) (hij : i ≠ j) :
      Y i j = 0 := by
    apply entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
      Y eigenvalue
    · exact commutesDiagonal
    · intro heq
      exact hij (eigenvalue_injective heq.symm)
  have hY01 : Y 0 1 = 0 := offDiagonal 0 1 (by decide)
  have hY02 : Y 0 2 = 0 := offDiagonal 0 2 (by decide)
  have hY10 : Y 1 0 = 0 := offDiagonal 1 0 (by decide)
  have hY12 : Y 1 2 = 0 := offDiagonal 1 2 (by decide)
  have hY20 : Y 2 0 = 0 := offDiagonal 2 0 (by decide)
  have hY21 : Y 2 1 = 0 := offDiagonal 2 1 (by decide)
  have hdiag01 : Y 0 0 = Y 1 1 := by
    have hentry :=
      congrFun (congrFun commutesTransformedA
        (0 : Fin 3)) (1 : Fin 3)
    rw [Matrix.mul_apply, Matrix.mul_apply] at hentry
    simp only [Fin.sum_univ_succ] at hentry
    norm_num at hentry
    simp only [hY01, hY02, hY21, zero_mul, mul_zero,
      add_zero, zero_add] at hentry
    have hfactor :
        (Y 0 0 - Y 1 1) * transformedA 0 1 = 0 := by
      linear_combination hentry
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hfactor).resolve_right
        (by simpa [transformedA] using transformedA_entry01_ne))
  have hdiag02 : Y 0 0 = Y 2 2 := by
    have hentry :=
      congrFun (congrFun commutesTransformedA
        (0 : Fin 3)) (2 : Fin 3)
    rw [Matrix.mul_apply, Matrix.mul_apply] at hentry
    simp only [Fin.sum_univ_succ] at hentry
    norm_num at hentry
    simp only [hY01, hY02, hY12, zero_mul, mul_zero,
      add_zero, zero_add] at hentry
    have hfactor :
        (Y 0 0 - Y 2 2) * transformedA 0 2 = 0 := by
      linear_combination hentry
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hfactor).resolve_right
        (by simpa [transformedA] using transformedA_entry02_ne))
  have hdiag12 : Y 1 1 = Y 2 2 :=
    hdiag01.symm.trans hdiag02
  have hYscalar :
      Y = Y 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [hY01, hY02, hY10, hY12, hY20, hY21,
        hdiag01, hdiag12]
  have recoverX :
      X = eigenbasis * Y * eigenbasisInverse := by
    calc
      X = 1 * X * 1 := by simp
      _ = (eigenbasis * eigenbasisInverse) * X *
          (eigenbasis * eigenbasisInverse) := by
        rw [eigenbasis_mul_inverse]
      _ = eigenbasis *
          (eigenbasisInverse * X * eigenbasis) *
            eigenbasisInverse := by
        noncomm_ring
      _ = eigenbasis * Y * eigenbasisInverse := by rfl
  refine ⟨Y 0 0, ?_⟩
  rw [recoverX, hYscalar]
  simp [eigenbasis_mul_inverse]

end Matrix

namespace FDRep

variable {G : Type u} [Finite G] [Group G]
variable {ι : Type} [Finite ι] [Nonempty ι]

/-- If the only linear endomorphisms commuting with two represented group
elements are scalars, the representation is simple. -/
theorem simple_of_two_generator_scalar_commutant
    (ρ : Representation ℂ G (ι → ℂ))
    (generatorA generatorB : G)
    (scalar_commutant :
      ∀ f : Module.End ℂ (ι → ℂ),
        Commute f (ρ generatorA) →
        Commute f (ρ generatorB) →
        ∃ c : ℂ, f = c • LinearMap.id) :
    Simple (FDRep.of ρ) := by
  let V : FDRep ℂ G := FDRep.of ρ
  let homEquiv :=
    (FDRep.forget₂HomLinearEquiv V V).symm |>.trans
      (Rep.homLinearEquiv _ _)
  have hid :
      Representation.IntertwiningMap.id ρ ≠ 0 := by
    let i : ι := Classical.choice inferInstance
    let v : ι → ℂ := fun _ ↦ 1
    have hv : v ≠ 0 := by
      intro hv0
      have hi := congrFun hv0 i
      simp [v] at hi
    intro heq
    have happ :=
      congrArg
        (fun f : Representation.IntertwiningMap ρ ρ ↦ f v)
        heq
    exact hv (by simpa using happ)
  have hintertwining :
      Module.finrank ℂ
          (Representation.IntertwiningMap ρ ρ) =
        1 := by
    apply finrank_eq_one
      (Representation.IntertwiningMap.id ρ) hid
    intro f
    have hcommA : Commute f.toLinearMap (ρ generatorA) := by
      change
        f.toLinearMap.comp (ρ generatorA) =
          (ρ generatorA).comp f.toLinearMap
      exact f.isIntertwining' generatorA
    have hcommB : Commute f.toLinearMap (ρ generatorB) := by
      change
        f.toLinearMap.comp (ρ generatorB) =
          (ρ generatorB).comp f.toLinearMap
      exact f.isIntertwining' generatorB
    obtain ⟨c, hc⟩ :=
      scalar_commutant f.toLinearMap hcommA hcommB
    refine ⟨c, ?_⟩
    apply Representation.IntertwiningMap.ext
    change c • LinearMap.id = f.toLinearMap
    exact hc.symm
  apply simple_of_end_finrank_eq_one V
  calc
    Module.finrank ℂ (V ⟶ V) =
        Module.finrank ℂ
          (Representation.IntertwiningMap V.ρ V.ρ) :=
      homEquiv.finrank_eq
    _ = Module.finrank ℂ
          (Representation.IntertwiningMap ρ ρ) := by
      rfl
    _ = 1 := hintertwining

/-- Matrix form of `simple_of_two_generator_scalar_commutant`.  The two
displayed matrices are required to be the matrices of the represented
generators in the standard coordinate basis. -/
theorem simple_of_two_generator_matrix_scalar_commutant
    [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ G (ι → ℂ))
    (generatorA generatorB : G)
    (matrixA matrixB : Matrix ι ι ℂ)
    (representation_generatorA :
      ρ generatorA = Matrix.toLin' matrixA)
    (representation_generatorB :
      ρ generatorB = Matrix.toLin' matrixB)
    (scalar_commutant :
      ∀ X : Matrix ι ι ℂ,
        X * matrixA = matrixA * X →
        X * matrixB = matrixB * X →
        ∃ c : ℂ, X = c • (1 : Matrix ι ι ℂ)) :
    Simple (FDRep.of ρ) := by
  apply simple_of_two_generator_scalar_commutant
    ρ generatorA generatorB
  intro f hcommA hcommB
  let X : Matrix ι ι ℂ := LinearMap.toMatrix' f
  have hmatrixA : X * matrixA = matrixA * X := by
    have h := congrArg LinearMap.toMatrix' hcommA.eq
    simpa only [X, representation_generatorA,
      LinearMap.toMatrix'_mul,
      LinearMap.toMatrix'_toLin'] using h
  have hmatrixB : X * matrixB = matrixB * X := by
    have h := congrArg LinearMap.toMatrix' hcommB.eq
    simpa only [X, representation_generatorB,
      LinearMap.toMatrix'_mul,
      LinearMap.toMatrix'_toLin'] using h
  obtain ⟨c, hc⟩ :=
    scalar_commutant X hmatrixA hmatrixB
  refine ⟨c, LinearMap.toMatrix'.injective ?_⟩
  simpa only [map_smul, LinearMap.toMatrix'_id] using hc

end FDRep

namespace CharacterRowCertificate

variable {G : Type} [Finite G] [Group G]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Package a two-generator matrix commutant proof directly as a normalized
character-row certificate. -/
def ofTwoGeneratorMatrixScalarCommutant
    (ρ : Representation ℂ G (ι → ℂ))
    (generatorA generatorB : G)
    (matrixA matrixB : Matrix ι ι ℂ)
    (representation_generatorA :
      ρ generatorA = Matrix.toLin' matrixA)
    (representation_generatorB :
      ρ generatorB = Matrix.toLin' matrixB)
    (scalar_commutant :
      ∀ X : Matrix ι ι ℂ,
        X * matrixA = matrixA * X →
        X * matrixB = matrixB * X →
        ∃ c : ℂ, X = c • (1 : Matrix ι ι ℂ)) :
    CharacterRowCertificate G := by
  letI : Simple (FDRep.of ρ) :=
    FDRep.simple_of_two_generator_matrix_scalar_commutant
      ρ generatorA generatorB matrixA matrixB
      representation_generatorA representation_generatorB
      scalar_commutant
  exact ofSimple (FDRep.of ρ)

end CharacterRowCertificate
end McKayConjecture
