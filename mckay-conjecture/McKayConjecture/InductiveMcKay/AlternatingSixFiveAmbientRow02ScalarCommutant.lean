/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import McKayConjecture.Character.TwoGeneratorMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientRow02CommutantGenerator

/-!
# Scalar common commutant for ambient row 02

The second generator has three distinct eigenvalues in the explicitly
checked basis.  Thus a commuting matrix is diagonal in that basis.  The two
checked nonzero entries of the transformed first generator force its three
diagonal entries to agree.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "P" => alternatingSixFiveAmbientRow02Eigenbasis
local notation "Q" => alternatingSixFiveAmbientRow02EigenbasisInverse
local notation "A" => alternatingSixFiveAmbient_row02_matrixA
local notation "B" => alternatingSixFiveAmbient_row02_matrixB
local notation "D" => alternatingSixFiveAmbientRow02GeneratorBDiagonal
local notation "A'" => alternatingSixFiveAmbientRow02TransformedGeneratorA

/-- The displayed diagonal entries are pairwise distinct. -/
theorem alternatingSixFiveAmbientRow02GeneratorBEigenvalue_injective :
    Function.Injective
      alternatingSixFiveAmbientRow02GeneratorBEigenvalue := by
  simpa [alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
    alternatingSixDegreeThreeGeneratorBEigenvalue] using
    alternatingSixDegreeThreeGeneratorBEigenvalue_injective

/-- Every matrix commuting with both row 02 presentation generators is
scalar. -/
theorem alternatingSixFiveAmbientRow02_scalar_commutant
    (X : Matrix (Fin 3) (Fin 3) ℂ)
    (commutesA : X * A = A * X)
    (commutesB : X * B = B * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.scalar_commutant_of_three_eigenvalues
    A B P Q alternatingSixFiveAmbientRow02GeneratorBEigenvalue
    alternatingSixFiveAmbientRow02EigenbasisInverse_mul
    alternatingSixFiveAmbientRow02Eigenbasis_mul_inverse
    alternatingSixFiveAmbientRow02GeneratorB_mul_eigenbasis
    alternatingSixFiveAmbientRow02GeneratorBEigenvalue_injective
  · change A' 0 1 ≠ 0
    rw [alternatingSixFiveAmbientRow02TransformedGeneratorA_entry01]
    exact
      alternatingSixFiveAmbientRow02TransformedGeneratorA01_ne_zero
  · change A' 0 2 ≠ 0
    rw [alternatingSixFiveAmbientRow02TransformedGeneratorA_entry02]
    exact
      alternatingSixFiveAmbientRow02TransformedGeneratorA02_ne_zero
  · exact commutesA
  · exact commutesB

end InductiveMcKay
end McKayConjecture
