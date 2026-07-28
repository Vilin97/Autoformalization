/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixThreeNormalizerDegreeFourRepresentations
import McKayConjecture.Character.TwoGeneratorMatrixCommutant

/-!
# Irreducibility of the four degree-four normalizer rows

The diagonal image of one Heisenberg generator and the signed cyclic
shift have scalar common commutant.  Schur's lemma and Maschke
semisimplicity then certify all four monomial representations as simple.
-/

noncomputable section

open CategoryTheory Matrix

namespace McKayConjecture
namespace AlternatingSixThreeNormalizer

open GroupTheory

/-- A noncentral Heisenberg generator used in the commutant
calculation. -/
def degreeFourHeisenbergGenerator :
    AlternatingSixThreeHeisenbergCoordinates :=
  ⟨0, 1, 0⟩

/-- The generator of the cyclic factor. -/
def degreeFourCyclicGenerator :
    AlternatingSixThreeCyclicEight :=
  Multiplicative.ofAdd (1 : ZMod 8)

/-- The two selected elements of the full semidirect product. -/
def degreeFourNormalizerGeneratorA :
    AlternatingSixThreeNormalizerCoordinates :=
  SemidirectProduct.inl degreeFourHeisenbergGenerator

def degreeFourNormalizerGeneratorB :
    AlternatingSixThreeNormalizerCoordinates :=
  SemidirectProduct.inr degreeFourCyclicGenerator

theorem threePhase_injective :
    Function.Injective threePhase :=
  ZMod.injective_stdAddChar

/-- The two displayed matrices are the represented matrices of the two
selected group elements. -/
theorem degreeFourRepresentation_generatorA
    (orbit extension : Fin 2) :
    degreeFourRepresentation orbit extension
        degreeFourNormalizerGeneratorA =
      Matrix.toLin'
        (degreeFourDiagonalMatrix orbit
          degreeFourHeisenbergGenerator) := by
  rw [degreeFourRepresentation_apply]
  congr 1
  change
    ((degreeFourGLHom orbit extension
        (SemidirectProduct.inl degreeFourHeisenbergGenerator) :
          Matrix.GeneralLinearGroup (Fin 4) ℂ) :
      Matrix (Fin 4) (Fin 4) ℂ) =
      degreeFourDiagonalMatrix orbit degreeFourHeisenbergGenerator
  rw [degreeFourGLHom, SemidirectProduct.lift_inl]
  rfl

theorem degreeFourRepresentation_generatorB
    (orbit extension : Fin 2) :
    degreeFourRepresentation orbit extension
        degreeFourNormalizerGeneratorB =
      Matrix.toLin' (degreeFourShiftMatrix extension) := by
  rw [degreeFourRepresentation_apply]
  congr 1
  change
    ((degreeFourGLHom orbit extension
        (SemidirectProduct.inr degreeFourCyclicGenerator) :
          Matrix.GeneralLinearGroup (Fin 4) ℂ) :
      Matrix (Fin 4) (Fin 4) ℂ) =
      degreeFourShiftMatrix extension
  rw [degreeFourGLHom, SemidirectProduct.lift_inr]
  have hshift :
      QuaternionGroup.zmodPower
        (degreeFourShiftGL extension)
        (degreeFourShiftGL_pow_eight extension)
        (1 : ZMod 8) =
      degreeFourShiftGL extension := by
    rw [show (1 : ZMod 8) = ((1 : ℕ) : ZMod 8) by rfl,
      QuaternionGroup.zmodPower_natCast]
    simp
  exact congrArg
    (fun u : Matrix.GeneralLinearGroup (Fin 4) ℂ =>
      (u : Matrix (Fin 4) (Fin 4) ℂ)) hshift

/-- Scalar common commutant for the axis-orbit diagonal and the cyclic
shift. -/
theorem degreeFourAxis_scalar_commutant
    (extension : Fin 2)
    (X : Matrix (Fin 4) (Fin 4) ℂ)
    (hA :
      X * degreeFourDiagonalMatrix 0 degreeFourHeisenbergGenerator =
        degreeFourDiagonalMatrix 0 degreeFourHeisenbergGenerator * X)
    (hB :
      X * degreeFourShiftMatrix extension =
        degreeFourShiftMatrix extension * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  let d : Fin 4 → ℂ :=
    fun i =>
      threePhase
        (degreeFourExponent 0 i degreeFourHeisenbergGenerator)
  have hdiag :
      X * Matrix.diagonal d = Matrix.diagonal d * X := by
    exact hA
  have off
      (i j : Fin 4)
      (hij :
        degreeFourExponent 0 j degreeFourHeisenbergGenerator ≠
          degreeFourExponent 0 i degreeFourHeisenbergGenerator) :
      X i j = 0 := by
    apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
      X d hdiag i j
    intro hphase
    exact hij (threePhase_injective hphase)
  have h01 : X 0 1 = 0 := off 0 1 (by decide)
  have h02 : X 0 2 = 0 := off 0 2 (by decide)
  have h03 : X 0 3 = 0 := off 0 3 (by decide)
  have h10 : X 1 0 = 0 := off 1 0 (by decide)
  have h12 : X 1 2 = 0 := off 1 2 (by decide)
  have h20 : X 2 0 = 0 := off 2 0 (by decide)
  have h21 : X 2 1 = 0 := off 2 1 (by decide)
  have h23 : X 2 3 = 0 := off 2 3 (by decide)
  have h30 : X 3 0 = 0 := off 3 0 (by decide)
  have h32 : X 3 2 = 0 := off 3 2 (by decide)
  have h13 : X 1 3 = 0 := by
    have h := congrFun (congrFun hB (1 : Fin 4)) (2 : Fin 4)
    simp [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, h02] at h
    exact h
  have h31 : X 3 1 = 0 := by
    have h := congrFun (congrFun hB (3 : Fin 4)) (0 : Fin 4)
    simp [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, h20] at h
    exact h
  have hdiag01 : X 0 0 = X 1 1 := by
    have h := congrFun (congrFun hB (1 : Fin 4)) (0 : Fin 4)
    simpa [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] using h.symm
  have hdiag12 : X 1 1 = X 2 2 := by
    have h := congrFun (congrFun hB (2 : Fin 4)) (1 : Fin 4)
    simpa [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] using h.symm
  have hdiag23 : X 2 2 = X 3 3 := by
    have h := congrFun (congrFun hB (3 : Fin 4)) (2 : Fin 4)
    simpa [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] using h.symm
  refine ⟨X 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h01, h02, h03, h10, h12, h13, h20, h21,
      h23, h30, h31, h32, hdiag01, hdiag12, hdiag23]

/-- Scalar common commutant for the diagonal-orbit matrix and the
cyclic shift. -/
theorem degreeFourDiagonalOrbit_scalar_commutant
    (extension : Fin 2)
    (X : Matrix (Fin 4) (Fin 4) ℂ)
    (hA :
      X * degreeFourDiagonalMatrix 1 degreeFourHeisenbergGenerator =
        degreeFourDiagonalMatrix 1 degreeFourHeisenbergGenerator * X)
    (hB :
      X * degreeFourShiftMatrix extension =
        degreeFourShiftMatrix extension * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  let d : Fin 4 → ℂ :=
    fun i =>
      threePhase
        (degreeFourExponent 1 i degreeFourHeisenbergGenerator)
  have hdiag :
      X * Matrix.diagonal d = Matrix.diagonal d * X := by
    exact hA
  have off
      (i j : Fin 4)
      (hij :
        degreeFourExponent 1 j degreeFourHeisenbergGenerator ≠
          degreeFourExponent 1 i degreeFourHeisenbergGenerator) :
      X i j = 0 := by
    apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
      X d hdiag i j
    intro hphase
    exact hij (threePhase_injective hphase)
  have h01 : X 0 1 = 0 := off 0 1 (by decide)
  have h02 : X 0 2 = 0 := off 0 2 (by decide)
  have h10 : X 1 0 = 0 := off 1 0 (by decide)
  have h13 : X 1 3 = 0 := off 1 3 (by decide)
  have h20 : X 2 0 = 0 := off 2 0 (by decide)
  have h23 : X 2 3 = 0 := off 2 3 (by decide)
  have h31 : X 3 1 = 0 := off 3 1 (by decide)
  have h32 : X 3 2 = 0 := off 3 2 (by decide)
  have h03 : X 0 3 = 0 := by
    have h := congrFun (congrFun hB (0 : Fin 4)) (2 : Fin 4)
    simp [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, h32] at h
    exact h
  have h30 : X 3 0 = 0 := by
    have h := congrFun (congrFun hB (3 : Fin 4)) (3 : Fin 4)
    simp [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, h23] at h
    exact h.resolve_right (degreeFourSign_ne_zero extension)
  have h12 : X 1 2 = 0 := by
    have h := congrFun (congrFun hB (1 : Fin 4)) (1 : Fin 4)
    simp [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, h01] at h
    exact h
  have h21 : X 2 1 = 0 := by
    have h := congrFun (congrFun hB (2 : Fin 4)) (0 : Fin 4)
    simp [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, h10] at h
    exact h
  have hdiag01 : X 0 0 = X 1 1 := by
    have h := congrFun (congrFun hB (1 : Fin 4)) (0 : Fin 4)
    simpa [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] using h.symm
  have hdiag12 : X 1 1 = X 2 2 := by
    have h := congrFun (congrFun hB (2 : Fin 4)) (1 : Fin 4)
    simpa [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] using h.symm
  have hdiag23 : X 2 2 = X 3 3 := by
    have h := congrFun (congrFun hB (3 : Fin 4)) (2 : Fin 4)
    simpa [degreeFourShiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] using h.symm
  refine ⟨X 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h01, h02, h03, h10, h12, h13, h20, h21,
      h23, h30, h31, h32, hdiag01, hdiag12, hdiag23]

/-- Uniform scalar-commutant statement for both dual orbits. -/
theorem degreeFour_scalar_commutant
    (orbit extension : Fin 2)
    (X : Matrix (Fin 4) (Fin 4) ℂ)
    (hA :
      X * degreeFourDiagonalMatrix orbit degreeFourHeisenbergGenerator =
        degreeFourDiagonalMatrix orbit degreeFourHeisenbergGenerator * X)
    (hB :
      X * degreeFourShiftMatrix extension =
        degreeFourShiftMatrix extension * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  fin_cases orbit
  · exact degreeFourAxis_scalar_commutant extension X hA hB
  · exact degreeFourDiagonalOrbit_scalar_commutant extension X hA hB

/-- Every one of the four monomial representations is simple. -/
theorem degreeFourFDRep_simple
    (orbit extension : Fin 2) :
    Simple (degreeFourFDRep orbit extension) := by
  exact
    FDRep.simple_of_two_generator_matrix_scalar_commutant
      (degreeFourRepresentation orbit extension)
      degreeFourNormalizerGeneratorA
      degreeFourNormalizerGeneratorB
      (degreeFourDiagonalMatrix orbit degreeFourHeisenbergGenerator)
      (degreeFourShiftMatrix extension)
      (degreeFourRepresentation_generatorA orbit extension)
      (degreeFourRepresentation_generatorB orbit extension)
      (degreeFour_scalar_commutant orbit extension)

/-- The four explicit irreducible characters. -/
def degreeFourCharacter
    (orbit extension : Fin 2) :
    IrreducibleCharacter AlternatingSixThreeNormalizerCoordinates := by
  letI : Simple (degreeFourFDRep orbit extension) :=
    degreeFourFDRep_simple orbit extension
  exact IrreducibleCharacter.ofSimple (degreeFourFDRep orbit extension)

@[simp]
theorem degreeFourCharacter_degree
    (orbit extension : Fin 2) :
    (degreeFourCharacter orbit extension).degree = 4 := by
  change Module.finrank ℂ (degreeFourFDRep orbit extension) = 4
  exact degreeFourFDRep_finrank orbit extension

end AlternatingSixThreeNormalizer
end McKayConjecture
