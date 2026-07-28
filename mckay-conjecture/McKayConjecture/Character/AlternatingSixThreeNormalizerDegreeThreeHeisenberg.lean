/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixThreeNormalizerDegreeFourRepresentations
import McKayConjecture.Character.TwoGeneratorMatrixCommutant

/-!
# The two three-dimensional Heisenberg representations

The extraspecial subgroup of the three-normalizer has two nonlinear
irreducible characters, distinguished by their nontrivial central
characters.  This file realizes them as the two Schrödinger
representations on functions on `ZMod 3`.
-/

noncomputable section

open CategoryTheory Matrix

namespace McKayConjecture
namespace AlternatingSixThreeNormalizer

open GroupTheory

/-- The two nonzero central-character parameters in `ZMod 3`. -/
def degreeThreeCentralParameter (central : Fin 2) : ZMod 3 :=
  (central.val + 1 : ℕ)

theorem degreeThreeCentralParameter_ne_zero (central : Fin 2) :
    degreeThreeCentralParameter central ≠ 0 := by
  fin_cases central <;> decide

/-- The Schrödinger matrix attached to a Heisenberg coordinate.

On the basis vector indexed by `j`, the matrix sends
`e_j` to
`threePhase (k * (z + y*j)) e_(j+x)`.
-/
def degreeThreeHeisenbergMatrix
    (central : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    Matrix (ZMod 3) (ZMod 3) ℂ :=
  fun i j =>
    if i = j + p.x then
      threePhase
        (degreeThreeCentralParameter central * (p.z + p.y * j))
    else
      0

@[simp]
theorem degreeThreeHeisenbergMatrix_one (central : Fin 2) :
    degreeThreeHeisenbergMatrix central 1 = 1 := by
  change degreeThreeHeisenbergMatrix central ⟨0, 0, 0⟩ = 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [degreeThreeHeisenbergMatrix]
  · simp [degreeThreeHeisenbergMatrix, hij]

theorem degreeThreeHeisenbergMatrix_mul
    (central : Fin 2)
    (p q : AlternatingSixThreeHeisenbergCoordinates) :
    degreeThreeHeisenbergMatrix central (p * q) =
      degreeThreeHeisenbergMatrix central p *
        degreeThreeHeisenbergMatrix central q := by
  classical
  change
    degreeThreeHeisenbergMatrix central
        ⟨p.z + q.z + p.y * q.x, p.x + q.x, p.y + q.y⟩ =
      degreeThreeHeisenbergMatrix central p *
        degreeThreeHeisenbergMatrix central q
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (j + q.x)]
  · simp only [degreeThreeHeisenbergMatrix, if_pos rfl]
    change
      (if i = j + (p.x + q.x) then
          threePhase
            (degreeThreeCentralParameter central *
              (p.z + q.z + p.y * q.x + (p.y + q.y) * j))
        else 0) =
        (if i = (j + q.x) + p.x then
            threePhase
              (degreeThreeCentralParameter central *
                (p.z + p.y * (j + q.x)))
          else 0) *
          threePhase
            (degreeThreeCentralParameter central *
              (q.z + q.y * j))
    by_cases hi : i = j + (p.x + q.x)
    · have hindex :
          j + (p.x + q.x) = (j + q.x) + p.x := by
        ring
      simp only [hi, if_true, hindex]
      rw [← threePhase_add]
      congr 1
      ring
    · have hi' : i ≠ (j + q.x) + p.x := by
        intro h
        apply hi
        rw [h]
        ring
      simp [hi, hi']
  · intro b _ hb
    have hzero :
        degreeThreeHeisenbergMatrix central q b j = 0 := by
      simp [degreeThreeHeisenbergMatrix, hb]
    simp [hzero]
  · simp

/-- The Schrödinger matrix as an invertible matrix. -/
def degreeThreeHeisenbergGL
    (central : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    Matrix.GeneralLinearGroup (ZMod 3) ℂ :=
  ⟨degreeThreeHeisenbergMatrix central p,
    degreeThreeHeisenbergMatrix central p⁻¹,
    by
      rw [← degreeThreeHeisenbergMatrix_mul,
        mul_inv_cancel, degreeThreeHeisenbergMatrix_one],
    by
      rw [← degreeThreeHeisenbergMatrix_mul,
        inv_mul_cancel, degreeThreeHeisenbergMatrix_one]⟩

@[simp]
theorem degreeThreeHeisenbergGL_coe
    (central : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    (degreeThreeHeisenbergGL central p :
      Matrix (ZMod 3) (ZMod 3) ℂ) =
      degreeThreeHeisenbergMatrix central p :=
  rfl

/-- The Schrödinger matrices form a representation of the Heisenberg
coordinate group. -/
def degreeThreeHeisenbergGLHom (central : Fin 2) :
    AlternatingSixThreeHeisenbergCoordinates →*
      Matrix.GeneralLinearGroup (ZMod 3) ℂ where
  toFun := degreeThreeHeisenbergGL central
  map_one' := by
    apply Units.ext
    exact degreeThreeHeisenbergMatrix_one central
  map_mul' p q := by
    apply Units.ext
    simpa only [Units.val_mul, degreeThreeHeisenbergGL_coe] using
      degreeThreeHeisenbergMatrix_mul central p q

/-- The corresponding complex representation of the Heisenberg group. -/
def degreeThreeHeisenbergRepresentation (central : Fin 2) :
    Representation ℂ AlternatingSixThreeHeisenbergCoordinates
      (ZMod 3 → ℂ) :=
  (Units.coeHom
      ((ZMod 3 → ℂ) →ₗ[ℂ] (ZMod 3 → ℂ))).comp
    ((Matrix.GeneralLinearGroup.toLin :
        Matrix.GeneralLinearGroup (ZMod 3) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (ZMod 3 → ℂ))
      |>.toMonoidHom.comp
        (degreeThreeHeisenbergGLHom central))

@[simp]
theorem degreeThreeHeisenbergRepresentation_apply
    (central : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    degreeThreeHeisenbergRepresentation central p =
      Matrix.toLin'
        (degreeThreeHeisenbergMatrix central p) :=
  rfl

/-- The finite-dimensional object underlying a Schrödinger row. -/
abbrev degreeThreeHeisenbergFDRep (central : Fin 2) :
    FDRep ℂ AlternatingSixThreeHeisenbergCoordinates :=
  FDRep.of (degreeThreeHeisenbergRepresentation central)

@[simp]
theorem degreeThreeHeisenbergFDRep_finrank (central : Fin 2) :
    Module.finrank ℂ (degreeThreeHeisenbergFDRep central) = 3 := by
  simp [degreeThreeHeisenbergFDRep, ZMod.card]

/-- The first noncentral generator, represented by cyclic translation. -/
def degreeThreeHeisenbergGeneratorX :
    AlternatingSixThreeHeisenbergCoordinates :=
  alternatingSixThreeHeisenbergCoordinateX

/-- The second noncentral generator, represented diagonally. -/
def degreeThreeHeisenbergGeneratorY :
    AlternatingSixThreeHeisenbergCoordinates :=
  alternatingSixThreeHeisenbergCoordinateY

/-- Cyclic translation on the three basis vectors. -/
def degreeThreeShiftMatrix : Matrix (ZMod 3) (ZMod 3) ℂ :=
  fun i j => if i = j + 1 then 1 else 0

/-- The diagonal matrix carrying the chosen nontrivial central
character. -/
def degreeThreePhaseMatrix (central : Fin 2) :
    Matrix (ZMod 3) (ZMod 3) ℂ :=
  Matrix.diagonal fun j =>
    threePhase (degreeThreeCentralParameter central * j)

@[simp]
theorem degreeThreeHeisenbergRepresentation_generatorX
    (central : Fin 2) :
    degreeThreeHeisenbergRepresentation central
        degreeThreeHeisenbergGeneratorX =
      Matrix.toLin' degreeThreeShiftMatrix := by
  rw [degreeThreeHeisenbergRepresentation_apply]
  apply congrArg Matrix.toLin'
  change
    degreeThreeHeisenbergMatrix central
        degreeThreeHeisenbergGeneratorX =
      degreeThreeShiftMatrix
  ext i j
  simp [degreeThreeHeisenbergGeneratorX,
    degreeThreeHeisenbergMatrix, degreeThreeShiftMatrix,
    alternatingSixThreeHeisenbergCoordinateX]

@[simp]
theorem degreeThreeHeisenbergRepresentation_generatorY
    (central : Fin 2) :
    degreeThreeHeisenbergRepresentation central
        degreeThreeHeisenbergGeneratorY =
      Matrix.toLin' (degreeThreePhaseMatrix central) := by
  rw [degreeThreeHeisenbergRepresentation_apply]
  apply congrArg Matrix.toLin'
  change
    degreeThreeHeisenbergMatrix central
        degreeThreeHeisenbergGeneratorY =
      degreeThreePhaseMatrix central
  ext i j
  by_cases hij : i = j
  · subst j
    simp [degreeThreeHeisenbergGeneratorY,
      degreeThreeHeisenbergMatrix, degreeThreePhaseMatrix,
      alternatingSixThreeHeisenbergCoordinateY]
  · simp [degreeThreeHeisenbergGeneratorY,
      degreeThreeHeisenbergMatrix, degreeThreePhaseMatrix,
      alternatingSixThreeHeisenbergCoordinateY, hij]

theorem degreeThreePhase_injective (central : Fin 2) :
    Function.Injective
      (fun j : ZMod 3 =>
        threePhase (degreeThreeCentralParameter central * j)) := by
  intro i j hij
  have hmul :
      degreeThreeCentralParameter central * i =
        degreeThreeCentralParameter central * j :=
    ZMod.injective_stdAddChar hij
  exact mul_left_cancel₀
    (degreeThreeCentralParameter_ne_zero central) hmul

/-- The translation and phase matrices have only scalar common
commutants. -/
theorem degreeThreeHeisenberg_scalar_commutant
    (central : Fin 2)
    (X : Matrix (ZMod 3) (ZMod 3) ℂ)
    (hshift :
      X * degreeThreeShiftMatrix =
        degreeThreeShiftMatrix * X)
    (hphase :
      X * degreeThreePhaseMatrix central =
        degreeThreePhaseMatrix central * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (ZMod 3) (ZMod 3) ℂ) := by
  let d : ZMod 3 → ℂ :=
    fun j => threePhase (degreeThreeCentralParameter central * j)
  have hdiag :
      X * Matrix.diagonal d = Matrix.diagonal d * X :=
    hphase
  have off (i j : ZMod 3) (hij : i ≠ j) : X i j = 0 := by
    apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
      X d hdiag i j
    exact
      (degreeThreePhase_injective central).ne
        (fun h => hij h.symm)
  have h01 : X 0 1 = 0 := off 0 1 (by decide)
  have h02 : X 0 2 = 0 := off 0 2 (by decide)
  have h10 : X 1 0 = 0 := off 1 0 (by decide)
  have h12 : X 1 2 = 0 := off 1 2 (by decide)
  have h20 : X 2 0 = 0 := off 2 0 (by decide)
  have h21 : X 2 1 = 0 := off 2 1 (by decide)
  have shift_entry (i j : ZMod 3) :
      X i (j + 1) = X (i - 1) j := by
    have h := congrFun (congrFun hshift i) j
    have hleft :
        (X * degreeThreeShiftMatrix) i j = X i (j + 1) := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single (j + 1)]
      · simp [degreeThreeShiftMatrix]
      · intro b _ hb
        simp [degreeThreeShiftMatrix, hb]
      · simp
    have hright :
        (degreeThreeShiftMatrix * X) i j = X (i - 1) j := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single (i - 1)]
      · simp [degreeThreeShiftMatrix]
      · intro b _ hb
        have hne : i ≠ b + 1 := by
          intro heq
          apply hb
          rw [heq]
          ring
        simp [degreeThreeShiftMatrix, hne]
      · simp
    rw [hleft, hright] at h
    exact h
  have hdiag01 : X 0 0 = X 1 1 := by
    have h := (shift_entry (1 : ZMod 3) (0 : ZMod 3)).symm
    norm_num at h
    exact h
  have hdiag12 : X 1 1 = X 2 2 := by
    have h := (shift_entry (2 : ZMod 3) (1 : ZMod 3)).symm
    norm_num at h
    exact h
  have hdiagall (i : ZMod 3) : X i i = X 0 0 := by
    fin_cases i
    · rfl
    · exact hdiag01.symm
    · exact (hdiag01.trans hdiag12).symm
  refine ⟨X 0 0, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hdiagall]
  · rw [off i j hij]
    simp [hij]

/-- Both Schrödinger representations are simple. -/
theorem degreeThreeHeisenbergFDRep_simple (central : Fin 2) :
    Simple (degreeThreeHeisenbergFDRep central) := by
  exact
    FDRep.simple_of_two_generator_matrix_scalar_commutant
      (degreeThreeHeisenbergRepresentation central)
      degreeThreeHeisenbergGeneratorX
      degreeThreeHeisenbergGeneratorY
      degreeThreeShiftMatrix
      (degreeThreePhaseMatrix central)
      (degreeThreeHeisenbergRepresentation_generatorX central)
      (degreeThreeHeisenbergRepresentation_generatorY central)
      (degreeThreeHeisenberg_scalar_commutant central)

/-- The two nonlinear irreducible characters of the Heisenberg factor. -/
def degreeThreeHeisenbergCharacter (central : Fin 2) :
    IrreducibleCharacter AlternatingSixThreeHeisenbergCoordinates := by
  letI : Simple (degreeThreeHeisenbergFDRep central) :=
    degreeThreeHeisenbergFDRep_simple central
  exact
    IrreducibleCharacter.ofSimple
      (degreeThreeHeisenbergFDRep central)

@[simp]
theorem degreeThreeHeisenbergCharacter_degree (central : Fin 2) :
    (degreeThreeHeisenbergCharacter central).degree = 3 := by
  change Module.finrank ℂ (degreeThreeHeisenbergFDRep central) = 3
  exact degreeThreeHeisenbergFDRep_finrank central

/-- Character values are the trace of the displayed Schrödinger
matrix. -/
theorem degreeThreeHeisenbergCharacter_values
    (central : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    (degreeThreeHeisenbergCharacter central).values p =
      Matrix.trace (degreeThreeHeisenbergMatrix central p) := by
  change
    (degreeThreeHeisenbergFDRep central).character p =
      Matrix.trace (degreeThreeHeisenbergMatrix central p)
  rw [show
      (degreeThreeHeisenbergFDRep central).character p =
        LinearMap.trace ℂ (ZMod 3 → ℂ)
          (Matrix.toLin'
            (degreeThreeHeisenbergMatrix central p)) by
      rfl,
    Matrix.trace_toLin'_eq]

end AlternatingSixThreeNormalizer
end McKayConjecture
