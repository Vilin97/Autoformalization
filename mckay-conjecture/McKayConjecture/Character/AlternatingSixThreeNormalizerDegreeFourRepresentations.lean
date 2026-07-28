/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FinCases
import McKayConjecture.Character.SimpleCharacterRowCertificate
import McKayConjecture.GroupTheory.AlternatingSixThreeNormalizerConjugacyInvariants

/-!
# Four-dimensional representations of the three-normalizer

The two nonzero `C₄`-orbits in the dual of the quotient
`3^(1+2)/Z` give two monomial representations of degree four.  Each has
two extensions across the kernel `C₂ ≤ C₈`, distinguished by the sign
of the fourth power of the cyclic shift.
-/

noncomputable section

open CategoryTheory Matrix

namespace McKayConjecture
namespace AlternatingSixThreeNormalizer

open GroupTheory

/-- The standard additive character of `ZMod 3`. -/
abbrev threePhase : AddChar (ZMod 3) ℂ :=
  ZMod.stdAddChar

@[simp]
theorem threePhase_add (a b : ZMod 3) :
    threePhase (a + b) = threePhase a * threePhase b :=
  AddChar.map_add_eq_mul _ _ _

@[simp]
theorem threePhase_zero :
    threePhase (0 : ZMod 3) = 1 :=
  AddChar.map_zero_eq_one _

@[simp]
theorem threePhase_neg_mul (a : ZMod 3) :
    threePhase a * threePhase (-a) = 1 := by
  rw [← threePhase_add, add_neg_cancel, threePhase_zero]

theorem threePhase_ne_zero (a : ZMod 3) :
    threePhase a ≠ 0 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.coe_ne_zero _

/-- The four weights in one of the two nonzero rotation orbits in the
dual of `ZMod 3 × ZMod 3`. -/
def degreeFourExponent
    (orbit : Fin 2) (i : Fin 4)
    (p : AlternatingSixThreeHeisenbergCoordinates) : ZMod 3 :=
  if orbit.val = 0 then
    ![p.x, p.y, -p.x, -p.y] i
  else
    ![p.x + p.y, p.y - p.x, -p.x - p.y, p.x - p.y] i

@[simp]
theorem degreeFourExponent_one
    (orbit : Fin 2) (i : Fin 4) :
    degreeFourExponent orbit i 1 = 0 := by
  change degreeFourExponent orbit i ⟨0, 0, 0⟩ = 0
  fin_cases orbit <;> fin_cases i <;>
    simp [degreeFourExponent]

@[simp]
theorem degreeFourExponent_mul
    (orbit : Fin 2) (i : Fin 4)
    (p q : AlternatingSixThreeHeisenbergCoordinates) :
    degreeFourExponent orbit i (p * q) =
      degreeFourExponent orbit i p +
        degreeFourExponent orbit i q := by
  change
    degreeFourExponent orbit i
        ⟨p.z + q.z + p.y * q.x, p.x + q.x, p.y + q.y⟩ =
      degreeFourExponent orbit i p +
        degreeFourExponent orbit i q
  fin_cases orbit <;> fin_cases i <;>
    simp [degreeFourExponent] <;> ring

/-- The diagonal matrix giving the restriction of a degree-four row to
the Heisenberg factor. -/
def degreeFourDiagonalMatrix
    (orbit : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun i => threePhase (degreeFourExponent orbit i p)

/-- Its explicit inverse diagonal matrix. -/
def degreeFourDiagonalInverseMatrix
    (orbit : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun i => threePhase (-degreeFourExponent orbit i p)

/-- The invertible diagonal matrix attached to a Heisenberg element. -/
def degreeFourDiagonalGL
    (orbit : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    Matrix.GeneralLinearGroup (Fin 4) ℂ :=
  ⟨degreeFourDiagonalMatrix orbit p,
    degreeFourDiagonalInverseMatrix orbit p,
    by
      rw [degreeFourDiagonalMatrix,
        degreeFourDiagonalInverseMatrix,
        Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [threePhase_neg_mul]
      · simp [hij],
    by
      rw [degreeFourDiagonalMatrix,
        degreeFourDiagonalInverseMatrix,
        Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [mul_comm, threePhase_neg_mul]
      · simp [hij]⟩

@[simp]
theorem degreeFourDiagonalGL_coe
    (orbit : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    (degreeFourDiagonalGL orbit p :
      Matrix (Fin 4) (Fin 4) ℂ) =
      degreeFourDiagonalMatrix orbit p :=
  rfl

/-- The diagonal matrices form a homomorphism of the Heisenberg factor. -/
def degreeFourDiagonalHom (orbit : Fin 2) :
    AlternatingSixThreeHeisenbergCoordinates →*
      Matrix.GeneralLinearGroup (Fin 4) ℂ where
  toFun := degreeFourDiagonalGL orbit
  map_one' := by
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst j
      simp [degreeFourDiagonalGL, degreeFourDiagonalMatrix]
    · simp [degreeFourDiagonalGL, degreeFourDiagonalMatrix, hij]
  map_mul' p q := by
    apply Units.ext
    rw [Units.val_mul, degreeFourDiagonalGL_coe,
      degreeFourDiagonalGL_coe, degreeFourDiagonalGL_coe]
    change
      Matrix.diagonal
          (fun i =>
            threePhase (degreeFourExponent orbit i (p * q))) =
        Matrix.diagonal
            (fun i => threePhase (degreeFourExponent orbit i p)) *
          Matrix.diagonal
            (fun i => threePhase (degreeFourExponent orbit i q))
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [degreeFourExponent_mul, threePhase_add]
    · simp [hij]

/-- The sign distinguishing the two extensions across the kernel
`C₂ ≤ C₈`. -/
def degreeFourSign (extension : Fin 2) : ℂ :=
  if extension.val = 0 then 1 else -1

@[simp]
theorem degreeFourSign_sq (extension : Fin 2) :
    degreeFourSign extension * degreeFourSign extension = 1 := by
  fin_cases extension <;> norm_num [degreeFourSign]

theorem degreeFourSign_ne_zero (extension : Fin 2) :
    degreeFourSign extension ≠ 0 := by
  fin_cases extension <;> norm_num [degreeFourSign]

/-- The cyclic shift whose fourth power is the chosen extension sign. -/
def degreeFourShiftMatrix (extension : Fin 2) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, degreeFourSign extension;
     1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0]

/-- The explicit inverse cyclic shift. -/
def degreeFourShiftInverseMatrix (extension : Fin 2) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1;
     degreeFourSign extension, 0, 0, 0]

/-- The cyclic shift as an invertible matrix. -/
def degreeFourShiftGL (extension : Fin 2) :
    Matrix.GeneralLinearGroup (Fin 4) ℂ :=
  ⟨degreeFourShiftMatrix extension,
    degreeFourShiftInverseMatrix extension,
    by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [degreeFourShiftMatrix,
          degreeFourShiftInverseMatrix,
          Matrix.mul_apply, Fin.sum_univ_succ,
          degreeFourSign_sq],
    by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [degreeFourShiftMatrix,
          degreeFourShiftInverseMatrix,
          Matrix.mul_apply, Fin.sum_univ_succ,
          degreeFourSign_sq]⟩

@[simp]
theorem degreeFourShiftGL_coe (extension : Fin 2) :
    (degreeFourShiftGL extension :
      Matrix (Fin 4) (Fin 4) ℂ) =
      degreeFourShiftMatrix extension :=
  rfl

/-- The shift has order dividing eight. -/
theorem degreeFourShiftGL_pow_eight (extension : Fin 2) :
    degreeFourShiftGL extension ^ 8 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [degreeFourShiftGL, degreeFourShiftMatrix,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
      degreeFourSign_sq]

/-- The `C₈` matrix homomorphism generated by the signed cyclic shift. -/
def degreeFourCyclicHom (extension : Fin 2) :
    AlternatingSixThreeCyclicEight →*
      Matrix.GeneralLinearGroup (Fin 4) ℂ where
  toFun c :=
    QuaternionGroup.zmodPower
      (degreeFourShiftGL extension)
      (degreeFourShiftGL_pow_eight extension)
      (Multiplicative.toAdd c)
  map_one' :=
    QuaternionGroup.zmodPower_zero
      (degreeFourShiftGL extension)
      (degreeFourShiftGL_pow_eight extension)
  map_mul' c d :=
    QuaternionGroup.zmodPower_add
      (degreeFourShiftGL extension)
      (degreeFourShiftGL_pow_eight extension)
      (Multiplicative.toAdd c)
      (Multiplicative.toAdd d)

/-- The signed shift intertwines the diagonal Heisenberg action with
the chosen order-four coordinate automorphism. -/
theorem degreeFourShiftGL_mul_diagonalGL
    (orbit extension : Fin 2)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    degreeFourShiftGL extension *
        degreeFourDiagonalGL orbit p =
      degreeFourDiagonalGL orbit
          (alternatingSixThreeHeisenbergCoordinateGenerator p) *
        degreeFourShiftGL extension := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul,
    degreeFourShiftGL_coe]
  change
    degreeFourShiftMatrix extension *
        degreeFourDiagonalMatrix orbit p =
      degreeFourDiagonalMatrix orbit
          (alternatingSixThreeHeisenbergCoordinateGenerator p) *
        degreeFourShiftMatrix extension
  ext i j
  fin_cases orbit <;> fin_cases i <;> fin_cases j
  all_goals
    simp [degreeFourShiftMatrix, degreeFourDiagonalMatrix,
      degreeFourExponent,
      alternatingSixThreeHeisenbergCoordinateGenerator,
      Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals
    first
    | ring
    | (congr 1 <;> ring)
  all_goals
    rw [show p.x - p.y = -p.y + p.x by ring,
      threePhase_add]
    ring

/-- The covariance identity iterated through a natural power of the
cyclic generator. -/
theorem degreeFourShiftGL_pow_mul_diagonalGL
    (orbit extension : Fin 2) (n : ℕ)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    degreeFourShiftGL extension ^ n *
        degreeFourDiagonalGL orbit p =
      degreeFourDiagonalGL orbit
          ((alternatingSixThreeHeisenbergCoordinateGenerator ^ n) p) *
        degreeFourShiftGL extension ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ', pow_succ']
      simp only [MulAut.mul_apply]
      calc
        degreeFourShiftGL extension *
              degreeFourShiftGL extension ^ n *
                degreeFourDiagonalGL orbit p =
            degreeFourShiftGL extension *
              (degreeFourDiagonalGL orbit
                  ((alternatingSixThreeHeisenbergCoordinateGenerator ^ n) p) *
                degreeFourShiftGL extension ^ n) := by
              rw [mul_assoc, ih]
        _ =
            (degreeFourShiftGL extension *
                degreeFourDiagonalGL orbit
                  ((alternatingSixThreeHeisenbergCoordinateGenerator ^ n) p)) *
              degreeFourShiftGL extension ^ n := by
                group
        _ =
            (degreeFourDiagonalGL orbit
                (alternatingSixThreeHeisenbergCoordinateGenerator
                  ((alternatingSixThreeHeisenbergCoordinateGenerator ^ n) p)) *
              degreeFourShiftGL extension) *
                degreeFourShiftGL extension ^ n := by
              rw [degreeFourShiftGL_mul_diagonalGL]
        _ =
            degreeFourDiagonalGL orbit
                (alternatingSixThreeHeisenbergCoordinateGenerator
                  ((alternatingSixThreeHeisenbergCoordinateGenerator ^ n) p)) *
              (degreeFourShiftGL extension *
                degreeFourShiftGL extension ^ n) := by
              group

/-- A natural residue in `C₈` acts by the corresponding natural power
of the coordinate generator. -/
theorem alternatingSixThreeHeisenbergCoordinateAction_ofAdd_nat
    (n : ℕ)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    alternatingSixThreeHeisenbergCoordinateAction
        (Multiplicative.ofAdd (n : ZMod 8)) p =
      (alternatingSixThreeHeisenbergCoordinateGenerator ^ n) p := by
  change
    QuaternionGroup.zmodPower
        alternatingSixThreeHeisenbergCoordinateGenerator
        alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
        (n : ZMod 8) p =
      (alternatingSixThreeHeisenbergCoordinateGenerator ^ n) p
  rw [QuaternionGroup.zmodPower_natCast]

/-- A natural residue in the cyclic matrix homomorphism is the
corresponding natural power of the signed shift. -/
theorem degreeFourCyclicHom_ofAdd_nat
    (extension : Fin 2) (n : ℕ) :
    degreeFourCyclicHom extension
        (Multiplicative.ofAdd (n : ZMod 8)) =
      degreeFourShiftGL extension ^ n := by
  change
    QuaternionGroup.zmodPower
        (degreeFourShiftGL extension)
        (degreeFourShiftGL_pow_eight extension)
        (n : ZMod 8) =
      degreeFourShiftGL extension ^ n
  rw [QuaternionGroup.zmodPower_natCast]

/-- Full covariance between the `C₈` shift and the coordinate action. -/
theorem degreeFourCyclicHom_mul_diagonalGL
    (orbit extension : Fin 2)
    (c : AlternatingSixThreeCyclicEight)
    (p : AlternatingSixThreeHeisenbergCoordinates) :
    degreeFourCyclicHom extension c *
        degreeFourDiagonalGL orbit p =
        degreeFourDiagonalGL orbit
          (alternatingSixThreeHeisenbergCoordinateAction c p) *
        degreeFourCyclicHom extension c := by
  apply alternatingSixThreeCyclicEight_cases (c := c)
  · change
      QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (0 : ZMod 8) *
          degreeFourDiagonalGL orbit p =
        degreeFourDiagonalGL orbit
            (QuaternionGroup.zmodPower
              alternatingSixThreeHeisenbergCoordinateGenerator
              alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
              (0 : ZMod 8) p) *
          QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (0 : ZMod 8)
    rw [show (0 : ZMod 8) = ((0 : ℕ) : ZMod 8) by rfl,
      QuaternionGroup.zmodPower_natCast]
    exact degreeFourShiftGL_pow_mul_diagonalGL orbit extension 0 p
  · change
      QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (1 : ZMod 8) *
          degreeFourDiagonalGL orbit p =
        degreeFourDiagonalGL orbit
            (QuaternionGroup.zmodPower
              alternatingSixThreeHeisenbergCoordinateGenerator
              alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
              (1 : ZMod 8) p) *
          QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (1 : ZMod 8)
    rw [show (1 : ZMod 8) = ((1 : ℕ) : ZMod 8) by rfl,
      QuaternionGroup.zmodPower_natCast]
    exact degreeFourShiftGL_pow_mul_diagonalGL orbit extension 1 p
  · change
      QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (2 : ZMod 8) *
          degreeFourDiagonalGL orbit p =
        degreeFourDiagonalGL orbit
            (QuaternionGroup.zmodPower
              alternatingSixThreeHeisenbergCoordinateGenerator
              alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
              (2 : ZMod 8) p) *
          QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (2 : ZMod 8)
    rw [show (2 : ZMod 8) = ((2 : ℕ) : ZMod 8) by rfl,
      QuaternionGroup.zmodPower_natCast]
    exact degreeFourShiftGL_pow_mul_diagonalGL orbit extension 2 p
  · change
      QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (3 : ZMod 8) *
          degreeFourDiagonalGL orbit p =
        degreeFourDiagonalGL orbit
            (QuaternionGroup.zmodPower
              alternatingSixThreeHeisenbergCoordinateGenerator
              alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
              (3 : ZMod 8) p) *
          QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (3 : ZMod 8)
    rw [show (3 : ZMod 8) = ((3 : ℕ) : ZMod 8) by rfl,
      QuaternionGroup.zmodPower_natCast]
    exact degreeFourShiftGL_pow_mul_diagonalGL orbit extension 3 p
  · change
      QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (4 : ZMod 8) *
          degreeFourDiagonalGL orbit p =
        degreeFourDiagonalGL orbit
            (QuaternionGroup.zmodPower
              alternatingSixThreeHeisenbergCoordinateGenerator
              alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
              (4 : ZMod 8) p) *
          QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (4 : ZMod 8)
    rw [show (4 : ZMod 8) = ((4 : ℕ) : ZMod 8) by rfl,
      QuaternionGroup.zmodPower_natCast]
    exact degreeFourShiftGL_pow_mul_diagonalGL orbit extension 4 p
  · change
      QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (5 : ZMod 8) *
          degreeFourDiagonalGL orbit p =
        degreeFourDiagonalGL orbit
            (QuaternionGroup.zmodPower
              alternatingSixThreeHeisenbergCoordinateGenerator
              alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
              (5 : ZMod 8) p) *
          QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (5 : ZMod 8)
    rw [show (5 : ZMod 8) = ((5 : ℕ) : ZMod 8) by rfl,
      QuaternionGroup.zmodPower_natCast]
    exact degreeFourShiftGL_pow_mul_diagonalGL orbit extension 5 p
  · change
      QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (6 : ZMod 8) *
          degreeFourDiagonalGL orbit p =
        degreeFourDiagonalGL orbit
            (QuaternionGroup.zmodPower
              alternatingSixThreeHeisenbergCoordinateGenerator
              alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
              (6 : ZMod 8) p) *
          QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (6 : ZMod 8)
    rw [show (6 : ZMod 8) = ((6 : ℕ) : ZMod 8) by rfl,
      QuaternionGroup.zmodPower_natCast]
    exact degreeFourShiftGL_pow_mul_diagonalGL orbit extension 6 p
  · change
      QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (7 : ZMod 8) *
          degreeFourDiagonalGL orbit p =
        degreeFourDiagonalGL orbit
            (QuaternionGroup.zmodPower
              alternatingSixThreeHeisenbergCoordinateGenerator
              alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
              (7 : ZMod 8) p) *
          QuaternionGroup.zmodPower
            (degreeFourShiftGL extension)
            (degreeFourShiftGL_pow_eight extension)
            (7 : ZMod 8)
    rw [show (7 : ZMod 8) = ((7 : ℕ) : ZMod 8) by rfl,
      QuaternionGroup.zmodPower_natCast]
    exact degreeFourShiftGL_pow_mul_diagonalGL orbit extension 7 p

/-- Compatibility in the orientation required by
`SemidirectProduct.lift`. -/
theorem degreeFourLiftCompatibility
    (orbit extension : Fin 2)
    (c : AlternatingSixThreeCyclicEight) :
    (degreeFourDiagonalHom orbit).comp
        (alternatingSixThreeHeisenbergCoordinateAction c).toMonoidHom =
      (MulAut.conj (degreeFourCyclicHom extension c)).toMonoidHom.comp
        (degreeFourDiagonalHom orbit) := by
  apply MonoidHom.ext
  intro p
  change
    degreeFourDiagonalGL orbit
        (alternatingSixThreeHeisenbergCoordinateAction c p) =
      degreeFourCyclicHom extension c *
        degreeFourDiagonalGL orbit p *
          (degreeFourCyclicHom extension c)⁻¹
  have hcov :=
    degreeFourCyclicHom_mul_diagonalGL orbit extension c p
  calc
    degreeFourDiagonalGL orbit
          (alternatingSixThreeHeisenbergCoordinateAction c p) =
        degreeFourDiagonalGL orbit
            (alternatingSixThreeHeisenbergCoordinateAction c p) *
          degreeFourCyclicHom extension c *
            (degreeFourCyclicHom extension c)⁻¹ := by
          group
    _ =
        degreeFourCyclicHom extension c *
          degreeFourDiagonalGL orbit p *
            (degreeFourCyclicHom extension c)⁻¹ := by
          rw [← hcov]

/-- The monomial `GL₄(ℂ)` representation of the full coordinate
normalizer. -/
def degreeFourGLHom (orbit extension : Fin 2) :
    AlternatingSixThreeNormalizerCoordinates →*
      Matrix.GeneralLinearGroup (Fin 4) ℂ :=
  SemidirectProduct.lift
    (degreeFourDiagonalHom orbit)
    (degreeFourCyclicHom extension)
    (degreeFourLiftCompatibility orbit extension)

@[simp]
theorem degreeFourGLHom_apply
    (orbit extension : Fin 2)
    (g : AlternatingSixThreeNormalizerCoordinates) :
    degreeFourGLHom orbit extension g =
      degreeFourDiagonalGL orbit g.left *
        degreeFourCyclicHom extension g.right :=
  rfl

/-- The corresponding four-dimensional complex representation. -/
def degreeFourRepresentation (orbit extension : Fin 2) :
    Representation ℂ AlternatingSixThreeNormalizerCoordinates
      (Fin 4 → ℂ) :=
  (Units.coeHom
      ((Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))).comp
    ((Matrix.GeneralLinearGroup.toLin :
        Matrix.GeneralLinearGroup (Fin 4) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (Fin 4 → ℂ))
      |>.toMonoidHom.comp
        (degreeFourGLHom orbit extension))

@[simp]
theorem degreeFourRepresentation_apply
    (orbit extension : Fin 2)
    (g : AlternatingSixThreeNormalizerCoordinates) :
    degreeFourRepresentation orbit extension g =
      Matrix.toLin'
        (degreeFourGLHom orbit extension g :
          Matrix (Fin 4) (Fin 4) ℂ) :=
  rfl

/-- The finite-dimensional object underlying a degree-four row. -/
abbrev degreeFourFDRep (orbit extension : Fin 2) :
    FDRep ℂ AlternatingSixThreeNormalizerCoordinates :=
  FDRep.of (degreeFourRepresentation orbit extension)

@[simp]
theorem degreeFourFDRep_finrank
    (orbit extension : Fin 2) :
    Module.finrank ℂ (degreeFourFDRep orbit extension) = 4 := by
  simp [degreeFourFDRep]

end AlternatingSixThreeNormalizer
end McKayConjecture
