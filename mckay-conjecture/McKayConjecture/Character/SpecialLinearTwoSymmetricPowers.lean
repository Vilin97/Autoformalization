/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.SymmetricSquare
import McKayConjecture.Character.SymmetricCube
import McKayConjecture.Character.SymmetricFourthPower
import McKayConjecture.Character.SymmetricFifthPower

/-!
# The low symmetric-power ladder for `SL(2, ℂ)`

Any homomorphism `G → SL(2, ℂ)` gives a two-dimensional complex
representation.  Its symmetric powers of degrees two through five have
dimensions three through six and characters

* `t² - 1`,
* `t³ - 2t`,
* `t⁴ - 3t² + 1`,
* `t⁵ - 4t³ + 3t`,

where `t` is the character of the original representation.  This file
packages those constructions and formulas, as well as the character and
dimension of the tensor product of two such two-dimensional
representations.
-/

noncomputable section

open CategoryTheory Matrix
open scoped MatrixGroups MonoidalCategory

namespace McKayConjecture
namespace SpecialLinearTwoRepresentation

variable {G : Type*} [Group G]

/-- Regard a homomorphism into `SL(2, ℂ)` as one into `GL(2, ℂ)`. -/
def generalLinearHom
    (ρ : G →* SL(2, ℂ)) :
    G →* GL (Fin 2) ℂ :=
  Matrix.SpecialLinearGroup.toGL.comp ρ

@[simp]
theorem coe_generalLinearHom
    (ρ : G →* SL(2, ℂ)) (g : G) :
    (generalLinearHom ρ g : Matrix (Fin 2) (Fin 2) ℂ) =
      (ρ g : Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

/-- The defining two-dimensional representation attached to an
`SL(2, ℂ)`-valued homomorphism. -/
def representation
    (ρ : G →* SL(2, ℂ)) :
    Representation ℂ G (Fin 2 → ℂ) :=
  (Units.coeHom
      ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))).comp
    ((Matrix.GeneralLinearGroup.toLin :
        GL (Fin 2) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (Fin 2 → ℂ))
      |>.toMonoidHom.comp
        (generalLinearHom ρ))

@[simp]
theorem representation_apply
    (ρ : G →* SL(2, ℂ)) (g : G) :
    representation ρ g =
      Matrix.toLin'
        (ρ g : Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

/-- The defining two-dimensional finite-dimensional representation. -/
abbrev fdRep
    (ρ : G →* SL(2, ℂ)) :
    FDRep ℂ G :=
  FDRep.of (representation ρ)

@[simp]
theorem fdRep_finrank
    (ρ : G →* SL(2, ℂ)) :
    Module.finrank ℂ (fdRep ρ) = 2 := by
  simp [fdRep]

@[simp]
theorem representation_character
    (ρ : G →* SL(2, ℂ)) (g : G) :
    (representation ρ).character g =
      Matrix.trace
        (ρ g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show
      (representation ρ).character g =
        LinearMap.trace ℂ (Fin 2 → ℂ)
          (Matrix.toLin'
            (ρ g :
              Matrix (Fin 2) (Fin 2) ℂ)) by
      rfl,
    Matrix.trace_toLin'_eq]

/-- If a group element maps to the central matrix `-I`, then it acts as
`-I` in the defining representation. -/
theorem representation_apply_of_matrix_eq_neg_one
    (ρ : G →* SL(2, ℂ)) (z : G)
    (hz :
      (ρ z : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    representation ρ z = -1 := by
  rw [representation_apply, hz]
  ext v i
  fin_cases i <;> simp

theorem generalLinearHom_det
    (ρ : G →* SL(2, ℂ)) (g : G) :
    Matrix.det
      (generalLinearHom ρ g :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  (ρ g).prop

/-! ### Symmetric powers -/

/-- The three-dimensional symmetric square. -/
abbrev symmetricSquareRepresentation
    (ρ : G →* SL(2, ℂ)) :
    Representation ℂ G (Fin 3 → ℂ) :=
  SymmetricSquare.representation (generalLinearHom ρ)

/-- The three-dimensional symmetric square as an `FDRep`. -/
abbrev symmetricSquareFDRep
    (ρ : G →* SL(2, ℂ)) :
    FDRep ℂ G :=
  SymmetricSquare.fdRep (generalLinearHom ρ)

@[simp]
theorem symmetricSquareFDRep_finrank
    (ρ : G →* SL(2, ℂ)) :
    Module.finrank ℂ (symmetricSquareFDRep ρ) = 3 :=
  SymmetricSquare.fdRep_finrank _

@[simp]
theorem symmetricSquare_character
    (ρ : G →* SL(2, ℂ)) (g : G) :
    (symmetricSquareRepresentation ρ).character g =
      (representation ρ).character g ^ 2 - 1 := by
  rw [SymmetricSquare.representation_character_of_det_one
    (generalLinearHom ρ) (generalLinearHom_det ρ),
    coe_generalLinearHom,
    representation_character]

/-- The central matrix `-I` acts trivially on the symmetric square. -/
theorem symmetricSquare_apply_of_matrix_eq_neg_one
    (ρ : G →* SL(2, ℂ)) (z : G)
    (hz :
      (ρ z : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    symmetricSquareRepresentation ρ z = 1 := by
  rw [SymmetricSquare.representation_apply,
    coe_generalLinearHom, hz,
    SymmetricSquare.matrix_neg_one,
    Matrix.toLin'_one]
  rfl

/-- The four-dimensional symmetric cube. -/
abbrev symmetricCubeRepresentation
    (ρ : G →* SL(2, ℂ)) :
    Representation ℂ G (Fin 4 → ℂ) :=
  SymmetricCube.representation (generalLinearHom ρ)

/-- The four-dimensional symmetric cube as an `FDRep`. -/
abbrev symmetricCubeFDRep
    (ρ : G →* SL(2, ℂ)) :
    FDRep ℂ G :=
  SymmetricCube.fdRep (generalLinearHom ρ)

@[simp]
theorem symmetricCubeFDRep_finrank
    (ρ : G →* SL(2, ℂ)) :
    Module.finrank ℂ (symmetricCubeFDRep ρ) = 4 :=
  SymmetricCube.fdRep_finrank _

@[simp]
theorem symmetricCube_character
    (ρ : G →* SL(2, ℂ)) (g : G) :
    (symmetricCubeRepresentation ρ).character g =
      (representation ρ).character g ^ 3 -
        2 * (representation ρ).character g := by
  rw [SymmetricCube.representation_character_of_det_one
    (generalLinearHom ρ) (generalLinearHom_det ρ),
    coe_generalLinearHom,
    representation_character]

/-- The central matrix `-I` acts as `-I` on the symmetric cube. -/
theorem symmetricCube_apply_of_matrix_eq_neg_one
    (ρ : G →* SL(2, ℂ)) (z : G)
    (hz :
      (ρ z : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    symmetricCubeRepresentation ρ z = -1 := by
  rw [SymmetricCube.representation_apply,
    coe_generalLinearHom, hz,
    SymmetricCube.matrix_neg_one]
  ext v i
  fin_cases i <;> simp

/-- The five-dimensional fourth symmetric power. -/
abbrev symmetricFourthPowerRepresentation
    (ρ : G →* SL(2, ℂ)) :
    Representation ℂ G (Fin 5 → ℂ) :=
  SymmetricFourthPower.representation (generalLinearHom ρ)

/-- The five-dimensional fourth symmetric power as an `FDRep`. -/
abbrev symmetricFourthPowerFDRep
    (ρ : G →* SL(2, ℂ)) :
    FDRep ℂ G :=
  SymmetricFourthPower.fdRep (generalLinearHom ρ)

@[simp]
theorem symmetricFourthPowerFDRep_finrank
    (ρ : G →* SL(2, ℂ)) :
    Module.finrank ℂ (symmetricFourthPowerFDRep ρ) = 5 :=
  SymmetricFourthPower.fdRep_finrank _

@[simp]
theorem symmetricFourthPower_character
    (ρ : G →* SL(2, ℂ)) (g : G) :
    (symmetricFourthPowerRepresentation ρ).character g =
      (representation ρ).character g ^ 4 -
        3 * (representation ρ).character g ^ 2 + 1 := by
  rw [SymmetricFourthPower.representation_character_of_det_one
    (generalLinearHom ρ) (generalLinearHom_det ρ),
    coe_generalLinearHom,
    representation_character]

/-- The central matrix `-I` acts trivially on the fourth symmetric power. -/
theorem symmetricFourthPower_apply_of_matrix_eq_neg_one
    (ρ : G →* SL(2, ℂ)) (z : G)
    (hz :
      (ρ z : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    symmetricFourthPowerRepresentation ρ z = 1 := by
  rw [SymmetricFourthPower.representation_apply,
    coe_generalLinearHom, hz,
    SymmetricFourthPower.matrix_neg_one,
    Matrix.toLin'_one]
  rfl

/-- The six-dimensional fifth symmetric power. -/
abbrev symmetricFifthPowerRepresentation
    (ρ : G →* SL(2, ℂ)) :
    Representation ℂ G (Fin 6 → ℂ) :=
  SymmetricFifthPower.representation (generalLinearHom ρ)

/-- The six-dimensional fifth symmetric power as an `FDRep`. -/
abbrev symmetricFifthPowerFDRep
    (ρ : G →* SL(2, ℂ)) :
    FDRep ℂ G :=
  SymmetricFifthPower.fdRep (generalLinearHom ρ)

@[simp]
theorem symmetricFifthPowerFDRep_finrank
    (ρ : G →* SL(2, ℂ)) :
    Module.finrank ℂ (symmetricFifthPowerFDRep ρ) = 6 :=
  SymmetricFifthPower.fdRep_finrank _

@[simp]
theorem symmetricFifthPower_character
    (ρ : G →* SL(2, ℂ)) (g : G) :
    (symmetricFifthPowerRepresentation ρ).character g =
      (representation ρ).character g ^ 5 -
        4 * (representation ρ).character g ^ 3 +
          3 * (representation ρ).character g := by
  rw [SymmetricFifthPower.representation_character_of_det_one
    (generalLinearHom ρ) (generalLinearHom_det ρ),
    coe_generalLinearHom,
    representation_character]

/-- The central matrix `-I` acts as `-I` on the fifth symmetric power. -/
theorem symmetricFifthPower_apply_of_matrix_eq_neg_one
    (ρ : G →* SL(2, ℂ)) (z : G)
    (hz :
      (ρ z : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    symmetricFifthPowerRepresentation ρ z = -1 := by
  rw [SymmetricFifthPower.representation_apply,
    coe_generalLinearHom, hz,
    SymmetricFifthPower.matrix_neg_one]
  ext v i
  fin_cases i <;> simp

/-! ### Tensor products -/

/-- Tensor product of the defining representations attached to two
`SL(2, ℂ)` homomorphisms. -/
abbrev tensorFDRep
    (ρ σ : G →* SL(2, ℂ)) :
    FDRep ℂ G :=
  fdRep ρ ⊗ fdRep σ

@[simp]
theorem tensorFDRep_finrank
    (ρ σ : G →* SL(2, ℂ)) :
    Module.finrank ℂ (tensorFDRep ρ σ) = 4 := by
  calc
    Module.finrank ℂ (tensorFDRep ρ σ) =
        Module.finrank ℂ (fdRep ρ) *
          Module.finrank ℂ (fdRep σ) :=
      Module.finrank_tensorProduct
    _ = 4 := by simp

@[simp]
theorem tensorFDRep_character
    (ρ σ : G →* SL(2, ℂ)) (g : G) :
    (tensorFDRep ρ σ).character g =
      (fdRep ρ).character g *
        (fdRep σ).character g := by
  have hchar :=
    congrFun (FDRep.char_tensor (fdRep ρ) (fdRep σ)) g
  simpa only [Pi.mul_apply] using hchar

/-- If both defining representations send an element to `-I`, that
element acts trivially on their tensor product. -/
theorem tensorFDRep_apply_of_matrices_eq_neg_one
    (ρ σ : G →* SL(2, ℂ)) (z : G)
    (hρ :
      (ρ z : Matrix (Fin 2) (Fin 2) ℂ) = -1)
    (hσ :
      (σ z : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    (tensorFDRep ρ σ).ρ z = 1 := by
  change
    Representation.tprod
        (representation ρ) (representation σ) z = 1
  rw [Representation.tprod_apply,
    representation_apply_of_matrix_eq_neg_one ρ z hρ,
    representation_apply_of_matrix_eq_neg_one σ z hσ]
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.one_apply, TensorProduct.map_tmul,
    LinearMap.neg_apply, TensorProduct.tmul_neg,
    TensorProduct.neg_tmul, neg_neg]

end SpecialLinearTwoRepresentation
end McKayConjecture
