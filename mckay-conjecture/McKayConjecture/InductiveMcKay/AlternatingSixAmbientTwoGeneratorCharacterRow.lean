/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwoGeneratorMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientMatrixRepresentation

/-!
# Character rows from two ambient generator matrices

Every exact ambient matrix certificate is transported from the same
two-generator Schur presentation to the canonical universal cover.  This file
checks that transport once and packages a scalar common-commutant proof as
either categorical simplicity or a normalized character-row certificate.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev ambientSourceEquiv :=
  alternatingSixSchurUniversalCentralExtension.sourceEquiv
    alternatingSixUniversalCentralExtension

/-- Canonical-cover element corresponding to the first Schur-presentation
generator. -/
def alternatingSixAmbientCanonicalGeneratorA :
    AlternatingSixUniversalCover :=
  ambientSourceEquiv alternatingSixSchurPresentedA

/-- Canonical-cover element corresponding to the second Schur-presentation
generator. -/
def alternatingSixAmbientCanonicalGeneratorB :
    AlternatingSixUniversalCover :=
  ambientSourceEquiv alternatingSixSchurPresentedB

/-- The central square of the first canonical lifted generator. -/
def alternatingSixAmbientCanonicalCentralGenerator :
    AlternatingSixUniversalCover :=
  alternatingSixAmbientCanonicalGeneratorA ^ 2

/-- The product of the two canonical lifted generators. -/
def alternatingSixAmbientCanonicalGeneratorAB :
    AlternatingSixUniversalCover :=
  alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB

/-- A fixed element whose character value separates the two residual
degree-four and degree-five pairs in the ordinary table.

Its positive word `a b a b b a b b b` is the shortlex state `77`; using a
positive word avoids introducing matrix inverses into the exact trace
certificate. -/
def alternatingSixAmbientCanonicalSeparator :
    AlternatingSixUniversalCover :=
  alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB

namespace AlternatingSixSchurMatrixRowCertificate

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
variable (C : AlternatingSixSchurMatrixRowCertificate n)

/-- Read a character value directly from an exact action matrix. -/
theorem universalCoverRepresentation_character_eq_trace_of_action_eq
    (g : AlternatingSixUniversalCover)
    (M : Matrix n n ℂ)
    (h :
      C.universalCoverRepresentation g =
        Matrix.toLin' M) :
    (FDRep.of C.universalCoverRepresentation).character g =
      M.trace := by
  change
    LinearMap.trace ℂ (n → ℂ)
        (C.universalCoverRepresentation g) =
      M.trace
  rw [h, Matrix.trace_toLin'_eq]

/-- The first canonical lifted generator acts by the certificate's first
matrix. -/
theorem universalCoverRepresentation_generatorA :
    C.universalCoverRepresentation
        alternatingSixAmbientCanonicalGeneratorA =
      Matrix.toLin' C.matrixA := by
  change
    C.presentedRepresentation
        (ambientSourceEquiv.symm
          (ambientSourceEquiv alternatingSixSchurPresentedA)) =
      Matrix.toLin' C.matrixA
  rw [ambientSourceEquiv.symm_apply_apply,
    C.presentedRepresentation_a]
  change
    (Matrix.GeneralLinearGroup.toLin C.matrixAGL :
      (n → ℂ) →ₗ[ℂ] (n → ℂ)) =
        Matrix.toLin' C.matrixA
  rw [Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.toLin'_apply', C.matrixAGL_val]

/-- The character value at the first canonical lifted generator is the
matrix trace of `matrixA`. -/
theorem universalCoverRepresentation_character_generatorA :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorA =
      C.matrixA.trace :=
  C.universalCoverRepresentation_character_eq_trace_of_action_eq
    alternatingSixAmbientCanonicalGeneratorA C.matrixA
    C.universalCoverRepresentation_generatorA

/-- The second canonical lifted generator acts by the certificate's second
matrix. -/
theorem universalCoverRepresentation_generatorB :
    C.universalCoverRepresentation
        alternatingSixAmbientCanonicalGeneratorB =
      Matrix.toLin' C.matrixB := by
  change
    C.presentedRepresentation
        (ambientSourceEquiv.symm
          (ambientSourceEquiv alternatingSixSchurPresentedB)) =
      Matrix.toLin' C.matrixB
  rw [ambientSourceEquiv.symm_apply_apply,
    C.presentedRepresentation_b]
  change
    (Matrix.GeneralLinearGroup.toLin C.matrixBGL :
      (n → ℂ) →ₗ[ℂ] (n → ℂ)) =
        Matrix.toLin' C.matrixB
  rw [Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.toLin'_apply', C.matrixBGL_val]

/-- The character value at the second canonical lifted generator is the
matrix trace of `matrixB`. -/
theorem universalCoverRepresentation_character_generatorB :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorB =
      C.matrixB.trace :=
  C.universalCoverRepresentation_character_eq_trace_of_action_eq
    alternatingSixAmbientCanonicalGeneratorB C.matrixB
    C.universalCoverRepresentation_generatorB

/-- The canonical central generator acts by the square of `matrixA`. -/
theorem universalCoverRepresentation_centralGenerator :
    C.universalCoverRepresentation
        alternatingSixAmbientCanonicalCentralGenerator =
      Matrix.toLin' (C.matrixA ^ 2) := by
  rw [alternatingSixAmbientCanonicalCentralGenerator,
    map_pow, C.universalCoverRepresentation_generatorA,
    Matrix.toLin'_pow]

/-- Character value at the canonical central generator. -/
theorem universalCoverRepresentation_character_centralGenerator :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalCentralGenerator =
      (C.matrixA ^ 2).trace :=
  C.universalCoverRepresentation_character_eq_trace_of_action_eq
    alternatingSixAmbientCanonicalCentralGenerator
    (C.matrixA ^ 2)
    C.universalCoverRepresentation_centralGenerator

/-- The central character value is the representation dimension times the
first relator scalar. -/
theorem universalCoverRepresentation_character_centralGenerator_eq :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalCentralGenerator =
      (Fintype.card n : ℂ) * C.relatorScalar 0 := by
  rw [C.universalCoverRepresentation_character_centralGenerator,
    C.matrixA_sq]
  simp [Matrix.trace, mul_comm]

/-- The product of the canonical lifted generators acts by
`matrixA * matrixB`. -/
theorem universalCoverRepresentation_generatorAB :
    C.universalCoverRepresentation
        alternatingSixAmbientCanonicalGeneratorAB =
      Matrix.toLin' (C.matrixA * C.matrixB) := by
  rw [alternatingSixAmbientCanonicalGeneratorAB,
    map_mul, C.universalCoverRepresentation_generatorA,
    C.universalCoverRepresentation_generatorB,
    Module.End.mul_eq_comp, Matrix.toLin'_mul]

/-- Character value at the product of the canonical lifted generators. -/
theorem universalCoverRepresentation_character_generatorAB :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorAB =
      (C.matrixA * C.matrixB).trace :=
  C.universalCoverRepresentation_character_eq_trace_of_action_eq
    alternatingSixAmbientCanonicalGeneratorAB
    (C.matrixA * C.matrixB)
    C.universalCoverRepresentation_generatorAB

/-- The fixed positive separating word acts by the corresponding matrix
word. -/
theorem universalCoverRepresentation_separator :
    C.universalCoverRepresentation
        alternatingSixAmbientCanonicalSeparator =
      Matrix.toLin'
        (C.matrixA * C.matrixB * C.matrixA *
          C.matrixB * C.matrixB * C.matrixA *
          C.matrixB * C.matrixB * C.matrixB) := by
  simp only [alternatingSixAmbientCanonicalSeparator,
    map_mul, C.universalCoverRepresentation_generatorA,
    C.universalCoverRepresentation_generatorB,
    Module.End.mul_eq_comp, Matrix.toLin'_mul]

/-- Character value at the fixed positive separating word. -/
theorem universalCoverRepresentation_character_separator :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalSeparator =
      (C.matrixA * C.matrixB * C.matrixA *
        C.matrixB * C.matrixB * C.matrixA *
        C.matrixB * C.matrixB * C.matrixB).trace :=
  C.universalCoverRepresentation_character_eq_trace_of_action_eq
    alternatingSixAmbientCanonicalSeparator
    (C.matrixA * C.matrixB * C.matrixA *
      C.matrixB * C.matrixB * C.matrixA *
      C.matrixB * C.matrixB * C.matrixB)
    C.universalCoverRepresentation_separator

/-- A scalar common commutant for the two presentation matrices proves that
the transported canonical-cover representation is simple. -/
theorem universalCoverRepresentation_simple_of_scalar_commutant
    (scalar_commutant :
      ∀ X : Matrix n n ℂ,
        X * C.matrixA = C.matrixA * X →
        X * C.matrixB = C.matrixB * X →
        ∃ c : ℂ, X = c • (1 : Matrix n n ℂ)) :
    Simple (FDRep.of C.universalCoverRepresentation) :=
  FDRep.simple_of_two_generator_matrix_scalar_commutant
    C.universalCoverRepresentation
    alternatingSixAmbientCanonicalGeneratorA
    alternatingSixAmbientCanonicalGeneratorB
    C.matrixA C.matrixB
    C.universalCoverRepresentation_generatorA
    C.universalCoverRepresentation_generatorB
    scalar_commutant

/-- Package an exact ambient row and its scalar common-commutant proof as a
normalized character-row certificate. -/
def characterRowCertificateOfScalarCommutant
    (scalar_commutant :
      ∀ X : Matrix n n ℂ,
        X * C.matrixA = C.matrixA * X →
        X * C.matrixB = C.matrixB * X →
        ∃ c : ℂ, X = c • (1 : Matrix n n ℂ)) :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  CharacterRowCertificate.ofTwoGeneratorMatrixScalarCommutant
    C.universalCoverRepresentation
    alternatingSixAmbientCanonicalGeneratorA
    alternatingSixAmbientCanonicalGeneratorB
    C.matrixA C.matrixB
    C.universalCoverRepresentation_generatorA
    C.universalCoverRepresentation_generatorB
    scalar_commutant

@[simp]
theorem characterRowCertificateOfScalarCommutant_representation
    (scalar_commutant :
      ∀ X : Matrix n n ℂ,
        X * C.matrixA = C.matrixA * X →
        X * C.matrixB = C.matrixB * X →
        ∃ c : ℂ, X = c • (1 : Matrix n n ℂ)) :
    (C.characterRowCertificateOfScalarCommutant
        scalar_commutant).representation =
      FDRep.of C.universalCoverRepresentation :=
  rfl

end AlternatingSixSchurMatrixRowCertificate
end InductiveMcKay
end McKayConjecture
