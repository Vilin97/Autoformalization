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

namespace AlternatingSixSchurMatrixRowCertificate

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
variable (C : AlternatingSixSchurMatrixRowCertificate n)

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
