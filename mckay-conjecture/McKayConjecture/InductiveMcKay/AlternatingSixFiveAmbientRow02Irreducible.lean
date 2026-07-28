/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwoGeneratorMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow02
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientRow02ScalarCommutant

/-!
# Irreducibility certificate for ambient row 02

The independently checked relation files first produce an honest
representation of the canonical universal cover.  Its two canonical lifted
presentation generators have exactly the advertised matrices.  The row 02
scalar-commutant calculation can therefore be transported to intertwiners,
giving both categorical simplicity and a normalized character-row
certificate.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "A" => alternatingSixFiveAmbient_row02_matrixA
local notation "B" => alternatingSixFiveAmbient_row02_matrixB

/-- The row 02 presentation certificate assembled from the stable aggregate
relation import and the common order-three-positive scalar pattern. -/
def alternatingSixFiveAmbientRow02IrreducibleMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 3) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreePositive A B
    (by
      simpa [AlternatingSixAmbientScalarPattern.exponent] using
        alternatingSixFiveAmbient_row02_matrixA_sq)
    (by
      simpa [AlternatingSixAmbientScalarPattern.exponent] using
        alternatingSixFiveAmbient_row02_matrixB_fourth)
    (by
      simpa [AlternatingSixAmbientScalarPattern.exponent] using
        alternatingSixFiveAmbient_row02_matrixAB_fifth)
    (by
      simpa [AlternatingSixAmbientScalarPattern.exponent] using
        alternatingSixFiveAmbient_row02_matrixABSquared_fifth)

private abbrev row02SourceEquiv :=
  alternatingSixSchurUniversalCentralExtension.sourceEquiv
    alternatingSixUniversalCentralExtension

/-- Canonical-cover element corresponding to the first presentation
generator. -/
def alternatingSixFiveAmbientRow02CanonicalGeneratorA :
    AlternatingSixUniversalCover :=
  row02SourceEquiv alternatingSixSchurPresentedA

/-- Canonical-cover element corresponding to the second presentation
generator. -/
def alternatingSixFiveAmbientRow02CanonicalGeneratorB :
    AlternatingSixUniversalCover :=
  row02SourceEquiv alternatingSixSchurPresentedB

/-- The honest canonical-cover representation afforded by row 02. -/
def alternatingSixFiveAmbientRow02Representation :
    Representation ℂ AlternatingSixUniversalCover (Fin 3 → ℂ) :=
  alternatingSixFiveAmbientRow02IrreducibleMatrixCertificate
    |>.universalCoverRepresentation

/-- The first canonical lifted generator acts by the advertised matrix. -/
theorem alternatingSixFiveAmbientRow02Representation_generatorA :
    alternatingSixFiveAmbientRow02Representation
        alternatingSixFiveAmbientRow02CanonicalGeneratorA =
      Matrix.toLin' A := by
  change
    (alternatingSixFiveAmbientRow02IrreducibleMatrixCertificate
      |>.presentedRepresentation
        (row02SourceEquiv.symm
          (row02SourceEquiv alternatingSixSchurPresentedA))) =
      Matrix.toLin' A
  rw [row02SourceEquiv.symm_apply_apply,
    AlternatingSixSchurMatrixRowCertificate.presentedRepresentation_a]
  change
    (Matrix.GeneralLinearGroup.toLin
        alternatingSixFiveAmbientRow02IrreducibleMatrixCertificate.matrixAGL :
      (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) =
        Matrix.toLin' A
  rw [Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.toLin'_apply',
    AlternatingSixSchurMatrixRowCertificate.matrixAGL_val]
  rfl

/-- The second canonical lifted generator acts by the advertised matrix. -/
theorem alternatingSixFiveAmbientRow02Representation_generatorB :
    alternatingSixFiveAmbientRow02Representation
        alternatingSixFiveAmbientRow02CanonicalGeneratorB =
      Matrix.toLin' B := by
  change
    (alternatingSixFiveAmbientRow02IrreducibleMatrixCertificate
      |>.presentedRepresentation
        (row02SourceEquiv.symm
          (row02SourceEquiv alternatingSixSchurPresentedB))) =
      Matrix.toLin' B
  rw [row02SourceEquiv.symm_apply_apply,
    AlternatingSixSchurMatrixRowCertificate.presentedRepresentation_b]
  change
    (Matrix.GeneralLinearGroup.toLin
        alternatingSixFiveAmbientRow02IrreducibleMatrixCertificate.matrixBGL :
      (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) =
        Matrix.toLin' B
  rw [Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.toLin'_apply',
    AlternatingSixSchurMatrixRowCertificate.matrixBGL_val]
  rfl

/-- The row 02 canonical-cover representation is simple. -/
theorem alternatingSixFiveAmbientRow02Representation_simple :
    Simple
      (FDRep.of alternatingSixFiveAmbientRow02Representation) :=
  FDRep.simple_of_two_generator_matrix_scalar_commutant
    alternatingSixFiveAmbientRow02Representation
    alternatingSixFiveAmbientRow02CanonicalGeneratorA
    alternatingSixFiveAmbientRow02CanonicalGeneratorB
    A B
    alternatingSixFiveAmbientRow02Representation_generatorA
    alternatingSixFiveAmbientRow02Representation_generatorB
    alternatingSixFiveAmbientRow02_scalar_commutant

/-- Fully checked normalized character-row certificate for ambient row 02,
obtained from its two-generator scalar commutant. -/
def alternatingSixFiveAmbientRow02CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  CharacterRowCertificate.ofTwoGeneratorMatrixScalarCommutant
    alternatingSixFiveAmbientRow02Representation
    alternatingSixFiveAmbientRow02CanonicalGeneratorA
    alternatingSixFiveAmbientRow02CanonicalGeneratorB
    A B
    alternatingSixFiveAmbientRow02Representation_generatorA
    alternatingSixFiveAmbientRow02Representation_generatorB
    alternatingSixFiveAmbientRow02_scalar_commutant

@[simp]
theorem alternatingSixFiveAmbientRow02CharacterRowCertificate_representation :
    alternatingSixFiveAmbientRow02CharacterRowCertificate.representation =
      FDRep.of alternatingSixFiveAmbientRow02Representation :=
  rfl

end InductiveMcKay
end McKayConjecture
