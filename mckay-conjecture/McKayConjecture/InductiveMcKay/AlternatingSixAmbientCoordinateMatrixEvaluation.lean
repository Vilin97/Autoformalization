/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RepresentationTheory.Character
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyClasses
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientMatrixRepresentation

/-!
# Evaluating ambient matrix rows on Schur-cover coordinates

The checked Schur-cover coordinate model stores a short signed word in the
two noncentral generators and a power of the first central relator.  This
module evaluates those two pieces directly in any exact ambient matrix row.
It is the low-footprint bridge used by class-value and character-norm
certificates: no matrix commutant calculation is involved.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

namespace AlternatingSixSchurMatrixRowCertificate

variable {n : Type} [Fintype n] [DecidableEq n]
variable (C : AlternatingSixSchurMatrixRowCertificate n)

/-- The `GL` value of one signed rewrite letter. -/
def rewriteLetterGL
    (letter : AlternatingSixRewriteLetter) :
    Matrix.GeneralLinearGroup n ℂ :=
  let generator :=
    if letter.1 = 0 then C.matrixAGL else C.matrixBGL
  if letter.2 then generator else generator⁻¹

/-- The `GL` value of a signed word in the two noncentral generators. -/
def rewriteWordGL
    (C : AlternatingSixSchurMatrixRowCertificate n) :
    AlternatingSixRewriteWord →
      Matrix.GeneralLinearGroup n ℂ
  | [] => 1
  | letter :: word =>
      C.rewriteLetterGL letter * C.rewriteWordGL word

/-- The descended presentation homomorphism evaluates a signed word by
substituting the two certificate matrices. -/
theorem presentedGLRepresentation_schurWord
    (word : AlternatingSixRewriteWord) :
    C.presentedGLRepresentation
        (alternatingSixSchurWord word) =
      C.rewriteWordGL word := by
  induction word with
  | nil =>
      simp [rewriteWordGL]
  | cons letter word ih =>
      rw [show letter :: word = [letter] ++ word by rfl]
      rw [alternatingSixSchurWord_append, map_mul, ih]
      rcases letter with ⟨generator, positive⟩
      fin_cases generator <;>
        cases positive <;>
        simp [alternatingSixSchurWord, rewriteWordGL,
          rewriteLetterGL, presentedGLRepresentation,
          presentationData]

/-- The central coordinate evaluates as the corresponding natural power of
the first relator scalar. -/
theorem presentedGLRepresentation_centralValue
    (central : ZMod 6) :
    C.presentedGLRepresentation
        (AlternatingSixSchurCoordinates.centralValue central) =
      C.relatorGL 0 ^ central.val := by
  let k := central.val
  have hcentral : central = (k : ZMod 6) :=
    (ZMod.natCast_zmod_val central).symm
  have hk : k < 6 := central.val_lt
  rw [hcentral]
  rw [AlternatingSixSchurCoordinates.centralValue,
    QuaternionGroup.zmodPower_natCast, map_pow]
  rw [ZMod.val_natCast_of_lt hk]
  congr 1
  simp [presentedGLRepresentation, presentationData,
    alternatingSixSchurPresentedK]

/-- Exact `GL` evaluation of an arbitrary Schur-cover coordinate. -/
theorem presentedGLRepresentation_coordinate
    (coordinate : AlternatingSixSchurCoordinates) :
    C.presentedGLRepresentation
        (AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          coordinate) =
      C.rewriteWordGL
          (alternatingSixRewriteNormalWords coordinate.state) *
        C.relatorGL 0 ^ coordinate.central.val := by
  rw [AlternatingSixSchurCoordinates.mulEquivPresentedGroup_apply,
    AlternatingSixSchurCoordinates.evaluate, map_mul,
    alternatingSixSchurNormalElement,
    C.presentedGLRepresentation_schurWord,
    C.presentedGLRepresentation_centralValue]

/-- The exact `GL` matrix attached to one Schur-cover coordinate. -/
def coordinateGL
    (coordinate : AlternatingSixSchurCoordinates) :
    Matrix.GeneralLinearGroup n ℂ :=
  C.rewriteWordGL
      (alternatingSixRewriteNormalWords coordinate.state) *
    C.relatorGL 0 ^ coordinate.central.val

/-- Coordinate evaluation in the linear presentation representation. -/
theorem presentedRepresentation_coordinate
    (coordinate : AlternatingSixSchurCoordinates) :
    C.presentedRepresentation
        (AlternatingSixSchurCoordinates.mulEquivPresentedGroup
          coordinate) =
      Matrix.toLin' (C.coordinateGL coordinate : Matrix n n ℂ) := by
  change
    (Matrix.GeneralLinearGroup.toLin
        (C.presentedGLRepresentation
          (AlternatingSixSchurCoordinates.mulEquivPresentedGroup
            coordinate)) :
      (n → ℂ) →ₗ[ℂ] (n → ℂ)) =
        Matrix.toLin' (C.coordinateGL coordinate : Matrix n n ℂ)
  rw [C.presentedGLRepresentation_coordinate]
  rw [Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.toLin'_apply']
  rfl

/-- Coordinate evaluation after transport to the canonical universal cover. -/
theorem universalCoverRepresentation_coordinate
    (coordinate : AlternatingSixSchurCoordinates) :
    C.universalCoverRepresentation
        (alternatingSixSchurCoordinatesEquivUniversalCover coordinate) =
      Matrix.toLin' (C.coordinateGL coordinate : Matrix n n ℂ) := by
  change
    C.presentedRepresentation
        ((alternatingSixSchurUniversalCentralExtension.sourceEquiv
            alternatingSixUniversalCentralExtension).symm
          ((alternatingSixSchurUniversalCentralExtension.sourceEquiv
              alternatingSixUniversalCentralExtension)
            (AlternatingSixSchurCoordinates.mulEquivPresentedGroup
              coordinate))) =
      _
  rw [MulEquiv.symm_apply_apply]
  exact C.presentedRepresentation_coordinate coordinate

/-- The character value of a coordinate is the trace of its exact `GL`
matrix. -/
theorem universalCoverRepresentation_character_coordinate
    [Nonempty n]
    (coordinate : AlternatingSixSchurCoordinates) :
    (FDRep.of C.universalCoverRepresentation).character
        (alternatingSixSchurCoordinatesEquivUniversalCover coordinate) =
      (C.coordinateGL coordinate : Matrix n n ℂ).trace := by
  change
    LinearMap.trace ℂ (n → ℂ)
        (C.universalCoverRepresentation
          (alternatingSixSchurCoordinatesEquivUniversalCover
            coordinate)) =
      _
  rw [C.universalCoverRepresentation_coordinate,
    Matrix.trace_toLin'_eq]

end AlternatingSixSchurMatrixRowCertificate
end InductiveMcKay
end McKayConjecture
