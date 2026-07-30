/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyClasses
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterAutomorphismChecks
import McKayConjecture.InductiveMcKay.AutomorphismStabilizerCorrection

/-!
# Sylow-stabilizing outer automorphisms of the canonical `A₆` cover

An automorphism of the computable Schur-cover coordinates transports across
the fixed multiplicative equivalence to the canonical free-presentation
universal cover.  For any prime and any chosen Sylow subgroup of that cover,
the generic Sylow correction construction then supplies an inner-corrected
element of the exact `SylowAutStabilizer`.

The construction is generic in the Schur-coordinate automorphism.  The two
audited outer automorphisms are exposed as thin specializations.  No claim is
made here about their action on character-table rows or about generation of
the full Sylow stabilizer.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Transport an automorphism of the computable Schur-cover coordinates to
the canonical universal cover of `A₆`. -/
def alternatingSixUniversalCoverAutomorphismOfSchur
    (a : MulAut AlternatingSixSchurCoordinates) :
    MulAut AlternatingSixUniversalCover :=
  MulAut.congr alternatingSixSchurCoordinatesEquivUniversalCover a

@[simp]
theorem alternatingSixUniversalCoverAutomorphismOfSchur_apply
    (a : MulAut AlternatingSixSchurCoordinates)
    (x : AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverAutomorphismOfSchur a x =
      alternatingSixSchurCoordinatesEquivUniversalCover
        (a (alternatingSixSchurCoordinatesEquivUniversalCover.symm x)) :=
  rfl

/-- Transport a Schur-coordinate automorphism and inner-correct it to
stabilize an arbitrary chosen Sylow subgroup of the canonical cover. -/
def alternatingSixUniversalCoverSylowStabilizerOfSchur
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover)
    (a : MulAut AlternatingSixSchurCoordinates) :
    SylowAutStabilizer P :=
  SylowAutStabilizer.corrected P
    (alternatingSixUniversalCoverAutomorphismOfSchur a)

/-- The corrected transported automorphism stabilizes the chosen Sylow
subgroup. -/
@[simp]
theorem alternatingSixUniversalCoverSylowStabilizerOfSchur_smul
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover)
    (a : MulAut AlternatingSixSchurCoordinates) :
    (alternatingSixUniversalCoverSylowStabilizerOfSchur P a :
        MulAut AlternatingSixUniversalCover) • P = P :=
  SylowAutStabilizer.correctedAutomorphism_smul P
    (alternatingSixUniversalCoverAutomorphismOfSchur a)

/-- Literal formula for the underlying inner-corrected automorphism. -/
@[simp]
theorem alternatingSixUniversalCoverSylowStabilizerOfSchur_coe
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover)
    (a : MulAut AlternatingSixSchurCoordinates) :
    (alternatingSixUniversalCoverSylowStabilizerOfSchur P a :
        MulAut AlternatingSixUniversalCover) =
      MulAut.conj
          (SylowAutStabilizer.correctionConjugator P
            (alternatingSixUniversalCoverAutomorphismOfSchur a)) *
        alternatingSixUniversalCoverAutomorphismOfSchur a :=
  SylowAutStabilizer.corrected_coe P
    (alternatingSixUniversalCoverAutomorphismOfSchur a)

/-! ### The two audited outer automorphisms -/

/-- The first audited Schur automorphism transported to the canonical
universal cover. -/
def alternatingSixUniversalCoverTransportedAlphaOne :
    MulAut AlternatingSixUniversalCover :=
  alternatingSixUniversalCoverAutomorphismOfSchur
    alternatingSixSchurAlphaOneAutomorphism

/-- The second audited Schur automorphism transported to the canonical
universal cover. -/
def alternatingSixUniversalCoverTransportedAlphaTwo :
    MulAut AlternatingSixUniversalCover :=
  alternatingSixUniversalCoverAutomorphismOfSchur
    alternatingSixSchurAlphaTwoAutomorphism

@[simp]
theorem alternatingSixUniversalCoverTransportedAlphaOne_apply
    (x : AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverTransportedAlphaOne x =
      alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAlphaOneAutomorphism
          (alternatingSixSchurCoordinatesEquivUniversalCover.symm x)) :=
  rfl

@[simp]
theorem alternatingSixUniversalCoverTransportedAlphaTwo_apply
    (x : AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverTransportedAlphaTwo x =
      alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAlphaTwoAutomorphism
          (alternatingSixSchurCoordinatesEquivUniversalCover.symm x)) :=
  rfl

/-- The first audited outer automorphism, inner-corrected to stabilize any
chosen Sylow subgroup of the canonical cover. -/
def alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    SylowAutStabilizer P :=
  SylowAutStabilizer.corrected P
    alternatingSixUniversalCoverTransportedAlphaOne

/-- The second audited outer automorphism, inner-corrected to stabilize any
chosen Sylow subgroup of the canonical cover. -/
def alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    SylowAutStabilizer P :=
  SylowAutStabilizer.corrected P
    alternatingSixUniversalCoverTransportedAlphaTwo

@[simp]
theorem alternatingSixUniversalCoverCorrectedAlphaOneStabilizer_smul
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer P :
        MulAut AlternatingSixUniversalCover) • P = P :=
  SylowAutStabilizer.correctedAutomorphism_smul P
    alternatingSixUniversalCoverTransportedAlphaOne

@[simp]
theorem alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer_smul
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer P :
        MulAut AlternatingSixUniversalCover) • P = P :=
  SylowAutStabilizer.correctedAutomorphism_smul P
    alternatingSixUniversalCoverTransportedAlphaTwo

@[simp]
theorem alternatingSixUniversalCoverCorrectedAlphaOneStabilizer_coe
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer P :
        MulAut AlternatingSixUniversalCover) =
      MulAut.conj
          (SylowAutStabilizer.correctionConjugator P
            alternatingSixUniversalCoverTransportedAlphaOne) *
        alternatingSixUniversalCoverTransportedAlphaOne :=
  SylowAutStabilizer.corrected_coe P
    alternatingSixUniversalCoverTransportedAlphaOne

@[simp]
theorem alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer_coe
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer P :
        MulAut AlternatingSixUniversalCover) =
      MulAut.conj
          (SylowAutStabilizer.correctionConjugator P
            alternatingSixUniversalCoverTransportedAlphaTwo) *
        alternatingSixUniversalCoverTransportedAlphaTwo :=
  SylowAutStabilizer.corrected_coe P
    alternatingSixUniversalCoverTransportedAlphaTwo

end InductiveMcKay
end McKayConjecture
