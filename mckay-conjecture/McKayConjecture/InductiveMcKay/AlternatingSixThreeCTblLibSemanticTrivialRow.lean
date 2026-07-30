/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibParameterizedRowBridge
import McKayConjecture.InductiveMcKay.AlternatingSixThreeTrivialProjectiveRow

/-!
# The semantic CTblLib bridge at the three-local trivial row

The independently audited CTblLib ambient and local generator permutations
all fix their zeroth displayed position.  This position is the trivial
character on both sides: in the constructed ambient table it is `row01`,
and in the constructed local table it is the frequency-zero linear row.

This file proves directly from the genuine character actions that both
corrected generators fix those two semantic rows.  Consequently every
parameterized CT-position identification which sends position zero to the
two trivial rows satisfies all four generator bridges at position zero.
The recorded display identifications have this property.

No assertion is made here about the remaining eleven CT positions.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeSemanticTrivialRowFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- Every ambient automorphism fixes the arithmetic three-prime row
affording the intrinsic trivial character. -/
theorem alternatingSixThreeAmbientTrivialRow_fixed
    (a : MulAut AlternatingSixUniversalCover) :
    alternatingSixAmbientPPrimeRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3 a
        alternatingSixThreeTrivialPPrimeRow =
      alternatingSixThreeTrivialPPrimeRow := by
  apply
    (alternatingSixAmbientPPrimeCharacterEquiv
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3).injective
  rw [alternatingSixAmbientPPrimeRowPermutation_character]
  apply Subtype.ext
  let χ :=
    (alternatingSixAmbientPPrimeCharacterEquiv
      alternatingSixAmbientOrdinaryCharacterTableCertificate 3
      alternatingSixThreeTrivialPPrimeRow).1
  have hχ :
      χ =
        IrreducibleCharacter.trivial
          AlternatingSixUniversalCover :=
    alternatingSixThreeAmbientTrivialCharacter_eq
  calc
    (a •
        alternatingSixAmbientPPrimeCharacterEquiv
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3
          alternatingSixThreeTrivialPPrimeRow).1 =
        a • IrreducibleCharacter.trivial
          AlternatingSixUniversalCover := congrArg (fun ψ ↦ a • ψ) hχ
    _ = IrreducibleCharacter.trivial
          AlternatingSixUniversalCover := by
      apply IrreducibleCharacter.ext
      funext g
      simp
    _ =
        (alternatingSixAmbientPPrimeCharacterEquiv
          alternatingSixAmbientOrdinaryCharacterTableCertificate 3
          alternatingSixThreeTrivialPPrimeRow).1 := hχ.symm

/-- Every genuine Sylow-stabilizer action fixes the frequency-zero local
row, since that row affords the intrinsic trivial character. -/
theorem alternatingSixThreeActualNormalizerLinearZeroRow_fixed
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3)) :
    alternatingSixThreeActualNormalizerRowPermutation a
        (Sum.inl (0 : Fin 8)) =
      Sum.inl 0 := by
  apply
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv.injective
  rw [alternatingSixThreeActualNormalizerRowPermutation_character]
  apply Subtype.ext
  let χ :=
    (AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
      (Sum.inl (0 : Fin 8))).1
  have hχ :
      χ =
        IrreducibleCharacter.trivial
          AlternatingSixUniversalCoverThreeNormalizer :=
    alternatingSixThreeActualNormalizerLinearZeroCharacter_eq
  calc
    (a •
        AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
          (Sum.inl (0 : Fin 8))).1 =
        SylowAutStabilizer.normalizerRestrictionHom
            (alternatingSixUniversalCoverSylow 3) a •
          χ := rfl
    _ =
        SylowAutStabilizer.normalizerRestrictionHom
            (alternatingSixUniversalCoverSylow 3) a •
          IrreducibleCharacter.trivial
            AlternatingSixUniversalCoverThreeNormalizer :=
      congrArg
        (fun ψ ↦
          SylowAutStabilizer.normalizerRestrictionHom
              (alternatingSixUniversalCoverSylow 3) a • ψ)
        hχ
    _ =
        IrreducibleCharacter.trivial
          AlternatingSixUniversalCoverThreeNormalizer := by
      apply IrreducibleCharacter.ext
      funext g
      simp
    _ =
        (AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
          (Sum.inl (0 : Fin 8))).1 := hχ.symm

@[simp]
theorem
    alternatingSixThreeAmbientCorrectedAlphaOneTrivialRow_fixed :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        alternatingSixThreeTrivialPPrimeRow =
      alternatingSixThreeTrivialPPrimeRow := by
  rw [alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq]
  exact
    alternatingSixThreeAmbientTrivialRow_fixed
      alternatingSixUniversalCoverTransportedAlphaOne

@[simp]
theorem
    alternatingSixThreeAmbientCorrectedAlphaTwoTrivialRow_fixed :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        alternatingSixThreeTrivialPPrimeRow =
      alternatingSixThreeTrivialPPrimeRow := by
  rw [alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq]
  exact
    alternatingSixThreeAmbientTrivialRow_fixed
      alternatingSixUniversalCoverTransportedAlphaTwo

@[simp]
theorem
    alternatingSixThreeActualNormalizerCorrectedAlphaOneLinearZeroRow_fixed :
    alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
        (Sum.inl (0 : Fin 8)) =
      Sum.inl 0 :=
  alternatingSixThreeActualNormalizerLinearZeroRow_fixed
    (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
      (alternatingSixUniversalCoverSylow 3))

@[simp]
theorem
    alternatingSixThreeActualNormalizerCorrectedAlphaTwoLinearZeroRow_fixed :
    alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
        (Sum.inl (0 : Fin 8)) =
      Sum.inl 0 :=
  alternatingSixThreeActualNormalizerLinearZeroRow_fixed
    (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
      (alternatingSixUniversalCoverSylow 3))

namespace AlternatingSixThreeCTblLibRowIdentification

variable
  (identification : AlternatingSixThreeCTblLibRowIdentification)

/-- A parameterized CT-position identification has the correct semantic
trivial position when its two zeroth images are the constructed trivial
rows. -/
def HasSemanticTrivialPosition : Prop :=
  identification.ambientPositionEquiv 0 =
      alternatingSixThreeTrivialPPrimeRow ∧
    identification.localPositionEquiv 0 =
      Sum.inl (0 : Fin 8)

/-- The first corrected ambient bridge holds at CT position zero for every
identification with the correct semantic trivial position. -/
theorem ambientCorrectedAlphaOneBridge_zero
    (h : identification.HasSemanticTrivialPosition) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (identification.ambientPositionEquiv 0) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne 0) := by
  calc
    _ =
        alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 3)
          alternatingSixThreeTrivialPPrimeRow :=
      congrArg
        (alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 3))
        h.1
    _ = alternatingSixThreeTrivialPPrimeRow :=
      alternatingSixThreeAmbientCorrectedAlphaOneTrivialRow_fixed
    _ = identification.ambientPositionEquiv 0 := h.1.symm
    _ =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne 0) := by
      rfl

/-- The second corrected ambient bridge holds at CT position zero for every
identification with the correct semantic trivial position. -/
theorem ambientCorrectedAlphaTwoBridge_zero
    (h : identification.HasSemanticTrivialPosition) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        (alternatingSixUniversalCoverSylow 3)
        (identification.ambientPositionEquiv 0) =
      identification.ambientPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo 0) := by
  calc
    _ =
        alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 3)
          alternatingSixThreeTrivialPPrimeRow :=
      congrArg
        (alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
          alternatingSixAmbientOrdinaryCharacterTableCertificate
          (alternatingSixUniversalCoverSylow 3))
        h.1
    _ = alternatingSixThreeTrivialPPrimeRow :=
      alternatingSixThreeAmbientCorrectedAlphaTwoTrivialRow_fixed
    _ = identification.ambientPositionEquiv 0 := h.1.symm
    _ =
        identification.ambientPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo 0) := by
      rfl

/-- The first corrected local bridge holds at CT position zero for every
identification with the correct semantic trivial position. -/
theorem localCorrectedAlphaOneBridge_zero
    (h : identification.HasSemanticTrivialPosition) :
    alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
        (identification.localPositionEquiv 0) =
      identification.localPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.localAlphaOne 0) := by
  calc
    _ =
        alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
          (Sum.inl (0 : Fin 8)) :=
      congrArg
        alternatingSixThreeActualNormalizerCorrectedAlphaOneRowPermutation
        h.2
    _ = Sum.inl 0 :=
      alternatingSixThreeActualNormalizerCorrectedAlphaOneLinearZeroRow_fixed
    _ = identification.localPositionEquiv 0 := h.2.symm
    _ =
        identification.localPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.localAlphaOne 0) := by
      rfl

/-- The second corrected local bridge holds at CT position zero for every
identification with the correct semantic trivial position. -/
theorem localCorrectedAlphaTwoBridge_zero
    (h : identification.HasSemanticTrivialPosition) :
    alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
        (identification.localPositionEquiv 0) =
      identification.localPositionEquiv
        (alternatingSixCTblLibThreePPrimeActionData.localAlphaTwo 0) := by
  calc
    _ =
        alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
          (Sum.inl (0 : Fin 8)) :=
      congrArg
        alternatingSixThreeActualNormalizerCorrectedAlphaTwoRowPermutation
        h.2
    _ = Sum.inl 0 :=
      alternatingSixThreeActualNormalizerCorrectedAlphaTwoLinearZeroRow_fixed
    _ = identification.localPositionEquiv 0 := h.2.symm
    _ =
        identification.localPositionEquiv
          (alternatingSixCTblLibThreePPrimeActionData.localAlphaTwo 0) := by
      rfl

end AlternatingSixThreeCTblLibRowIdentification

/-- The recorded display identifications agree with CTblLib at the
distinguished trivial position. -/
theorem alternatingSixThreeRecordedCTblLibRowIdentification_hasSemanticTrivialPosition :
    alternatingSixThreeRecordedCTblLibRowIdentification
      |>.HasSemanticTrivialPosition := by
  constructor <;>
    rfl

end InductiveMcKay
end McKayConjecture
