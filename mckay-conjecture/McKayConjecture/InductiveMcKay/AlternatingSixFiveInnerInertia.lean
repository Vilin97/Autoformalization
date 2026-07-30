/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixAutomorphismLowerBound
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAutomorphismAction
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibParameterizedRowBridge
import McKayConjecture.InductiveMcKay.NormalizerInnerCharacterStabilizerSurjectivity

/-!
# Detecting inner inertia for five-local `A₆` rows

The certified automorphism normal form for the universal cover of `A₆`
has four outer representatives.  Since inner automorphisms act trivially
on ordinary characters, a row has entirely inner inertia as soon as none
of the three nonidentity outer representatives fixes it.

The final statements phrase this criterion on the semantic ambient row
permutations attached to a completed ordinary character table.  Thus the
remaining inertia check is finite and independent of projective
representation choices.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveInnerInertiaFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- For the canonical universal cover of `A₆`, a character whose only
fixing outer representative is the identity has inner inertia. -/
theorem
    alternatingSixNormalizerInnerCharacterStabilizerHom_surjective_of_outerRepresentative
    {p : ℕ}
    (P : Sylow p AlternatingSixUniversalCover)
    (χ : PPrimeIrreducibleCharacter AlternatingSixUniversalCover p)
    (hOuter :
      ∀ i : Fin 4,
        alternatingSixUniversalCoverOuterRepresentative i • χ = χ →
          i = 0) :
    Function.Surjective
      (normalizerInnerCharacterStabilizerHom P χ) := by
  apply
    normalizerInnerCharacterStabilizerHom_surjective_of_isInner
  intro a ha
  obtain ⟨⟨g, i⟩, hgi⟩ :=
    alternatingSixUniversalCoverAutomorphismFamily_surjective
      (a : MulAut AlternatingSixUniversalCover)
  obtain ⟨q, hq⟩ :=
    alternatingSixUniversalCoverInnerAutomorphism_mem g
  have hiFix :
      alternatingSixUniversalCoverOuterRepresentative i • χ = χ := by
    calc
      alternatingSixUniversalCoverOuterRepresentative i • χ =
          (MulAut.conj q *
              alternatingSixUniversalCoverOuterRepresentative i) • χ := by
            simp [mul_smul]
      _ =
          (alternatingSixUniversalCoverInnerAutomorphism g *
              alternatingSixUniversalCoverOuterRepresentative i) • χ := by
            rw [hq]
      _ = a • χ :=
        congrArg
          (fun b : MulAut AlternatingSixUniversalCover ↦ b • χ)
          hgi
      _ = χ := ha
  have hi : i = 0 :=
    hOuter i hiFix
  subst i
  have hRepresentativeZero :
      alternatingSixUniversalCoverOuterRepresentative 0 = 1 := by
    apply MulEquiv.ext
    intro x
    change
      alternatingSixSchurCoordinatesEquivUniversalCover
          ((1 : MulAut AlternatingSixSchurCoordinates)
            (alternatingSixSchurCoordinatesEquivUniversalCover.symm x)) =
        x
    simpa using
      alternatingSixSchurCoordinatesEquivUniversalCover.apply_symm_apply x
  refine ⟨q, ?_⟩
  calc
    (a : MulAut AlternatingSixUniversalCover) =
        alternatingSixUniversalCoverAutomorphismFamily (g, 0) :=
      hgi.symm
    _ = MulAut.conj q := by
      rw [alternatingSixUniversalCoverAutomorphismFamily,
        hRepresentativeZero, mul_one, ← hq]

/-- Semantic-row form of the four-representative criterion. -/
theorem
    alternatingSixFiveInnerCharacterStabilizer_surjective_of_outerRowsMoved
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (r : AlternatingSixAmbientPPrimeRowIndex 5)
    (hMoved :
      ∀ i : Fin 4, i ≠ 0 →
        alternatingSixAmbientPPrimeRowPermutation T 5
            (alternatingSixUniversalCoverOuterRepresentative i) r ≠
          r) :
    Function.Surjective
      (normalizerInnerCharacterStabilizerHom
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixAmbientPPrimeCharacterEquiv T 5 r)) := by
  apply
    alternatingSixNormalizerInnerCharacterStabilizerHom_surjective_of_outerRepresentative
  intro i hiFix
  by_contra hi
  apply hMoved i hi
  apply (alternatingSixAmbientPPrimeCharacterEquiv T 5).injective
  rw [alternatingSixAmbientPPrimeRowPermutation_character]
  exact hiFix

/-- It suffices to check that the two audited outer generators and their
product all move the selected semantic ambient row. -/
theorem
    alternatingSixFiveInnerCharacterStabilizer_surjective_of_generatorsMoved
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (r : AlternatingSixAmbientPPrimeRowIndex 5)
    (hAlphaOne :
      alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5 r ≠ r)
    (hAlphaTwo :
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 5 r ≠ r)
    (hAlphaOneAlphaTwo :
      alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5
          (alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 5 r) ≠
        r) :
    Function.Surjective
      (normalizerInnerCharacterStabilizerHom
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixAmbientPPrimeCharacterEquiv T 5 r)) := by
  apply
    alternatingSixFiveInnerCharacterStabilizer_surjective_of_outerRowsMoved
      T r
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · simpa [
      alternatingSixAmbientPPrimeAlphaOneRowPermutation,
      alternatingSixUniversalCoverOuterRepresentative,
      alternatingSixSchurOuterRepresentative,
      alternatingSixUniversalCoverTransportedAlphaOne,
      alternatingSixUniversalCoverAutomorphismOfSchur
    ] using hAlphaOne
  · simpa [
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
      alternatingSixUniversalCoverOuterRepresentative,
      alternatingSixSchurOuterRepresentative,
      alternatingSixUniversalCoverTransportedAlphaTwo,
      alternatingSixUniversalCoverAutomorphismOfSchur
    ] using hAlphaTwo
  · have hRepresentative :
        alternatingSixUniversalCoverOuterRepresentative 3 =
          alternatingSixUniversalCoverTransportedAlphaOne *
            alternatingSixUniversalCoverTransportedAlphaTwo := by
      simpa [
        alternatingSixUniversalCoverOuterRepresentative,
        alternatingSixSchurOuterRepresentative,
        alternatingSixUniversalCoverTransportedAlphaOne,
        alternatingSixUniversalCoverTransportedAlphaTwo,
        alternatingSixUniversalCoverAutomorphismOfSchur
      ] using
        map_mul
          (MulAut.congr
            alternatingSixSchurCoordinatesEquivUniversalCover)
          alternatingSixSchurAlphaOneAutomorphism
          alternatingSixSchurAlphaTwoAutomorphism
    change
      alternatingSixAmbientPPrimeRowPermutation T 5
          (alternatingSixUniversalCoverOuterRepresentative 3) r ≠
        r
    rw [hRepresentative,
      alternatingSixAmbientPPrimeRowPermutation_mul]
    exact hAlphaOneAlphaTwo

/-! ### Audited CT positions with free outer orbit -/

/-- A five-local CTblLib ambient position has free action under the four
audited outer representatives.  Since the first two generators are
involutions, it is enough to test them and their product. -/
def AlternatingSixFiveOuterFreeCTPosition
    (i : Fin 24) :
    Prop :=
  alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i ≠ i ∧
    alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i ≠ i ∧
      alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne
          (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i) ≠
        i

instance alternatingSixFiveOuterFreeCTPositionDecidable
    (i : Fin 24) :
    Decidable (AlternatingSixFiveOuterFreeCTPosition i) := by
  unfold AlternatingSixFiveOuterFreeCTPosition
  infer_instance

/-- Exactly twelve of the twenty-four five-prime CT positions have free
outer orbit. -/
theorem alternatingSixFiveOuterFreeCTPosition_card :
    Fintype.card
        {i : Fin 24 // AlternatingSixFiveOuterFreeCTPosition i} =
      12 := by
  decide

/-- The free positions are precisely the zero-based blocks `8..11` and
`16..23`. -/
theorem alternatingSixFiveOuterFreeCTPosition_iff
    (i : Fin 24) :
    AlternatingSixFiveOuterFreeCTPosition i ↔
      (8 ≤ i.val ∧ i.val < 12) ∨ 16 ≤ i.val := by
  fin_cases i <;> decide

namespace AlternatingSixFiveCTblLibRowIdentification

/-- Once a proposed ambient CT-position identification is known to
transport the two audited generator actions to the genuine semantic
actions, every audited free-orbit position has inner character inertia. -/
theorem innerCharacterStabilizer_surjective_of_outerFreePosition
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAlphaOne :
      identification.AmbientCorrectedAlphaOneBridge T)
    (hAlphaTwo :
      identification.AmbientCorrectedAlphaTwoBridge T)
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterFreeCTPosition i) :
    Function.Surjective
      (normalizerInnerCharacterStabilizerHom
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixAmbientPPrimeCharacterEquiv T 5
          (identification.ambientPositionEquiv i))) := by
  apply
    alternatingSixFiveInnerCharacterStabilizer_surjective_of_generatorsMoved
  · intro hfix
    apply hi.1
    apply identification.ambientPositionEquiv.injective
    have hBridge := hAlphaOne i
    rw [
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq
    ] at hBridge
    exact hBridge.symm.trans hfix
  · intro hfix
    apply hi.2.1
    apply identification.ambientPositionEquiv.injective
    have hBridge := hAlphaTwo i
    rw [
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq
    ] at hBridge
    exact hBridge.symm.trans hfix
  · intro hfix
    apply hi.2.2
    apply identification.ambientPositionEquiv.injective
    have hBridgeTwo := hAlphaTwo i
    have hBridgeOne :=
      hAlphaOne
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)
    rw [
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq
    ] at hBridgeTwo
    rw [
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq
    ] at hBridgeOne
    calc
      identification.ambientPositionEquiv
            (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne
              (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)) =
          alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5
            (identification.ambientPositionEquiv
              (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)) :=
        hBridgeOne.symm
      _ =
          alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5
            (alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 5
              (identification.ambientPositionEquiv i)) := by
        rw [hBridgeTwo]
      _ = identification.ambientPositionEquiv i := hfix

end AlternatingSixFiveCTblLibRowIdentification

end InductiveMcKay
end McKayConjecture
