/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientCompletedOrdinaryCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibParameterizedFullEquivariance
import McKayConjecture.InductiveMcKay.ExactNormalizerTrivialProjectiveRow

/-!
# The trivial projective row for a fixed five-local `A₆` candidate

The first arithmetic ambient row is intrinsically trivial because it has
degree one and the canonical sixfold cover is perfect.  The existing
central-block candidate sends it to the zero-frequency linear row of the
proved `C₃ × (C₅ ⋊ C₄)` normalizer model.  Direct calculation identifies
the transport of that local row with the intrinsic trivial character.

The central-block CTblLib position data used below was deliberately
engineered so that its transported audited candidate is the existing
central-block row equivalence.  It is a fixed proposed candidate, not an
assertion that either engineered position equivalence is the true CTblLib
display order.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveTrivialProjectiveRowFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The degree-one row in the arithmetic ambient `5'`-row enumeration. -/
def alternatingSixFiveTrivialPPrimeRow :
    AlternatingSixAmbientPPrimeRowIndex 5 :=
  ⟨.row01, by decide⟩

/-- The completed ambient character at the degree-one row is the intrinsic
trivial character. -/
theorem alternatingSixFiveAmbientTrivialCharacter_eq :
    (alternatingSixAmbientPPrimeCharacterEquiv
        alternatingSixAmbientOrdinaryCharacterTableCertificate 5
        alternatingSixFiveTrivialPPrimeRow).1 =
      IrreducibleCharacter.trivial AlternatingSixUniversalCover := by
  apply IrreducibleCharacter.eq_trivial_of_degree_one
  rw [alternatingSixAmbientPPrimeCharacterEquiv_degree]
  rfl

/-- The fixed proposed central-block row equivalence sends the ambient
trivial row to the zero-frequency linear row of the concrete
five-normalizer table. -/
@[simp]
theorem alternatingSixFiveCentralBlockRowEquiv_trivialRow :
    alternatingSixAmbientFivePPrimeCentralBlockRowEquiv
        alternatingSixFiveTrivialPPrimeRow =
      (0, CyclicFiveInversionSemidirect.CharacterRow.linear 0) := by
  have hrow :
      alternatingSixFiveAmbientRowEquivPPrimeRowIndex.symm
          alternatingSixFiveTrivialPPrimeRow =
        AlternatingSixFiveAmbientRow.row01 := by
    apply alternatingSixFiveAmbientRowEquivPPrimeRowIndex.injective
    rw [alternatingSixFiveAmbientRowEquivPPrimeRowIndex.apply_symm_apply]
    apply Subtype.ext
    rfl
  rw [alternatingSixAmbientFivePPrimeCentralBlockRowEquiv,
    Equiv.trans_apply, hrow]
  rfl

/-- The deliberately engineered CTblLib position specialization recovers
the same computation.

This is coordinate algebra for a fixed proposed candidate, not an
assertion that the engineered equivalences record CTblLib display order. -/
@[simp]
theorem alternatingSixFiveCentralBlockCandidate_trivialRow :
    (alternatingSixFiveCentralBlockCTblLibRowIdentification
        |>.candidateAmbientLocalRowEquiv)
        alternatingSixFiveTrivialPPrimeRow =
      (0, CyclicFiveInversionSemidirect.CharacterRow.linear 0) := by
  rw [
    alternatingSixFiveCentralBlockCTblLibRowIdentification_candidate,
    alternatingSixFiveCentralBlockRowEquiv_trivialRow
  ]

private theorem cyclicThreeLinearHom_zero :
    CyclicThree.linearHom (0 : Fin 3) = 1 := by
  apply MonoidHom.ext
  intro c
  change
    QuaternionGroup.zmodPower
        (CyclicThree.thirdRootParameter 0)
        (CyclicThree.thirdRootParameter_pow_three 0)
        (Multiplicative.toAdd c) =
      1
  obtain ⟨z, hz⟩ :=
    ZMod.intCast_surjective (Multiplicative.toAdd c)
  rw [← hz, QuaternionGroup.zmodPower_intCast]
  simp [CyclicThree.thirdRootParameter]

private theorem quaternionGroupFiveLinearHom_zero :
    QuaternionGroupFive.linearHom (0 : Fin 4) = 1 := by
  apply MonoidHom.ext
  intro g
  rcases g with i | i
  · simp only [QuaternionGroupFive.linearHom,
      QuaternionGroupFive.linearHomOfFourthRoot,
      QuaternionGroup.lift_apply_a]
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective i
    rw [← hz, QuaternionGroup.zmodPower_intCast]
    simp [QuaternionGroupFive.fourthRootParameter]
  · simp only [QuaternionGroupFive.linearHom,
      QuaternionGroupFive.linearHomOfFourthRoot,
      QuaternionGroup.lift_apply_xa]
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective i
    rw [← hz, QuaternionGroup.zmodPower_intCast]
    simp [QuaternionGroupFive.fourthRootParameter]

/-- The frequency-zero linear row of `C₅ ⋊ C₄` is intrinsically trivial. -/
theorem cyclicFiveInversionSemidirectLinearZeroCharacter_eq :
    (CyclicFiveInversionSemidirect.pPrimeCharacterEquiv
        (CyclicFiveInversionSemidirect.CharacterRow.linear 0)).1 =
      IrreducibleCharacter.trivial
        CyclicFiveInversionSemidirect.Group := by
  apply IrreducibleCharacter.ext
  funext g
  change
    (QuaternionGroupFive.linearCharacter 0).values
        (quaternionFiveEquivCyclicFiveInversionSemidirect.symm g) =
      1
  rw [QuaternionGroupFive.linearCharacter,
    IrreducibleCharacter.linear_values,
    quaternionGroupFiveLinearHom_zero]
  simp

/-- The zero-frequency row of the concrete
`C₃ × (C₅ ⋊ C₄)` normalizer model is the intrinsic trivial character. -/
theorem alternatingSixFiveSemidirectNormalizerZeroCharacter_eq :
    (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv
        ((0, CyclicFiveInversionSemidirect.CharacterRow.linear 0) :
          AlternatingSixFiveSemidirectNormalizerCharacterRow)).1 =
      IrreducibleCharacter.trivial
        AlternatingSixFiveNormalizerSemidirect := by
  apply IrreducibleCharacter.ext
  funext g
  rcases g with ⟨z, q⟩
  rw [alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv_values]
  change
    (CyclicThree.linearCharacter 0).values z *
        (CyclicFiveInversionSemidirect.pPrimeCharacterEquiv
          (CyclicFiveInversionSemidirect.CharacterRow.linear 0)).1.values q =
      1
  rw [CyclicThree.linearCharacter,
    IrreducibleCharacter.linear_values,
    cyclicThreeLinearHom_zero,
    cyclicFiveInversionSemidirectLinearZeroCharacter_eq]
  simp

/-- Values of the concrete five-normalizer rows after transport to the
actual fixed normalizer. -/
@[simp]
theorem alternatingSixFiveActualNormalizerPPrimeCharacterEquiv_values
    (r : AlternatingSixFiveConcreteNormalizerRow)
    (g : AlternatingSixFiveNormalizerSemidirect) :
    (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r).1.values
        (alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer
          g) =
      (alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r).1.values
        g := by
  change
    ((alternatingSixFiveSemidirectNormalizerPPrimeCharacterEquiv r).1.comap
        alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer.symm).values
        (alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer
          g) =
      _
  rw [IrreducibleCharacter.comap_values,
    MulEquiv.symm_apply_apply]

/-- Transporting the zero-frequency row to the actual fixed five-normalizer
preserves its intrinsic triviality. -/
theorem alternatingSixFiveActualNormalizerZeroCharacter_eq :
    (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
        ((0, CyclicFiveInversionSemidirect.CharacterRow.linear 0) :
          AlternatingSixFiveConcreteNormalizerRow)).1 =
      IrreducibleCharacter.trivial
        (SylowNormalizer (alternatingSixUniversalCoverSylow 5)) := by
  apply IrreducibleCharacter.ext
  funext g
  obtain ⟨x, rfl⟩ :=
    alternatingSixFiveNormalizerSemidirectEquivUniversalCoverNormalizer.surjective
      g
  rw [alternatingSixFiveActualNormalizerPPrimeCharacterEquiv_values]
  rw [alternatingSixFiveSemidirectNormalizerZeroCharacter_eq]
  rfl

/-- Conditional on genuine ordinary equivariance of the fixed proposed
central-block candidate, its first row carries complete exact-normalizer
projective data.

The equivariance parameter is exactly the existing central-block ordinary
candidate predicate.  No additional row-identification hypothesis is
introduced. -/
def alternatingSixFiveCentralBlockTrivialProjectiveRowData
    (h :
      AlternatingSixFiveCentralBlockRowMatchingEquivariant
        alternatingSixAmbientOrdinaryCharacterTableCertificate) :
    let d :=
      alternatingSixFiveCentralBlockConcreteCharacterTableCertificate
        alternatingSixAmbientOrdinaryCharacterTableCertificate h
    ExactNormalizerProjectiveRowData
      d.toEquivariantMcKayEquiv
      (d.ambientEnumeration alternatingSixFiveTrivialPPrimeRow) := by
  let d :=
    alternatingSixFiveCentralBlockConcreteCharacterTableCertificate
      alternatingSixAmbientOrdinaryCharacterTableCertificate h
  apply ExactNormalizerProjectiveRowData.ofTrivialCharacters
  · exact alternatingSixFiveAmbientTrivialCharacter_eq
  · change
      (d.toEquivariantMcKayEquiv
          (d.ambientEnumeration
            alternatingSixFiveTrivialPPrimeRow)).1 =
        IrreducibleCharacter.trivial
          (SylowNormalizer (alternatingSixUniversalCoverSylow 5))
    rw [d.toEquivariantMcKayEquiv_apply_enumerated]
    change
      (alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
          (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv
            alternatingSixFiveTrivialPPrimeRow)).1 =
        IrreducibleCharacter.trivial
          (SylowNormalizer (alternatingSixUniversalCoverSylow 5))
    rw [alternatingSixFiveCentralBlockRowEquiv_trivialRow]
    exact alternatingSixFiveActualNormalizerZeroCharacter_eq

end InductiveMcKay
end McKayConjecture
