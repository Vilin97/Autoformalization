/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientCompletedOrdinaryCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibParameterizedFullEquivariance
import McKayConjecture.InductiveMcKay.ExactNormalizerTrivialProjectiveRow

/-!
# The trivial projective row for a fixed two-local `A₆` candidate

The first arithmetic ambient row has degree one and hence, by perfectness
of the canonical sixfold cover, is intrinsically trivial.  The existing
central-block candidate sends it to the zero-frequency character of the
proved `C₃ × Q₁₆` normalizer model.  Direct calculation identifies the
transport of that local row with the intrinsic trivial character.

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

local instance alternatingSixTwoTrivialProjectiveRowFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The degree-one row in the arithmetic ambient `2'`-row enumeration. -/
def alternatingSixTwoTrivialPPrimeRow :
    AlternatingSixAmbientPPrimeRowIndex 2 :=
  ⟨.row01, by decide⟩

/-- The completed ambient character at the degree-one row is the intrinsic
trivial character. -/
theorem alternatingSixTwoAmbientTrivialCharacter_eq :
    (alternatingSixAmbientPPrimeCharacterEquiv
        alternatingSixAmbientOrdinaryCharacterTableCertificate 2
        alternatingSixTwoTrivialPPrimeRow).1 =
      IrreducibleCharacter.trivial AlternatingSixUniversalCover := by
  apply IrreducibleCharacter.eq_trivial_of_degree_one
  rw [alternatingSixAmbientPPrimeCharacterEquiv_degree]
  rfl

/-- The fixed proposed central-block candidate sends the ambient trivial
row to the zero-frequency row of the concrete two-normalizer table.

This is a computation in the engineered candidate, not a CTblLib display
order assertion. -/
@[simp]
theorem alternatingSixTwoCentralBlockRowEquiv_trivialRow :
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        alternatingSixTwoTrivialPPrimeRow =
      (0, (0, 0)) := by
  change
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        ⟨.row01, by decide⟩ =
      (0, (0, 0))
  exact
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow_row01

/-- The deliberately engineered CTblLib position specialization recovers
the same first-row computation. -/
@[simp]
theorem alternatingSixTwoCentralBlockCandidate_trivialRow :
    (alternatingSixTwoCentralBlockCTblLibRowIdentification
        |>.candidateAmbientLocalRowEquiv)
        alternatingSixTwoTrivialPPrimeRow =
      (0, (0, 0)) := by
  rw [
    alternatingSixTwoCentralBlockCTblLibRowIdentification_candidate,
    alternatingSixTwoCentralBlockRowEquiv_trivialRow
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

private theorem quaternionGroupFourLinearHom_zero :
    QuaternionGroupFour.linearHom ((0, 0) :
      QuaternionGroupFour.LinearIndex) = 1 := by
  apply MonoidHom.ext
  intro g
  rcases g with i | i
  · simp only [QuaternionGroupFour.linearHom,
      QuaternionGroupFour.linearHomOfSigns,
      QuaternionGroup.lift_apply_a]
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective i
    rw [← hz, QuaternionGroup.zmodPower_intCast]
    simp [QuaternionGroupFour.signParameter]
  · simp only [QuaternionGroupFour.linearHom,
      QuaternionGroupFour.linearHomOfSigns,
      QuaternionGroup.lift_apply_xa]
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective i
    rw [← hz, QuaternionGroup.zmodPower_intCast]
    simp [QuaternionGroupFour.signParameter]

/-- The zero-frequency row of the concrete `C₃ × Q₁₆` normalizer model is
the intrinsic trivial character. -/
theorem alternatingSixTwoModelNormalizerZeroCharacter_eq :
    (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv
        ((0, (0, 0)) :
          AlternatingSixTwoModelNormalizerCharacterRow)).1 =
      IrreducibleCharacter.trivial
        AlternatingSixTwoNormalizerModel := by
  apply IrreducibleCharacter.ext
  funext g
  rcases g with ⟨z, q⟩
  change
    (AlternatingSixTwoNormalizerModelCharacterTable.pPrimeCharacterEquiv
        ((0, (0, 0)) :
          AlternatingSixTwoModelNormalizerCharacterRow)).1.values
        (z, q) =
      1
  rw [
    AlternatingSixTwoNormalizerModelCharacterTable.pPrimeCharacterEquiv_values
  ]
  change
    (CyclicThree.linearCharacter 0).values z *
        (QuaternionGroupFour.linearCharacter (0, 0)).values q =
      1
  rw [CyclicThree.linearCharacter,
    QuaternionGroupFour.linearCharacter,
    IrreducibleCharacter.linear_values,
    IrreducibleCharacter.linear_values,
    cyclicThreeLinearHom_zero,
    quaternionGroupFourLinearHom_zero]
  simp

/-- Transporting the zero-frequency row to the actual fixed two-normalizer
preserves its intrinsic triviality. -/
theorem alternatingSixTwoActualNormalizerZeroCharacter_eq :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
        ((0, (0, 0)) :
          AlternatingSixTwoConcreteNormalizerRow)).1 =
      IrreducibleCharacter.trivial
        (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) := by
  apply IrreducibleCharacter.ext
  funext g
  obtain ⟨x, rfl⟩ :=
    alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer.surjective g
  rw [alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_values]
  rw [alternatingSixTwoModelNormalizerZeroCharacter_eq]
  rfl

/-- Conditional on genuine ordinary equivariance of the fixed proposed
central-block candidate, its first row carries complete exact-normalizer
projective data.

The equivariance parameter is exactly the existing central-block ordinary
candidate predicate.  No additional row-identification hypothesis is
introduced. -/
def alternatingSixTwoCentralBlockTrivialProjectiveRowData
    (h :
      AlternatingSixTwoCentralBlockRowMatchingEquivariant
        alternatingSixAmbientOrdinaryCharacterTableCertificate) :
    let d :=
      alternatingSixTwoConcreteCharacterTableCertificateOfAmbientTable
        alternatingSixAmbientOrdinaryCharacterTableCertificate h
    ExactNormalizerProjectiveRowData
      d.toEquivariantMcKayEquiv
      (d.ambientEnumeration alternatingSixTwoTrivialPPrimeRow) := by
  let d :=
    alternatingSixTwoConcreteCharacterTableCertificateOfAmbientTable
      alternatingSixAmbientOrdinaryCharacterTableCertificate h
  apply ExactNormalizerProjectiveRowData.ofTrivialCharacters
  · exact alternatingSixTwoAmbientTrivialCharacter_eq
  · change
      (d.toEquivariantMcKayEquiv
          (d.ambientEnumeration
            alternatingSixTwoTrivialPPrimeRow)).1 =
        IrreducibleCharacter.trivial
          (SylowNormalizer (alternatingSixUniversalCoverSylow 2))
    rw [d.toEquivariantMcKayEquiv_apply_enumerated]
    change
      (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
          (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
            alternatingSixTwoTrivialPPrimeRow)).1 =
        IrreducibleCharacter.trivial
          (SylowNormalizer (alternatingSixUniversalCoverSylow 2))
    rw [alternatingSixTwoCentralBlockRowEquiv_trivialRow]
    exact alternatingSixTwoActualNormalizerZeroCharacter_eq

end InductiveMcKay
end McKayConjecture
