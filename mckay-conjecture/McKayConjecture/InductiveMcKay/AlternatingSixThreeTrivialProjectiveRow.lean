/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientCompletedOrdinaryCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibCandidateRowBridge
import McKayConjecture.InductiveMcKay.ExactNormalizerTrivialProjectiveRow

/-!
# The trivial projective row for the three-local `A₆` candidate

The first arithmetic ambient row has degree one.  Since the canonical
sixfold cover is perfect, it is intrinsically the trivial character.  The
audited CTblLib candidate sends this row to the frequency-zero linear row
of the actual Sylow-three normalizer; an explicit calculation identifies
that local row with the intrinsic trivial character.

Consequently, whenever the existing audited candidate has been promoted
to a genuine equivariant ordinary McKay correspondence, its first row has
complete exact-normalizer projective data.  No extra semantic
identification of the first row is assumed here.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeTrivialProjectiveRowFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The degree-one row in the arithmetic ambient `3'`-row enumeration. -/
def alternatingSixThreeTrivialPPrimeRow :
    AlternatingSixAmbientPPrimeRowIndex 3 :=
  ⟨.row01, by decide⟩

/-- The completed ambient character at the degree-one row is the intrinsic
trivial character. -/
theorem alternatingSixThreeAmbientTrivialCharacter_eq :
    (alternatingSixAmbientPPrimeCharacterEquiv
        alternatingSixAmbientOrdinaryCharacterTableCertificate 3
        alternatingSixThreeTrivialPPrimeRow).1 =
      IrreducibleCharacter.trivial AlternatingSixUniversalCover := by
  apply IrreducibleCharacter.eq_trivial_of_degree_one
  rw [alternatingSixAmbientPPrimeCharacterEquiv_degree]
  rfl

/-- The audited CTblLib candidate sends the first ambient row to the
frequency-zero linear local row. -/
@[simp]
theorem alternatingSixThreeCTblLibCandidate_trivialRow :
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv
        alternatingSixThreeTrivialPPrimeRow =
      Sum.inl 0 := by
  simpa [alternatingSixThreeTrivialPPrimeRow,
    alternatingSixAmbientThreePPrimeRowIndexEquiv,
    alternatingSixThreeConcreteNormalizerRowIndexEquiv,
    alternatingSixCTblLibThreePPrimeActionData] using
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv_ordered
      (0 : Fin 12)

private theorem cyclicEightLinearHom_zero :
    CyclicEight.linearHom (0 : Fin 8) = 1 := by
  apply MonoidHom.ext
  intro c
  change
    QuaternionGroup.zmodPower
        (CyclicEight.eighthRootParameter 0)
        (CyclicEight.eighthRootParameter_pow_eight 0)
        (Multiplicative.toAdd c) =
      1
  obtain ⟨z, hz⟩ :=
    ZMod.intCast_surjective (Multiplicative.toAdd c)
  rw [← hz, QuaternionGroup.zmodPower_intCast]
  simp [CyclicEight.eighthRootParameter]

/-- The frequency-zero coordinate linear character is intrinsically
trivial. -/
theorem alternatingSixThreeCoordinateLinearZeroCharacter_eq :
    AlternatingSixThreeNormalizer.coordinateLinearCharacter 0 =
      IrreducibleCharacter.trivial
        AlternatingSixThreeNormalizerCoordinates := by
  rw [AlternatingSixThreeNormalizer.coordinateLinearCharacter,
    IrreducibleCharacter.linear_eq_trivial_iff]
  apply MonoidHom.ext
  intro x
  simp [AlternatingSixThreeNormalizer.coordinateQuotientLinearHom,
    cyclicEightLinearHom_zero]

/-- Transporting the frequency-zero row to the actual fixed normalizer
preserves its intrinsic triviality. -/
theorem alternatingSixThreeActualNormalizerLinearZeroCharacter_eq :
    (AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
        (Sum.inl (0 : Fin 8))).1 =
      IrreducibleCharacter.trivial
        AlternatingSixUniversalCoverThreeNormalizer := by
  apply IrreducibleCharacter.ext
  funext g
  obtain ⟨x, rfl⟩ :=
    alternatingSixThreeNormalizerCoordinatesEquivUniversalCoverNormalizer.surjective g
  rw [
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv_values]
  change
    (AlternatingSixThreeNormalizer.coordinateLinearCharacter 0).values x =
      1
  rw [alternatingSixThreeCoordinateLinearZeroCharacter_eq]
  rfl

/-- Conditional on the already-isolated genuine equivariance obligation
for the audited CTblLib ordinary-row candidate, the first row carries the
complete exact-normalizer projective data.

The projective part itself is unconditional: the only parameter is exactly
the ordinary candidate-equivariance bridge required to construct the
underlying ordinary McKay equivalence. -/
def alternatingSixThreeCTblLibCandidateTrivialProjectiveRowData
    (h :
      AlternatingSixThreeCTblLibCandidateEquivariant
        alternatingSixAmbientOrdinaryCharacterTableCertificate) :
    let d :=
      alternatingSixThreeCTblLibCandidateConcreteCharacterTableCertificate
        alternatingSixAmbientOrdinaryCharacterTableCertificate h
    ExactNormalizerProjectiveRowData
      d.toEquivariantMcKayEquiv
      (d.ambientEnumeration alternatingSixThreeTrivialPPrimeRow) := by
  let d :=
    alternatingSixThreeCTblLibCandidateConcreteCharacterTableCertificate
      alternatingSixAmbientOrdinaryCharacterTableCertificate h
  apply ExactNormalizerProjectiveRowData.ofTrivialCharacters
  · exact alternatingSixThreeAmbientTrivialCharacter_eq
  · change
      (d.toEquivariantMcKayEquiv
          (d.ambientEnumeration
            alternatingSixThreeTrivialPPrimeRow)).1 =
        IrreducibleCharacter.trivial
          AlternatingSixUniversalCoverThreeNormalizer
    rw [d.toEquivariantMcKayEquiv_apply_enumerated]
    change
      (AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
          (alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv
            alternatingSixThreeTrivialPPrimeRow)).1 =
        IrreducibleCharacter.trivial
          AlternatingSixUniversalCoverThreeNormalizer
    rw [alternatingSixThreeCTblLibCandidate_trivialRow]
    exact alternatingSixThreeActualNormalizerLinearZeroCharacter_eq

end InductiveMcKay
end McKayConjecture
