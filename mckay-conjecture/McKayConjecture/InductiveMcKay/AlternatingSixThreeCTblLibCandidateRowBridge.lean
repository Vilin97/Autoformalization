/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixCTblLibOuterActionData
import McKayConjecture.InductiveMcKay.AlternatingSixThreeDisplayedRowBridgeEquivariance

/-!
# The audited CTblLib candidate bridge for the three-local `A₆` rows

The existing display-order bridge identifies equal positions in the
project's ambient and local row enumerations.  The independently audited
CTblLib correspondence at `p = 3` is not the identity on its display
positions.  This file therefore records a separate row equivalence obtained
by inserting the audited candidate permutation.

The remaining proposition uses the genuine actions transported through the
project's proved character enumerations.  It is deliberately not proved
from the finite CTblLib audit: doing so requires semantic identifications
between the CTblLib positions and the constructed character rows, followed
by a full Sylow-stabilizer generation theorem.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeCTblLibCandidateFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- Insert the audited CTblLib `p = 3` candidate between the project's
ordered ambient and concrete local row enumerations.

This is an explicit candidate equivalence, not yet a proved equivariant
McKay correspondence. -/
def alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv :
    AlternatingSixAmbientPPrimeRowIndex 3 ≃
      AlternatingSixThreeConcreteNormalizerRow :=
  alternatingSixAmbientThreePPrimeRowIndexEquiv.symm |>.trans
    (alternatingSixCTblLibThreePPrimeActionData.candidate.trans
      alternatingSixThreeConcreteNormalizerRowIndexEquiv)

/-- On ordered positions, the new bridge is exactly the audited candidate
permutation. -/
@[simp]
theorem alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv_ordered
    (i : Fin 12) :
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv
        (alternatingSixAmbientThreePPrimeRowIndexEquiv i) =
      alternatingSixThreeConcreteNormalizerRowIndexEquiv
        (alternatingSixCTblLibThreePPrimeActionData.candidate i) := by
  simp [alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv]

/-- The audited candidate is genuinely different from the positionwise
display-order bridge. -/
theorem alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv_ne_displayed :
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv ≠
      alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv := by
  intro h
  have hAtOne :=
    Equiv.congr_fun h
      (alternatingSixAmbientThreePPrimeRowIndexEquiv (1 : Fin 12))
  have hCandidate :
      alternatingSixCTblLibThreePPrimeActionData.candidate (1 : Fin 12) =
        (1 : Fin 12) := by
    apply alternatingSixThreeConcreteNormalizerRowIndexEquiv.injective
    simpa only [
      alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv_ordered,
      alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv_ordered
    ] using hAtOne
  have hValue := congrArg Fin.val hCandidate
  norm_num [alternatingSixCTblLibThreePPrimeActionData] at hValue

/-- Equal display positions do not intertwine the two audited `p = 3`
generator actions.  This finite fact is independent of the still-missing
semantic identification of CTblLib positions with Lean character rows. -/
theorem
    alternatingSixCTblLibThree_displayIdentity_not_generatorEquivariant :
    ¬((∀ i : Fin 12,
          alternatingSixCTblLibThreePPrimeActionData.ambientAlphaOne i =
            alternatingSixCTblLibThreePPrimeActionData.localAlphaOne i) ∧
        ∀ i : Fin 12,
          alternatingSixCTblLibThreePPrimeActionData.ambientAlphaTwo i =
            alternatingSixCTblLibThreePPrimeActionData.localAlphaTwo i) := by
  decide

/-- The exact genuine-action obligation for the audited candidate bridge. -/
def AlternatingSixThreeCTblLibCandidateEquivariant
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) : Prop :=
  ∀ (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixAmbientPPrimeRowIndex 3),
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv
        (alternatingSixThreeAmbientRowStabilizerAction T a r) =
      alternatingSixThreeLocalRowStabilizerAction a
        (alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv r)

/-- Package a proof of the genuine-action obligation into the existing
three-local finite character-table interface. -/
def alternatingSixThreeCTblLibCandidateConcreteCharacterTableCertificate
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixThreeCTblLibCandidateEquivariant T) :
    AlternatingSixThreeConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 3) where
  ambientEnumeration :=
    alternatingSixAmbientPPrimeCharacterEquiv T 3
  indexEquiv :=
    alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv
  indexEquivariance := by
    intro a r
    exact h a r

@[simp]
theorem
    alternatingSixThreeCTblLibCandidateConcreteCharacterTableCertificate_ambientEnumeration
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixThreeCTblLibCandidateEquivariant T) :
    (alternatingSixThreeCTblLibCandidateConcreteCharacterTableCertificate T h).ambientEnumeration =
      alternatingSixAmbientPPrimeCharacterEquiv T 3 :=
  rfl

@[simp]
theorem
    alternatingSixThreeCTblLibCandidateConcreteCharacterTableCertificate_indexEquiv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixThreeCTblLibCandidateEquivariant T) :
    (alternatingSixThreeCTblLibCandidateConcreteCharacterTableCertificate T h).indexEquiv =
      alternatingSixThreeCTblLibCandidateAmbientLocalRowEquiv :=
  rfl

end InductiveMcKay
end McKayConjecture
