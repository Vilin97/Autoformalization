/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAutomorphismAction
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeOuterRowActions

/-!
# Compatibility of the two ambient outer-row action APIs

The semantic prime-to-`p` row permutations were defined by transporting the
action of the two audited automorphisms through a completed character table.
The completed ambient calculation independently determines the same actions
as explicit permutations of the thirty-one named ordinary rows.

This file identifies the two APIs for every prime parameter.  It also records
the corresponding statements after the inner corrections used to stabilize a
chosen Sylow subgroup.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The first audited automorphism used by the semantic row-action API is the
canonical coordinate automorphism used by the completed named-row action. -/
theorem alternatingSixUniversalCoverTransportedAlphaOne_eq_canonical :
    alternatingSixUniversalCoverTransportedAlphaOne =
      GroupTheory.alternatingSixUniversalCoverAlphaOneAutomorphism := by
  ext element
  rfl

/-- The second audited automorphism used by the semantic row-action API is the
canonical coordinate automorphism used by the completed named-row action. -/
theorem alternatingSixUniversalCoverTransportedAlphaTwo_eq_canonical :
    alternatingSixUniversalCoverTransportedAlphaTwo =
      GroupTheory.alternatingSixUniversalCoverAlphaTwoAutomorphism := by
  ext element
  rfl

/-- For every `p`, the semantic first outer action obtained from the completed
ambient table is exactly the restriction of the named ordinary-row action. -/
theorem alternatingSixAmbientPPrimeAlphaOneRowPermutation_eq_canonical
    (p : ℕ) :
    alternatingSixAmbientPPrimeAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate p =
      alternatingSixAmbientAlphaOnePPrimeRowAction p := by
  apply Equiv.ext
  intro row
  change
    (alternatingSixAmbientPPrimeCharacterEquiv
          alternatingSixAmbientOrdinaryCharacterTableCertificate p).symm
        (alternatingSixUniversalCoverTransportedAlphaOne •
          alternatingSixAmbientPPrimeCharacterEquiv
            alternatingSixAmbientOrdinaryCharacterTableCertificate p row) =
      alternatingSixAmbientAlphaOnePPrimeRowAction p row
  rw [alternatingSixUniversalCoverTransportedAlphaOne_eq_canonical]
  exact alternatingSixAmbientPPrimeCharacterAction_alphaOne p row

/-- For every `p`, the semantic second outer action obtained from the completed
ambient table is exactly the restriction of the named ordinary-row action. -/
theorem alternatingSixAmbientPPrimeAlphaTwoRowPermutation_eq_canonical
    (p : ℕ) :
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate p =
      alternatingSixAmbientAlphaTwoPPrimeRowAction p := by
  apply Equiv.ext
  intro row
  change
    (alternatingSixAmbientPPrimeCharacterEquiv
          alternatingSixAmbientOrdinaryCharacterTableCertificate p).symm
        (alternatingSixUniversalCoverTransportedAlphaTwo •
          alternatingSixAmbientPPrimeCharacterEquiv
            alternatingSixAmbientOrdinaryCharacterTableCertificate p row) =
      alternatingSixAmbientAlphaTwoPPrimeRowAction p row
  rw [alternatingSixUniversalCoverTransportedAlphaTwo_eq_canonical]
  exact alternatingSixAmbientPPrimeCharacterAction_alphaTwo p row

/-- Inner correction to a chosen Sylow subgroup leaves the canonical first
named-row action unchanged. -/
theorem alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq_canonical
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate P =
      alternatingSixAmbientAlphaOnePPrimeRowAction p := by
  rw [alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq,
    alternatingSixAmbientPPrimeAlphaOneRowPermutation_eq_canonical]

/-- Inner correction to a chosen Sylow subgroup leaves the canonical second
named-row action unchanged. -/
theorem alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq_canonical
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
        alternatingSixAmbientOrdinaryCharacterTableCertificate P =
      alternatingSixAmbientAlphaTwoPPrimeRowAction p := by
  rw [alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq,
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation_eq_canonical]

end InductiveMcKay
end McKayConjecture
