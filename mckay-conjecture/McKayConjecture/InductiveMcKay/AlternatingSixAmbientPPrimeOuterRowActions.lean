/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterRowActions
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeCharacterEnumeration
import McKayConjecture.InductiveMcKay.AlternatingSixOuterSylowAdjustment

/-!
# Outer automorphisms on the prime-to-`p` ambient rows of `6.A₆`

The two canonical outer automorphisms preserve character degree, so their
proved permutations of all thirty-one ordinary rows restrict to every
arithmetic prime-to-`p` row subtype.

This file also identifies those restricted permutations with the genuine
character action of both the canonical automorphisms and their selected
Sylow-stabilizing inner adjustments.  It is independent of CTblLib row
numbers and of any proposed ambient-to-local row matching.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The first canonical outer row permutation restricted to rows of degree
prime to `p`. -/
def alternatingSixAmbientAlphaOnePPrimeRowAction
    (p : ℕ) :
    Equiv.Perm (AlternatingSixAmbientPPrimeRowIndex p) :=
  alternatingSixAmbientAlphaOneOrdinaryRowAction.subtypePerm
    (fun row => by
      rw [alternatingSixAmbientAlphaOneOrdinaryRowAction_dimension])

/-- The second canonical outer row permutation restricted to rows of degree
prime to `p`. -/
def alternatingSixAmbientAlphaTwoPPrimeRowAction
    (p : ℕ) :
    Equiv.Perm (AlternatingSixAmbientPPrimeRowIndex p) :=
  alternatingSixAmbientAlphaTwoOrdinaryRowAction.subtypePerm
    (fun row => by
      rw [alternatingSixAmbientAlphaTwoOrdinaryRowAction_dimension])

@[simp]
theorem alternatingSixAmbientAlphaOnePPrimeRowAction_val
    (p : ℕ)
    (row : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientAlphaOnePPrimeRowAction p row).1 =
      alternatingSixAmbientAlphaOneOrdinaryRowAction row.1 :=
  rfl

@[simp]
theorem alternatingSixAmbientAlphaTwoPPrimeRowAction_val
    (p : ℕ)
    (row : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientAlphaTwoPPrimeRowAction p row).1 =
      alternatingSixAmbientAlphaTwoOrdinaryRowAction row.1 :=
  rfl

/-- The table-induced prime-to-`p` enumeration transports the first
canonical automorphism to the restricted named-row permutation. -/
theorem
    alternatingSixAmbientPPrimeCharacterAction_alphaOne
    (p : ℕ)
    (row : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeCharacterEquiv
          alternatingSixAmbientOrdinaryCharacterTableCertificate p).symm
        (alternatingSixUniversalCoverAlphaOneAutomorphism •
          alternatingSixAmbientPPrimeCharacterEquiv
            alternatingSixAmbientOrdinaryCharacterTableCertificate p row) =
      alternatingSixAmbientAlphaOnePPrimeRowAction p row := by
  apply
    (alternatingSixAmbientPPrimeCharacterEquiv
      alternatingSixAmbientOrdinaryCharacterTableCertificate p).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change
    alternatingSixUniversalCoverAlphaOneAutomorphism •
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character row.1) =
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          (alternatingSixAmbientAlphaOneOrdinaryRowAction row.1))
  calc
    alternatingSixUniversalCoverAlphaOneAutomorphism •
          (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character row.1) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character
            (alternatingSixAmbientOrdinaryRowAutomorphismAction
              alternatingSixAmbientOrdinaryCharacterTableCertificate
              alternatingSixUniversalCoverAlphaOneAutomorphism row.1)) :=
      (alternatingSixAmbientOrdinaryRowAutomorphismAction_character
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        alternatingSixUniversalCoverAlphaOneAutomorphism row.1).symm
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character
            (alternatingSixAmbientAlphaOneOrdinaryRowAction row.1)) := by
      rw [alternatingSixAmbientAlphaOneOrdinaryRowAction_eq]

/-- The table-induced prime-to-`p` enumeration transports the second
canonical automorphism to the restricted named-row permutation. -/
theorem
    alternatingSixAmbientPPrimeCharacterAction_alphaTwo
    (p : ℕ)
    (row : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeCharacterEquiv
          alternatingSixAmbientOrdinaryCharacterTableCertificate p).symm
        (alternatingSixUniversalCoverAlphaTwoAutomorphism •
          alternatingSixAmbientPPrimeCharacterEquiv
            alternatingSixAmbientOrdinaryCharacterTableCertificate p row) =
      alternatingSixAmbientAlphaTwoPPrimeRowAction p row := by
  apply
    (alternatingSixAmbientPPrimeCharacterEquiv
      alternatingSixAmbientOrdinaryCharacterTableCertificate p).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change
    alternatingSixUniversalCoverAlphaTwoAutomorphism •
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character row.1) =
      (alternatingSixAmbientOrdinaryCharacterTableCertificate
        |>.toFiniteCharacterTableCertificate.character
          (alternatingSixAmbientAlphaTwoOrdinaryRowAction row.1))
  calc
    alternatingSixUniversalCoverAlphaTwoAutomorphism •
          (alternatingSixAmbientOrdinaryCharacterTableCertificate
            |>.toFiniteCharacterTableCertificate.character row.1) =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character
            (alternatingSixAmbientOrdinaryRowAutomorphismAction
              alternatingSixAmbientOrdinaryCharacterTableCertificate
              alternatingSixUniversalCoverAlphaTwoAutomorphism row.1)) :=
      (alternatingSixAmbientOrdinaryRowAutomorphismAction_character
        alternatingSixAmbientOrdinaryCharacterTableCertificate
        alternatingSixUniversalCoverAlphaTwoAutomorphism row.1).symm
    _ =
        (alternatingSixAmbientOrdinaryCharacterTableCertificate
          |>.toFiniteCharacterTableCertificate.character
            (alternatingSixAmbientAlphaTwoOrdinaryRowAction row.1)) := by
      rw [alternatingSixAmbientAlphaTwoOrdinaryRowAction_eq]

/-- Inner adjustment to a fixed Sylow subgroup does not change the first
canonical automorphism's action on ambient prime-to-`p` rows. -/
theorem
    alternatingSixAmbientPPrimeCharacterAction_sylowAdjustedAlphaOne
    (p : ℕ) [Fact p.Prime]
    (row : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeCharacterEquiv
          alternatingSixAmbientOrdinaryCharacterTableCertificate p).symm
        (alternatingSixUniversalCoverSylowAdjustedAlphaOne p •
          alternatingSixAmbientPPrimeCharacterEquiv
            alternatingSixAmbientOrdinaryCharacterTableCertificate p row) =
      alternatingSixAmbientAlphaOnePPrimeRowAction p row := by
  simpa [alternatingSixUniversalCoverSylowAdjustedAlphaOne] using
    alternatingSixAmbientPPrimeCharacterAction_alphaOne p row

/-- Inner adjustment to a fixed Sylow subgroup does not change the second
canonical automorphism's action on ambient prime-to-`p` rows. -/
theorem
    alternatingSixAmbientPPrimeCharacterAction_sylowAdjustedAlphaTwo
    (p : ℕ) [Fact p.Prime]
    (row : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeCharacterEquiv
          alternatingSixAmbientOrdinaryCharacterTableCertificate p).symm
        (alternatingSixUniversalCoverSylowAdjustedAlphaTwo p •
          alternatingSixAmbientPPrimeCharacterEquiv
            alternatingSixAmbientOrdinaryCharacterTableCertificate p row) =
      alternatingSixAmbientAlphaTwoPPrimeRowAction p row := by
  simpa [alternatingSixUniversalCoverSylowAdjustedAlphaTwo] using
    alternatingSixAmbientPPrimeCharacterAction_alphaTwo p row

end InductiveMcKay
end McKayConjecture
