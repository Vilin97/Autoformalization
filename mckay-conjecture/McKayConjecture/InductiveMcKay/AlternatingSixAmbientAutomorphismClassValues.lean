/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAutomorphismAction
import McKayConjecture.InductiveMcKay.AlternatingSixOuterConjugacyClassAction

/-!
# Character values under the audited `6.A₆` automorphisms

The checked Schur-cover conjugacy certificate enumerates the conjugacy
classes of the canonical universal cover by `Fin 31`.  Under the
contragredient action on characters, an automorphism sends the value at
class `i` to the original character's value at the inverse image of `i`.

This file proves that semantic statement first for any Schur-coordinate
automorphism, then for rows of a completed ambient ordinary character table,
and finally for the two audited automorphisms.  It makes no identification
with CTblLib row indices or permutations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The canonical universal-cover representative of the checked conjugacy
class with index `i`. -/
def alternatingSixUniversalCoverClassRepresentative
    (i : Fin 31) :
    AlternatingSixUniversalCover :=
  alternatingSixSchurCoordinatesEquivUniversalCover
    (alternatingSixSchurClassRepresentative i)

/-- The transported checked class equivalence is represented by the
transported coordinate representative. -/
@[simp]
theorem alternatingSixUniversalCoverClassIndexEquiv_apply
    (i : Fin 31) :
    alternatingSixUniversalCoverClassIndexEquiv i =
      ConjClasses.mk
        (alternatingSixUniversalCoverClassRepresentative i) :=
  rfl

/-- Passing to the inverse automorphism gives the inverse checked
class-index permutation. -/
@[simp]
theorem alternatingSixSchurClassIndexPermutation_symm
    (α : MulAut AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndexPermutation α.symm =
      (alternatingSixSchurClassIndexPermutation α).symm :=
  rfl

/-- The checked class-index permutation of any Schur-coordinate
automorphism is the actual class action of its transport to the canonical
universal cover. -/
theorem alternatingSixSchurClassIndexPermutation_universalCover
    (α : MulAut AlternatingSixSchurCoordinates)
    (i : Fin 31) :
    alternatingSixUniversalCoverClassIndexEquiv
        (alternatingSixSchurClassIndexPermutation α i) =
      ConjClasses.map
        (MulAut.congr
          alternatingSixSchurCoordinatesEquivUniversalCover α).toMonoidHom
        (alternatingSixUniversalCoverClassIndexEquiv i) := by
  rw [alternatingSixUniversalCoverClassIndexEquiv,
    Equiv.trans_apply, Equiv.trans_apply,
    alternatingSixSchurClassIndexPermutation_class]
  exact
    conjugacyClassesEquivOfMulEquiv_map_congr
      alternatingSixSchurCoordinatesEquivUniversalCover α
      (alternatingSixSchurCoordinateConjugacyClassEquiv i)

/-- Under the contragredient action on irreducible characters, the value at
checked class `i` becomes the source character's value at the representative
of the inverse class-index image. -/
theorem alternatingSixSchurAutomorphism_smul_values_classRepresentative
    (α : MulAut AlternatingSixSchurCoordinates)
    (χ : IrreducibleCharacter AlternatingSixUniversalCover)
    (i : Fin 31) :
    ((MulAut.congr
        alternatingSixSchurCoordinatesEquivUniversalCover α) • χ).values
          (alternatingSixUniversalCoverClassRepresentative i) =
      χ.values
        (alternatingSixUniversalCoverClassRepresentative
          ((alternatingSixSchurClassIndexPermutation α).symm i)) := by
  rw [IrreducibleCharacter.smul_values]
  apply IrreducibleCharacter.values_eq_of_isConj
  rw [← ConjClasses.mk_eq_mk_iff_isConj]
  calc
    ConjClasses.mk
          ((MulAut.congr
            alternatingSixSchurCoordinatesEquivUniversalCover α).symm
              (alternatingSixUniversalCoverClassRepresentative i)) =
        ConjClasses.map
          (MulAut.congr
            alternatingSixSchurCoordinatesEquivUniversalCover
            α.symm).toMonoidHom
          (alternatingSixUniversalCoverClassIndexEquiv i) := by
            rfl
    _ =
        alternatingSixUniversalCoverClassIndexEquiv
          (alternatingSixSchurClassIndexPermutation α.symm i) :=
      (alternatingSixSchurClassIndexPermutation_universalCover
        α.symm i).symm
    _ =
        ConjClasses.mk
          (alternatingSixUniversalCoverClassRepresentative
            ((alternatingSixSchurClassIndexPermutation α).symm i)) := by
      rfl

/-- The semantic prime-to-`p` row action attached to a completed ambient
table satisfies the inverse-class value formula for any transported
Schur-coordinate automorphism. -/
theorem
    alternatingSixAmbientPPrimeRowPermutation_values_classRepresentative_ofSchur
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (α : MulAut AlternatingSixSchurCoordinates)
    (r : AlternatingSixAmbientPPrimeRowIndex p)
    (i : Fin 31) :
    (alternatingSixAmbientPPrimeCharacterEquiv T p
        (alternatingSixAmbientPPrimeRowPermutation T p
          (MulAut.congr
            alternatingSixSchurCoordinatesEquivUniversalCover α) r)).1.values
          (alternatingSixUniversalCoverClassRepresentative i) =
      (alternatingSixAmbientPPrimeCharacterEquiv T p r).1.values
        (alternatingSixUniversalCoverClassRepresentative
          ((alternatingSixSchurClassIndexPermutation α).symm i)) := by
  rw [alternatingSixAmbientPPrimeRowPermutation_character]
  exact
    alternatingSixSchurAutomorphism_smul_values_classRepresentative
      α (alternatingSixAmbientPPrimeCharacterEquiv T p r).1 i

/-- The preceding semantic formula expressed directly in terms of the
completed table rows. -/
theorem
    alternatingSixAmbientPPrimeTableRowPermutation_values_classRepresentative_ofSchur
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (α : MulAut AlternatingSixSchurCoordinates)
    (r : AlternatingSixAmbientPPrimeRowIndex p)
    (i : Fin 31) :
    (T.toFiniteCharacterTableCertificate.character
        (alternatingSixAmbientPPrimeRowPermutation T p
          (MulAut.congr
            alternatingSixSchurCoordinatesEquivUniversalCover α) r).1).values
          (alternatingSixUniversalCoverClassRepresentative i) =
      (T.toFiniteCharacterTableCertificate.character r.1).values
        (alternatingSixUniversalCoverClassRepresentative
          ((alternatingSixSchurClassIndexPermutation α).symm i)) := by
  simpa only [
    alternatingSixAmbientPPrimeCharacterEquiv_apply_val
  ] using
    alternatingSixAmbientPPrimeRowPermutation_values_classRepresentative_ofSchur
      T p α r i

/-- The first audited semantic row permutation acts on table values by the
inverse of its certified conjugacy-class permutation. -/
theorem
    alternatingSixAmbientPPrimeAlphaOneRowPermutation_values_classRepresentative
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (r : AlternatingSixAmbientPPrimeRowIndex p)
    (i : Fin 31) :
    (T.toFiniteCharacterTableCertificate.character
        (alternatingSixAmbientPPrimeAlphaOneRowPermutation T p r).1).values
          (alternatingSixUniversalCoverClassRepresentative i) =
      (T.toFiniteCharacterTableCertificate.character r.1).values
        (alternatingSixUniversalCoverClassRepresentative
          (alternatingSixAlphaOneConjugacyClassPermutation.symm i)) := by
  simpa only [
    alternatingSixAmbientPPrimeAlphaOneRowPermutation,
    alternatingSixUniversalCoverTransportedAlphaOne,
    alternatingSixUniversalCoverAutomorphismOfSchur,
    alternatingSixAlphaOneConjugacyClassPermutation
  ] using
    alternatingSixAmbientPPrimeTableRowPermutation_values_classRepresentative_ofSchur
      T p alternatingSixSchurAlphaOneAutomorphism r i

/-- The second audited semantic row permutation acts on table values by the
inverse of its certified conjugacy-class permutation. -/
theorem
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation_values_classRepresentative
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (r : AlternatingSixAmbientPPrimeRowIndex p)
    (i : Fin 31) :
    (T.toFiniteCharacterTableCertificate.character
        (alternatingSixAmbientPPrimeAlphaTwoRowPermutation T p r).1).values
          (alternatingSixUniversalCoverClassRepresentative i) =
      (T.toFiniteCharacterTableCertificate.character r.1).values
        (alternatingSixUniversalCoverClassRepresentative
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm i)) := by
  simpa only [
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
    alternatingSixUniversalCoverTransportedAlphaTwo,
    alternatingSixUniversalCoverAutomorphismOfSchur,
    alternatingSixAlphaTwoConjugacyClassPermutation
  ] using
    alternatingSixAmbientPPrimeTableRowPermutation_values_classRepresentative_ofSchur
      T p alternatingSixSchurAlphaTwoAutomorphism r i

end InductiveMcKay
end McKayConjecture
