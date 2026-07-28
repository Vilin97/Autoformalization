/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeRowIndexData

/-!
# Arithmetic ambient rows as certified prime-to-`p` character rows

A completed ordinary character table for the canonical sixfold cover has two
apparently different prime-to-`p` row subtypes:

* `AlternatingSixAmbientPPrimeRowIndex p`, filtered using the recorded matrix
  dimension; and
* the generic `FiniteCharacterTableCertificate.PPrimeRow p`, filtered using
  the degree of the certified irreducible character.

The row certificate identifies these dimensions, so the two subtypes are
canonically equivalent by the identity map on the underlying ordinary row.
Composing with the completed table gives the ambient character enumeration
needed by a finite McKay certificate.

This file does not construct a completed ambient ordinary table and does not
match ambient rows with local rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The arithmetic and certified prime-to-`p` row filters agree for a
completed ambient ordinary character table.  The equivalence is the identity
on the underlying ordinary-row index. -/
def alternatingSixAmbientPPrimeRowIndexEquivTablePPrimeRow
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ) :
    AlternatingSixAmbientPPrimeRowIndex p ≃
      T.toFiniteCharacterTableCertificate.PPrimeRow p where
  toFun r :=
    ⟨r.1, by
      rw [
        T.toFiniteCharacterTableCertificate.mem_pPrimeRow_iff]
      simpa using
        (T.row r.1).representation_finrank ▸ r.2⟩
  invFun r :=
    ⟨r.1, by
      have hr := r.2
      rw [
        T.toFiniteCharacterTableCertificate.mem_pPrimeRow_iff] at hr
      simpa using
        (T.row r.1).representation_finrank ▸ hr⟩
  left_inv r := by
    apply Subtype.ext
    rfl
  right_inv r := by
    apply Subtype.ext
    rfl

@[simp]
theorem alternatingSixAmbientPPrimeRowIndexEquivTablePPrimeRow_val
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeRowIndexEquivTablePPrimeRow T p r).1 =
      r.1 :=
  rfl

/-- A supplied completed ordinary table enumerates its prime-to-`p` ambient
characters by the arithmetic matrix-row subtype. -/
def alternatingSixAmbientPPrimeCharacterEquiv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ) :
    AlternatingSixAmbientPPrimeRowIndex p ≃
      PPrimeIrreducibleCharacter AlternatingSixUniversalCover p :=
  (alternatingSixAmbientPPrimeRowIndexEquivTablePPrimeRow T p).trans
    (T.pPrimeIrreducibleCharacterEquiv p)

@[simp]
theorem alternatingSixAmbientPPrimeCharacterEquiv_apply_val
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeCharacterEquiv T p r).1 =
      T.toFiniteCharacterTableCertificate.character r.1 :=
  rfl

/-- The table-induced ambient enumeration preserves the recorded matrix
dimension as the degree of the certified irreducible character. -/
@[simp]
theorem alternatingSixAmbientPPrimeCharacterEquiv_degree
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeCharacterEquiv T p r).1.degree =
      r.1.dimension := by
  rw [alternatingSixAmbientPPrimeCharacterEquiv_apply_val,
    FiniteCharacterTableCertificate.character_degree]
  exact (T.row r.1).representation_finrank

/-- The arithmetic prime-to-`p` enumeration retains the exact advertised
central value of each ambient row. -/
theorem alternatingSixAmbientPPrimeCharacterEquiv_values_centralGenerator
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeCharacterEquiv T p r).1.values
        alternatingSixAmbientCanonicalCentralGenerator =
      ((alternatingSixAmbientPPrimeCharacterEquiv T p r).1.degree : ℂ) *
        alternatingSixComplexCyclotomicRoot ^
          r.1.scalarPattern.exponent 0 := by
  rw [
    alternatingSixAmbientPPrimeCharacterEquiv_degree,
    alternatingSixAmbientPPrimeCharacterEquiv_apply_val,
    T.character_values_centralGenerator
  ]

end InductiveMcKay
end McKayConjecture
