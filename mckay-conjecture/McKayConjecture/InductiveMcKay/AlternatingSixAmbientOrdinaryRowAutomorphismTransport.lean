/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Automorphism
import McKayConjecture.Character.InverseConjugate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterTable

/-!
# Transporting completed ordinary rows by automorphisms

A complete ordinary table canonically transports the genuine automorphism
action on irreducible characters back to its finite row type.  This file
packages that general construction and its uniqueness properties; it is
independent of the explicit `A₆` outer-action calculation.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The ordinary row reached by transporting its certified irreducible
character through an automorphism of the canonical sixfold cover. -/
def alternatingSixAmbientOrdinaryRowAutomorphismAction
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (row : AlternatingSixAmbientOrdinaryRow) :
    AlternatingSixAmbientOrdinaryRow :=
  T.toFiniteCharacterTableCertificate.irreducibleCharacterEquiv.symm
    (a • T.toFiniteCharacterTableCertificate.character row)

/-- The transported row enumerates exactly the transported character. -/
theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_character
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (row : AlternatingSixAmbientOrdinaryRow) :
    T.toFiniteCharacterTableCertificate.character
        (alternatingSixAmbientOrdinaryRowAutomorphismAction T a row) =
      a • T.toFiniteCharacterTableCertificate.character row := by
  exact
    T.toFiniteCharacterTableCertificate.irreducibleCharacterEquiv
      |>.apply_symm_apply _

/-- A proposed row is the transported row exactly when its certified
character is the transported character. -/
theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_iff
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (row target : AlternatingSixAmbientOrdinaryRow) :
    alternatingSixAmbientOrdinaryRowAutomorphismAction T a row = target ↔
      a • T.toFiniteCharacterTableCertificate.character row =
        T.toFiniteCharacterTableCertificate.character target := by
  constructor
  · intro h
    rw [← h]
    exact
      (alternatingSixAmbientOrdinaryRowAutomorphismAction_character
        T a row).symm
  · intro h
    apply T.row_injective
    change
      T.toFiniteCharacterTableCertificate.character
          (alternatingSixAmbientOrdinaryRowAutomorphismAction T a row) =
        T.toFiniteCharacterTableCertificate.character target
    exact
      (alternatingSixAmbientOrdinaryRowAutomorphismAction_character
        T a row).trans h

/-- Character equality proves the corresponding explicit row-action
identity. -/
theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_of_character
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (row target : AlternatingSixAmbientOrdinaryRow)
    (h :
      a • T.toFiniteCharacterTableCertificate.character row =
        T.toFiniteCharacterTableCertificate.character target) :
    alternatingSixAmbientOrdinaryRowAutomorphismAction T a row = target :=
  (alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_iff
    T a row target).2 h

@[simp]
theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_one
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (row : AlternatingSixAmbientOrdinaryRow) :
    alternatingSixAmbientOrdinaryRowAutomorphismAction T 1 row = row := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_of_character
  simp

theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_mul
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a b : MulAut AlternatingSixUniversalCover)
    (row : AlternatingSixAmbientOrdinaryRow) :
    alternatingSixAmbientOrdinaryRowAutomorphismAction T (a * b) row =
      alternatingSixAmbientOrdinaryRowAutomorphismAction T a
        (alternatingSixAmbientOrdinaryRowAutomorphismAction T b row) := by
  apply
    alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_of_character
  rw [
    alternatingSixAmbientOrdinaryRowAutomorphismAction_character,
    alternatingSixAmbientOrdinaryRowAutomorphismAction_character,
    mul_smul
  ]

/-- The degree of a certified ordinary character is its recorded matrix
dimension. -/
@[simp]
theorem alternatingSixAmbientOrdinaryCharacter_degree
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (row : AlternatingSixAmbientOrdinaryRow) :
    (T.toFiniteCharacterTableCertificate.character row).degree =
      row.dimension := by
  rw [FiniteCharacterTableCertificate.character_degree]
  exact (T.row row).representation_finrank

/-- The value at the inverse central generator is the degree times the
inverse of the advertised central scalar. -/
theorem alternatingSixAmbientOrdinaryCharacter_values_centralGenerator_inv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (row : AlternatingSixAmbientOrdinaryRow) :
    (T.toFiniteCharacterTableCertificate.character row).values
        alternatingSixAmbientCanonicalCentralGenerator⁻¹ =
      (row.dimension : ℂ) *
        (alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0)⁻¹ := by
  rw [
    IrreducibleCharacter.value_inv_eq_conj,
    T.character_values_centralGenerator
  ]
  have hnorm :
      ‖alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0‖ = 1 := by
    rw [norm_pow,
      alternatingSixComplexCyclotomicRoot_isPrimitive.norm'_eq_one]
    · exact one_pow _
    · norm_num
  rw [map_mul, map_natCast,
    ← Complex.inv_eq_conj hnorm]

/-- Automorphism transport preserves the recorded row dimension. -/
@[simp]
theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_dimension
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (row : AlternatingSixAmbientOrdinaryRow) :
    (alternatingSixAmbientOrdinaryRowAutomorphismAction T a row).dimension =
      row.dimension := by
  have hdegree :=
    congrArg IrreducibleCharacter.degree
      (alternatingSixAmbientOrdinaryRowAutomorphismAction_character
        T a row)
  rw [IrreducibleCharacter.smul_degree] at hdegree
  exact
    (alternatingSixAmbientOrdinaryCharacter_degree T _).symm
      |>.trans
        (hdegree.trans
          (alternatingSixAmbientOrdinaryCharacter_degree T row))

end InductiveMcKay
end McKayConjecture
