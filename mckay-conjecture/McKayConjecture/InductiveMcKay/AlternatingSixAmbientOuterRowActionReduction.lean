/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAutomorphisms
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterRowActionSignature

/-!
# Reducing the ambient outer-row action to the paired rows

Degree and central scalar leave at most one competing row.  Consequently the
full 31-row action follows once a separating character value rules out that
single signature mate.  This is the common final step for both canonical
outer automorphisms; it avoids repeating the completed character table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- A character value different from the value on the signature mate rules
out that mate as the transported row. -/
theorem
    alternatingSixAmbientOrdinaryRowAutomorphismAction_ne_signatureMate_of_value_ne
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (row expected : AlternatingSixAmbientOrdinaryRow)
    (g : AlternatingSixUniversalCover)
    (hvalue :
      (a • T.toFiniteCharacterTableCertificate.character row).values g ≠
        (T.toFiniteCharacterTableCertificate.character
          (alternatingSixAmbientOrdinaryRowSignatureMate expected)).values g) :
    alternatingSixAmbientOrdinaryRowAutomorphismAction T a row ≠
      alternatingSixAmbientOrdinaryRowSignatureMate expected := by
  intro hmate
  apply hvalue
  rw [← alternatingSixAmbientOrdinaryRowAutomorphismAction_character,
    hmate]

/-- Degree and central-scalar signatures, together with one separating
value, identify a single transported row.  This pointwise form is useful
when one member of a paired signature is determined first and the other is
then forced by injectivity. -/
theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected_at
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (row expected : AlternatingSixAmbientOrdinaryRow)
    (hcentral :
      a.symm alternatingSixAmbientCanonicalCentralGenerator =
        alternatingSixAmbientCanonicalCentralGenerator⁻¹)
    (hdimension : expected.dimension = row.dimension)
    (hscalar :
      expected.scalarPattern =
        alternatingSixAmbientOuterScalarPattern row.scalarPattern)
    (hne :
      alternatingSixAmbientOrdinaryRowAutomorphismAction T a row ≠
        alternatingSixAmbientOrdinaryRowSignatureMate expected) :
    alternatingSixAmbientOrdinaryRowAutomorphismAction T a row =
      expected := by
  let target :=
    alternatingSixAmbientOrdinaryRowAutomorphismAction T a row
  have htargetDimension : target.dimension = expected.dimension := by
    rw [
      alternatingSixAmbientOrdinaryRowAutomorphismAction_dimension,
      hdimension
    ]
  have htargetScalar : target.scalarPattern = expected.scalarPattern := by
    rw [
      alternatingSixAmbientOrdinaryRowAutomorphismAction_scalarPattern
        T a hcentral,
      hscalar
    ]
  rcases
      alternatingSixAmbientOrdinaryRow_eq_or_eq_signatureMate
        expected target htargetDimension htargetScalar with
    htarget | hmate
  · exact htarget
  · exact (hne hmate).elim

/-- Automorphism transport is injective on the completed row labels. -/
theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_injective
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover) :
    Function.Injective
      (alternatingSixAmbientOrdinaryRowAutomorphismAction T a) := by
  intro row₁ row₂ hrows
  have hcharacters :=
    congrArg
      (T.toFiniteCharacterTableCertificate.character)
      hrows
  rw [
    alternatingSixAmbientOrdinaryRowAutomorphismAction_character,
    alternatingSixAmbientOrdinaryRowAutomorphismAction_character
  ] at hcharacters
  have hcancel :=
    congrArg
      (fun χ : IrreducibleCharacter AlternatingSixUniversalCover ↦
        a.symm • χ)
      hcharacters
  apply
    T.toFiniteCharacterTableCertificate
      |>.irreducibleCharacterEquiv.injective
  simpa [← mul_smul] using hcancel

/-- If a proposed row permutation has the forced degree and central-scalar
signatures, it is enough to exclude the one possible signature mate on each
genuinely paired row. -/
theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (expected : Equiv.Perm AlternatingSixAmbientOrdinaryRow)
    (hcentral :
      a.symm alternatingSixAmbientCanonicalCentralGenerator =
        alternatingSixAmbientCanonicalCentralGenerator⁻¹)
    (hdimension :
      ∀ row,
        (expected row).dimension = row.dimension)
    (hscalar :
      ∀ row,
        (expected row).scalarPattern =
          alternatingSixAmbientOuterScalarPattern row.scalarPattern)
    (hresolve :
      ∀ row,
        alternatingSixAmbientOrdinaryRowSignatureMate (expected row) ≠
            expected row →
          alternatingSixAmbientOrdinaryRowAutomorphismAction T a row ≠
            alternatingSixAmbientOrdinaryRowSignatureMate (expected row)) :
    ∀ row,
      alternatingSixAmbientOrdinaryRowAutomorphismAction T a row =
        expected row := by
  intro row
  have htargetDimension :
      (alternatingSixAmbientOrdinaryRowAutomorphismAction T a row).dimension =
        (expected row).dimension := by
    rw [
      alternatingSixAmbientOrdinaryRowAutomorphismAction_dimension,
      hdimension
    ]
  have htargetScalar :
      (alternatingSixAmbientOrdinaryRowAutomorphismAction T a row).scalarPattern =
        (expected row).scalarPattern := by
    rw [
      alternatingSixAmbientOrdinaryRowAutomorphismAction_scalarPattern
        T a hcentral,
      hscalar
    ]
  rcases
      alternatingSixAmbientOrdinaryRow_eq_or_eq_signatureMate
        (expected row)
        (alternatingSixAmbientOrdinaryRowAutomorphismAction T a row)
        htargetDimension htargetScalar with
    htarget | hmate
  · exact htarget
  · by_cases hfixed :
        alternatingSixAmbientOrdinaryRowSignatureMate (expected row) =
          expected row
    · exact hmate.trans hfixed
    · exact (hresolve row hfixed hmate).elim

/-- Conditional final row action for the first canonical outer
automorphism.  The remaining premise has content only on the eleven paired
degree/scalar signatures. -/
theorem alternatingSixAmbientAlphaOneOrdinaryRowAction_eq_of_mate_separation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hcentral :
      alternatingSixUniversalCoverAlphaOneAutomorphism.symm
          alternatingSixAmbientCanonicalCentralGenerator =
        alternatingSixAmbientCanonicalCentralGenerator⁻¹)
    (hresolve :
      ∀ row,
        alternatingSixAmbientOrdinaryRowSignatureMate
              (alternatingSixAmbientAlphaOneOrdinaryRowAction row) ≠
            alternatingSixAmbientAlphaOneOrdinaryRowAction row →
          alternatingSixAmbientOrdinaryRowAutomorphismAction T
              alternatingSixUniversalCoverAlphaOneAutomorphism row ≠
            alternatingSixAmbientOrdinaryRowSignatureMate
              (alternatingSixAmbientAlphaOneOrdinaryRowAction row)) :
    ∀ row,
      alternatingSixAmbientOrdinaryRowAutomorphismAction T
          alternatingSixUniversalCoverAlphaOneAutomorphism row =
        alternatingSixAmbientAlphaOneOrdinaryRowAction row := by
  apply alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected
    T alternatingSixUniversalCoverAlphaOneAutomorphism
    alternatingSixAmbientAlphaOneOrdinaryRowAction hcentral
  · exact alternatingSixAmbientAlphaOneOrdinaryRowAction_dimension
  · exact alternatingSixAmbientAlphaOneOrdinaryRowAction_scalarPattern
  · exact hresolve

/-- Conditional final row action for the second canonical outer
automorphism.  Its nontrivial degree-four and degree-five obligations are
discharged by the state-77/state-79 separator values. -/
theorem alternatingSixAmbientAlphaTwoOrdinaryRowAction_eq_of_mate_separation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hcentral :
      alternatingSixUniversalCoverAlphaTwoAutomorphism.symm
          alternatingSixAmbientCanonicalCentralGenerator =
        alternatingSixAmbientCanonicalCentralGenerator⁻¹)
    (hresolve :
      ∀ row,
        alternatingSixAmbientOrdinaryRowSignatureMate
              (alternatingSixAmbientAlphaTwoOrdinaryRowAction row) ≠
            alternatingSixAmbientAlphaTwoOrdinaryRowAction row →
          alternatingSixAmbientOrdinaryRowAutomorphismAction T
              alternatingSixUniversalCoverAlphaTwoAutomorphism row ≠
            alternatingSixAmbientOrdinaryRowSignatureMate
              (alternatingSixAmbientAlphaTwoOrdinaryRowAction row)) :
    ∀ row,
      alternatingSixAmbientOrdinaryRowAutomorphismAction T
          alternatingSixUniversalCoverAlphaTwoAutomorphism row =
        alternatingSixAmbientAlphaTwoOrdinaryRowAction row := by
  apply alternatingSixAmbientOrdinaryRowAutomorphismAction_eq_expected
    T alternatingSixUniversalCoverAlphaTwoAutomorphism
    alternatingSixAmbientAlphaTwoOrdinaryRowAction hcentral
  · exact alternatingSixAmbientAlphaTwoOrdinaryRowAction_dimension
  · exact alternatingSixAmbientAlphaTwoOrdinaryRowAction_scalarPattern
  · exact hresolve

end InductiveMcKay
end McKayConjecture
