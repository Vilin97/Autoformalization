/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.FiniteIndexProjectiveTable
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeNormalizerRepresentations

/-!
# The `3'`-character table of the Sylow-three normalizer in `SL(2, 𝔽₅)`

This file transports the six explicit rows of `QuaternionGroup 3` across the
concrete matrix-group equivalence with the exact Sylow `3`-normalizer.  The
result is an actual enumeration of all `3'`-degree irreducible characters of
the normalizer, together with degree and value formulas on its two explicit
generators.

The final definitions specialize the generic finite-index certificate API:
subsequent work on the ambient `SL(2, 𝔽₅)` table only has to supply the
ambient enumeration, the six-row matching, its automorphism check, and the
projective comparison rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The complete six-row enumeration of the `3'`-characters of the exact
Sylow `3`-normalizer in `SL(2, 𝔽₅)`. -/
def specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv :
    QuaternionGroupThreeCharacterRow ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer specialLinearTwoFiveSylowThree) 3 :=
  quaternionGroupThreePPrimeCharacterEquiv.trans
    (IrreducibleCharacter.pPrimeComapEquiv 3
      quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer.symm)

@[simp]
theorem specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_degree
    (r : QuaternionGroupThreeCharacterRow) :
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv r).1.degree =
      (quaternionGroupThreePPrimeCharacterEquiv r).1.degree :=
  rfl

@[simp]
theorem specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_degree_linear
    (j : ZMod 4) :
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
      (.linear j)).1.degree = 1 := by
  simp [specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv]

@[simp]
theorem
    specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_degree_twoDimensional
    (k : Fin 2) :
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
      (.twoDimensional k)).1.degree = 2 := by
  simp [specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv]

/-- Evaluation after transport can be read entirely in quaternion normal
form. -/
@[simp]
theorem specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values
    (r : QuaternionGroupThreeCharacterRow)
    (g : QuaternionGroup 3) :
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv r).1.values
        (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer g) =
      (quaternionGroupThreePPrimeCharacterEquiv r).1.values g := by
  change
    ((quaternionGroupThreePPrimeCharacterEquiv r).1.comap
      quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer.symm).values
        (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer g) =
      _
  rw [IrreducibleCharacter.comap_values,
    MulEquiv.symm_apply_apply]

@[simp]
theorem specialLinearTwoFiveThreeNormalizerLinear_values_a
    (j : ZMod 4) (i : ZMod 6) :
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
      (.linear j)).1.values
        (specialLinearTwoFiveSylowThreeNormalizerA ^ i.val) =
      (ZMod.toCircle
        (j * (2 * (i.val : ZMod 4))) : ℂ) := by
  calc
    _ =
        (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
          (.linear j)).1.values
          (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
            (QuaternionGroup.a i)) := by
      rw [
        quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_a]
    _ =
        (quaternionGroupThreePPrimeCharacterEquiv
          (.linear j)).1.values (QuaternionGroup.a i) :=
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values _ _
    _ = _ :=
      quaternionGroupThreeLinearPPrimeCharacter_values_a j i

@[simp]
theorem specialLinearTwoFiveThreeNormalizerLinear_values_xa
    (j : ZMod 4) (i : ZMod 6) :
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
      (.linear j)).1.values
        (specialLinearTwoFiveSylowThreeNormalizerX *
          specialLinearTwoFiveSylowThreeNormalizerA ^ i.val) =
      (ZMod.toCircle
        (j * (1 + 2 * (i.val : ZMod 4))) : ℂ) := by
  calc
    _ =
        (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
          (.linear j)).1.values
          (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
            (QuaternionGroup.xa i)) := by
      rw [
        quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_xa]
    _ =
        (quaternionGroupThreePPrimeCharacterEquiv
          (.linear j)).1.values (QuaternionGroup.xa i) :=
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values _ _
    _ = _ :=
      quaternionGroupThreeLinearPPrimeCharacter_values_xa j i

@[simp]
theorem specialLinearTwoFiveThreeNormalizerTwoDimensional_values_a
    (k : Fin 2) (i : ZMod 6) :
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
      (.twoDimensional k)).1.values
        (specialLinearTwoFiveSylowThreeNormalizerA ^ i.val) =
      quaternionGroupThreeSixthRootCharacter
          (quaternionGroupThreeTwoFrequency k * i) +
        quaternionGroupThreeSixthRootCharacter
          (-(quaternionGroupThreeTwoFrequency k * i)) := by
  calc
    _ =
        (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
          (.twoDimensional k)).1.values
          (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
            (QuaternionGroup.a i)) := by
      rw [
        quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_a]
    _ =
        (quaternionGroupThreePPrimeCharacterEquiv
          (.twoDimensional k)).1.values (QuaternionGroup.a i) :=
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values _ _
    _ = _ :=
      quaternionGroupThreeTwoIrreducibleCharacter_values_a k i

@[simp]
theorem specialLinearTwoFiveThreeNormalizerTwoDimensional_values_xa
    (k : Fin 2) (i : ZMod 6) :
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
      (.twoDimensional k)).1.values
        (specialLinearTwoFiveSylowThreeNormalizerX *
          specialLinearTwoFiveSylowThreeNormalizerA ^ i.val) = 0 := by
  calc
    _ =
        (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
          (.twoDimensional k)).1.values
          (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
            (QuaternionGroup.xa i)) := by
      rw [
        quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_xa]
    _ =
        (quaternionGroupThreePPrimeCharacterEquiv
          (.twoDimensional k)).1.values (QuaternionGroup.xa i) :=
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values _ _
    _ = 0 :=
      quaternionGroupThreeTwoIrreducibleCharacter_values_xa k i

/-- There are exactly six `3'`-degree irreducible characters of the exact
Sylow `3`-normalizer. -/
theorem natCard_specialLinearTwoFiveThreeNormalizerPPrimeCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          (SylowNormalizer specialLinearTwoFiveSylowThree) 3) =
      6 := by
  calc
    Nat.card
          (PPrimeIrreducibleCharacter
            (SylowNormalizer specialLinearTwoFiveSylowThree) 3) =
        Nat.card QuaternionGroupThreeCharacterRow :=
      Nat.card_congr
        specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv.symm
    _ = 6 := by
      rw [Nat.card_eq_fintype_card]
      native_decide

/-- The remaining ordinary-character-table input for the `p = 3`,
`SL(2, 𝔽₅)` finite-index certificate.  The normalizer enumeration is omitted
from the fields because it is the explicit equivalence proved above. -/
structure SpecialLinearTwoFiveThreeCharacterTableCompletion
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- Enumeration of the ambient `3'`-degree rows. -/
  ambientEnumeration :
    AmbientIndex ≃
      PPrimeIrreducibleCharacter SpecialLinearTwoFive 3
  /-- Matching of the ambient rows with the six normalizer rows. -/
  indexEquiv :
    AmbientIndex ≃ QuaternionGroupThreeCharacterRow
  /-- The finite automorphism-equivariance check on row indices. -/
  indexEquivariance :
    ∀ (a :
        SylowAutStabilizer specialLinearTwoFiveSylowThree)
      (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv.symm
          (a •
            specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
              (indexEquiv i))

namespace SpecialLinearTwoFiveThreeCharacterTableCompletion

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- Insert the already verified normalizer table into the generic
finite-index McKay certificate. -/
def toFiniteIndexMcKayEquivCertificate
    (d :
      SpecialLinearTwoFiveThreeCharacterTableCompletion AmbientIndex) :
    FiniteIndexMcKayEquivCertificate
      specialLinearTwoFiveSylowThree
      AmbientIndex QuaternionGroupThreeCharacterRow where
  ambientEnumeration := d.ambientEnumeration
  normalizerEnumeration :=
    specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
  indexEquiv := d.indexEquiv
  indexEquivariance := d.indexEquivariance

/-- The character-level equivariant McKay equivalence produced after the
three remaining finite ordinary-table checks are supplied. -/
def toEquivariantMcKayEquiv
    (d :
      SpecialLinearTwoFiveThreeCharacterTableCompletion AmbientIndex) :
    EquivariantMcKayEquiv specialLinearTwoFiveSylowThree :=
  d.toFiniteIndexMcKayEquivCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      SpecialLinearTwoFiveThreeCharacterTableCompletion AmbientIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv (d.ambientEnumeration i) =
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
        (d.indexEquiv i) :=
  d.toFiniteIndexMcKayEquivCertificate
    |>.toEquivariantMcKayEquiv_apply_enumerated i

end SpecialLinearTwoFiveThreeCharacterTableCompletion

/-- The remaining projective-table input after the exact normalizer rows have
been fixed.  It consists of one checked factor-set/central-scalar witness for
each ambient table row. -/
structure SpecialLinearTwoFiveThreeProjectiveTableCompletion
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- The ordinary character table, row matching, and equivariance checks. -/
  characterTable :
    SpecialLinearTwoFiveThreeCharacterTableCompletion AmbientIndex
  /-- The projective comparison calculation for every ambient row. -/
  projectiveRow :
    ∀ i : AmbientIndex,
      ExactNormalizerProjectiveRowData
        characterTable.toEquivariantMcKayEquiv
        (characterTable.ambientEnumeration i)

namespace SpecialLinearTwoFiveThreeProjectiveTableCompletion

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- Insert the completed projective rows into the generic finite-index
projective-table certificate. -/
def toFiniteIndexExactNormalizerProjectiveTableCertificate
    (d :
      SpecialLinearTwoFiveThreeProjectiveTableCompletion AmbientIndex) :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      specialLinearTwoFiveSylowThree
      AmbientIndex QuaternionGroupThreeCharacterRow where
  characterCertificate :=
    d.characterTable.toFiniteIndexMcKayEquivCertificate
  projectiveRow := d.projectiveRow

/-- A completed six-row table gives the full local inductive McKay datum for
`SL(2, 𝔽₅)` at `p = 3`. -/
def toLocalInductiveMcKayData
    (d :
      SpecialLinearTwoFiveThreeProjectiveTableCompletion AmbientIndex) :
    LocalInductiveMcKayData specialLinearTwoFiveSylowThree :=
  d.toFiniteIndexExactNormalizerProjectiveTableCertificate
    |>.toLocalInductiveMcKayData

end SpecialLinearTwoFiveThreeProjectiveTableCompletion

end InductiveMcKay
end McKayConjecture
