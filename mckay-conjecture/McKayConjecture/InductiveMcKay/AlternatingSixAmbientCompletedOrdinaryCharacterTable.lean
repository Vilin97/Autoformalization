/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharactersThroughTwentyOne
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24Row25CharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelveCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixCanonicalCoverNumericalMcKay

/-!
# Complete ordinary character table of the canonical sixfold cover of `A₆`

The exact norm certificates supply all 31 named irreducible rows. Degree and
central-scalar signatures separate every pair except eleven explicit
collisions; the dedicated trace calculations separate those pairs. The
independently proved conjugacy-class count then shows that the row family is
the complete ordinary character table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixCompletedTableFactPrimeFive :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The normalized ordinary-character certificate at every named row of the
canonical sixfold cover. -/
def alternatingSixAmbientCompletedOrdinaryRow
    (row : AlternatingSixAmbientOrdinaryRow) :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row := by
  cases row with
  | row01 | row02 | row03 | row04 | row05 | row06 | row07
  | row08 | row09 | row10 | row11 | row12 | row13 | row14
  | row15 | row16 | row17 | row18 | row19 =>
      exact
        alternatingSixAmbientOrdinaryCharacterRowCertificateThroughNineteen
          _ (by decide)
  | row20 =>
      exact alternatingSixAmbientRow20OrdinaryCharacterRowCertificate
  | row21 =>
      exact alternatingSixAmbientRow21OrdinaryCharacterRowCertificate
  | row22 =>
      exact alternatingSixAmbientRow22OrdinaryCharacterRowCertificate
  | row23 =>
      exact alternatingSixAmbientRow23OrdinaryCharacterRowCertificate
  | row24 =>
      exact alternatingSixAmbientRow24OrdinaryCharacterRowCertificate
  | row25 =>
      exact alternatingSixAmbientRow25OrdinaryCharacterRowCertificate
  | row30 =>
      exact alternatingSixAmbientRow30OrdinaryCharacterRowCertificate
  | row31 =>
      exact alternatingSixAmbientRow31OrdinaryCharacterRowCertificate
  | atlasTwelvePowerOne =>
      exact
        alternatingSixAmbientAtlasTwelvePowerOneOrdinaryCharacterRowCertificate
  | atlasTwelvePowerTwo =>
      exact
        alternatingSixAmbientAtlasTwelvePowerTwoOrdinaryCharacterRowCertificate
  | atlasTwelvePowerSeven =>
      exact
        alternatingSixAmbientAtlasTwelvePowerSevenOrdinaryCharacterRowCertificate
  | atlasTwelvePowerEleven =>
      exact
        alternatingSixAmbientAtlasTwelvePowerElevenOrdinaryCharacterRowCertificate

/-- The 31 normalized rows, together with the eleven trace inequalities
needed by the finite signature reduction. -/
def alternatingSixAmbientSeparatedOrdinaryRowFamilyCertificate :
    AlternatingSixAmbientSeparatedOrdinaryRowFamily where
  row := alternatingSixAmbientCompletedOrdinaryRow
  row02_ne_row03 := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientOrdinaryRow02_ne_row03
  row04_ne_row05 := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientOrdinaryRow04_ne_row05
  row06_ne_row07 := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientOrdinaryRow06_ne_row07
  row08_ne_row09 := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientOrdinaryRow08_ne_row09
  row12_ne_row13 := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientOrdinaryRow12_ne_row13
  row14_ne_row15 := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientOrdinaryRow14_ne_row15
  row16_ne_row17 := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientOrdinaryRow16_ne_row17
  row18_ne_row19 := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientOrdinaryRow18_ne_row19
  row24_ne_row25 := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientRow24OrdinaryCharacter_ne_row25OrdinaryCharacter
  atlasOne_ne_atlasSeven := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientAtlasPowerOneOrdinaryCharacter_ne_powerSeven
  atlasTwo_ne_atlasEleven := by
    simpa [alternatingSixAmbientCompletedOrdinaryRow] using
      alternatingSixAmbientAtlasPowerTwoOrdinaryCharacter_ne_powerEleven

/-- The complete ordinary character table of the canonical sixfold cover of
`A₆`. -/
def alternatingSixAmbientOrdinaryCharacterTableCertificate :
    AlternatingSixAmbientOrdinaryCharacterTableCertificate :=
  alternatingSixAmbientSeparatedOrdinaryRowFamilyCertificate
    |>.toOrdinaryCharacterTableCertificate

/-! ### Unconditional numerical McKay statements for the canonical cover -/

/-- Numerical McKay for the fixed Sylow `2`-subgroup of the canonical
sixfold cover. -/
theorem alternatingSixCanonicalCover_statement_two_unconditional :
    Statement AlternatingSixUniversalCover 2
      (alternatingSixUniversalCoverSylow 2) :=
  alternatingSixCanonicalCover_statement_two
    alternatingSixAmbientOrdinaryCharacterTableCertificate

/-- Numerical McKay for the fixed Sylow `3`-subgroup of the canonical
sixfold cover. -/
theorem alternatingSixCanonicalCover_statement_three_unconditional :
    Statement AlternatingSixUniversalCover 3
      (alternatingSixUniversalCoverSylow 3) :=
  alternatingSixCanonicalCover_statement_three
    alternatingSixAmbientOrdinaryCharacterTableCertificate

/-- Numerical McKay for the fixed Sylow `5`-subgroup of the canonical
sixfold cover. -/
theorem alternatingSixCanonicalCover_statement_five_unconditional :
    Statement AlternatingSixUniversalCover 5
      (alternatingSixUniversalCoverSylow 5) :=
  alternatingSixCanonicalCover_statement_five
    alternatingSixAmbientOrdinaryCharacterTableCertificate

end InductiveMcKay
end McKayConjecture
