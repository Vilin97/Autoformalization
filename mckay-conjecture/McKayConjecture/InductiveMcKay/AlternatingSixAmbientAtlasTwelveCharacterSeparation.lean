/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasDegreeTwelveTraceSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoOrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenOrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerElevenOrdinaryCharacter

/-!
# Separation of the paired ATLAS degree-twelve ordinary characters

The power-one and power-seven rows have the same degree and central scalar,
as do the power-two and power-eleven rows. Exact traces at the presentation
word `AB` distinguish the normalized characters in each pair.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

private abbrev atlasPowerOneOrdinaryCertificate :=
  alternatingSixAmbientAtlasTwelvePowerOneOrdinaryCharacterRowCertificate

private abbrev atlasPowerTwoOrdinaryCertificate :=
  alternatingSixAmbientAtlasTwelvePowerTwoOrdinaryCharacterRowCertificate

private abbrev atlasPowerSevenOrdinaryCertificate :=
  alternatingSixAmbientAtlasTwelvePowerSevenOrdinaryCharacterRowCertificate

private abbrev atlasPowerElevenOrdinaryCertificate :=
  alternatingSixAmbientAtlasTwelvePowerElevenOrdinaryCharacterRowCertificate

/-- The normalized ATLAS power-one and power-seven characters are
distinct. -/
theorem
    alternatingSixAmbientAtlasPowerOneOrdinaryCharacter_ne_powerSeven :
    (atlasPowerOneOrdinaryCertificate.characterRowCertificate
        |>.irreducibleCharacter) ≠
      (atlasPowerSevenOrdinaryCertificate.characterRowCertificate
        |>.irreducibleCharacter) := by
  apply
    atlasPowerOneOrdinaryCertificate
      |>.irreducibleCharacter_ne_of_matrixAB_trace_ne
        atlasPowerSevenOrdinaryCertificate
  change
    (alternatingSixFiveAmbient_atlas12Power1_matrixA *
          alternatingSixFiveAmbient_atlas12Power1_matrixB).trace ≠
      (alternatingSixFiveAmbient_atlas12Power7_matrixA *
          alternatingSixFiveAmbient_atlas12Power7_matrixB).trace
  exact
    alternatingSixAmbientAtlas12Power1_matrixAB_trace_ne_power7_matrixAB_trace

/-- The normalized ATLAS power-two and power-eleven characters are
distinct. -/
theorem
    alternatingSixAmbientAtlasPowerTwoOrdinaryCharacter_ne_powerEleven :
    (atlasPowerTwoOrdinaryCertificate.characterRowCertificate
        |>.irreducibleCharacter) ≠
      (atlasPowerElevenOrdinaryCertificate.characterRowCertificate
        |>.irreducibleCharacter) := by
  apply
    atlasPowerTwoOrdinaryCertificate
      |>.irreducibleCharacter_ne_of_matrixAB_trace_ne
        atlasPowerElevenOrdinaryCertificate
  change
    (alternatingSixFiveAmbient_atlas12Power2_matrixA *
          alternatingSixFiveAmbient_atlas12Power2_matrixB).trace ≠
      (alternatingSixFiveAmbient_atlas12Power11_matrixA *
          alternatingSixFiveAmbient_atlas12Power11_matrixB).trace
  exact
    alternatingSixAmbientAtlas12Power2_matrixAB_trace_ne_power11_matrixAB_trace

end InductiveMcKay
end McKayConjecture
