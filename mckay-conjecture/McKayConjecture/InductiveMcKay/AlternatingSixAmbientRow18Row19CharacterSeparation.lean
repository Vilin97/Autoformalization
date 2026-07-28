/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CharacterRowSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeEightCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19OrdinaryCharacter

/-!
# Separation of ambient ordinary rows 18 and 19

Rows 18 and 19 have the same dimension and central-scalar pattern.  Their
already-checked `AB` traces distinguish the two normalized ordinary
characters.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

private abbrev row18OrdinaryCertificate :=
  alternatingSixAmbientRow18OrdinaryCharacterRowCertificate

private abbrev row19OrdinaryCertificate :=
  alternatingSixAmbientRow19OrdinaryCharacterRowCertificate

/-- The normalized ordinary characters at rows 18 and 19 are distinct. -/
theorem
    alternatingSixAmbientRow18OrdinaryCharacter_ne_row19OrdinaryCharacter :
    row18OrdinaryCertificate.characterRowCertificate.irreducibleCharacter ≠
      row19OrdinaryCertificate.characterRowCertificate.irreducibleCharacter := by
  apply
    row18OrdinaryCertificate.irreducibleCharacter_ne_of_matrixAB_trace_ne
      row19OrdinaryCertificate
  change
    (alternatingSixFiveAmbient_row18_matrixA *
          alternatingSixFiveAmbient_row18_matrixB).trace ≠
      (alternatingSixFiveAmbient_row19_matrixA *
          alternatingSixFiveAmbient_row19_matrixB).trace
  exact
    alternatingSixAmbientRow18_matrixAB_trace_ne_row19_matrixAB_trace

end InductiveMcKay
end McKayConjecture
