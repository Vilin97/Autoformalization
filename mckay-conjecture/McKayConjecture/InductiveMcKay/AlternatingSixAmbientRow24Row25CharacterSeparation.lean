/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeTenCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25OrdinaryCharacter

/-!
# Separation of ambient ordinary rows 24 and 25

Rows 24 and 25 have the same degree and central-scalar pattern.  Their
already-checked traces at the second presentation generator distinguish
the two normalized ordinary characters.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

private abbrev row24OrdinaryCertificate :=
  alternatingSixAmbientRow24OrdinaryCharacterRowCertificate

private abbrev row25OrdinaryCertificate :=
  alternatingSixAmbientRow25OrdinaryCharacterRowCertificate

/-- The normalized ordinary characters at rows 24 and 25 are distinct. -/
theorem
    alternatingSixAmbientRow24OrdinaryCharacter_ne_row25OrdinaryCharacter :
    row24OrdinaryCertificate.characterRowCertificate.irreducibleCharacter ≠
      row25OrdinaryCertificate.characterRowCertificate.irreducibleCharacter := by
  apply
    row24OrdinaryCertificate.irreducibleCharacter_ne_of_matrixB_trace_ne
      row25OrdinaryCertificate
  change
    alternatingSixFiveAmbient_row24_matrixB.trace ≠
      alternatingSixFiveAmbient_row25_matrixB.trace
  exact alternatingSixAmbientRow24_matrixB_trace_ne_row25_matrixB_trace

end InductiveMcKay
end McKayConjecture
