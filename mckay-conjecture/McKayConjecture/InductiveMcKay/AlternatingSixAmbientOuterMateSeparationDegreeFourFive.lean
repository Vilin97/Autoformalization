/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeFourCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeFiveCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterSecondSeparator

/-!
# Degree-four and degree-five mate-separating values

The first outer automorphism fixes the state-77 class.  The second exchanges
the state-77 and state-79 classes.  Their exact values distinguish the two
rows in each of the repeated degree-four and degree-five signatures.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The state-77 value of row 06 differs from the competing row-07 value. -/
theorem alternatingSixAmbientAlphaOneRow06_mateTestValue_ne :
    alternatingSixAmbientRow06CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator ≠
      alternatingSixAmbientRow07CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator := by
  rw [alternatingSixAmbientRow06_character_separator,
    alternatingSixAmbientRow07_character_separator]
  norm_num

/-- The state-77 value of row 08 differs from the competing row-09 value. -/
theorem alternatingSixAmbientAlphaOneRow08_mateTestValue_ne :
    alternatingSixAmbientRow08CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator ≠
      alternatingSixAmbientRow09CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator := by
  rw [alternatingSixAmbientRow08_character_separator,
    alternatingSixAmbientRow09_character_separator]
  norm_num

/-- The state-79 value of row 06 differs from its state-77 value. -/
theorem alternatingSixAmbientAlphaTwoRow06_mateTestValue_ne :
    alternatingSixAmbientRow06CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSecondSeparator ≠
      alternatingSixAmbientRow06CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator := by
  rw [alternatingSixAmbientRow06_character_secondSeparator,
    alternatingSixAmbientRow06_character_separator]
  norm_num

/-- The state-79 value of row 08 differs from its state-77 value. -/
theorem alternatingSixAmbientAlphaTwoRow08_mateTestValue_ne :
    alternatingSixAmbientRow08CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSecondSeparator ≠
      alternatingSixAmbientRow08CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator := by
  rw [alternatingSixAmbientRow08_character_secondSeparator,
    alternatingSixAmbientRow08_character_separator]
  norm_num

end InductiveMcKay
end McKayConjecture
