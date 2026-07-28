/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionCompleteness
import McKayConjecture.Character.CliffordCorrespondence
import McKayConjecture.Character.Multiplicity

/-!
# Restriction multiplicities as character pairings

For a homomorphism `φ : H →* G`, the multiplicity of an irreducible
character `η` in the restriction of an irreducible character `χ` is the
normalized pairing of `η` with the restricted character.  Completeness of
irreducible characters then gives the exact irreducible-character expansion
of every restricted character.

These formulas are stated for arbitrary homomorphisms.  In particular, they
can be reused when restriction is taken through the quotient-action groups
which occur in the transitivity proof for the Glauberman correspondence.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G H : Type} [Group G] [Group H]
variable [Finite G] [Finite H]

/-- Restriction multiplicity is the normalized character pairing with the
restricted realization. -/
theorem normalizedPairing_restrictedCharacter_eq_restrictionMultiplicity
    (φ : H →* G)
    (η : IrreducibleCharacter H)
    (χ : IrreducibleCharacter G) :
    ClassFunction.normalizedPairing
        (FDRep.characterClassFunction
          (FDRep.res φ χ.realization))
        η.toClassFunction =
      (restrictionMultiplicity φ η χ : ℂ) := by
  letI : Fintype H := Fintype.ofFinite H
  change
    ClassFunction.characterPairing
        (FDRep.characterClassFunction
          (FDRep.res φ χ.realization))
        η.toClassFunction =
      (restrictionMultiplicity φ η χ : ℂ)
  simpa [restrictionMultiplicity,
    IrreducibleCharacter.multiplicity,
    FDRep.multiplicity] using
    IrreducibleCharacter.characterPairing_eq_multiplicity
      η (FDRep.res φ χ.realization)

/-- The character of a restriction is the nonnegative integral combination
of irreducible characters with coefficients given by restriction
multiplicity. -/
theorem restrictedCharacter_eq_integerCharacterCombination
    (φ : H →* G)
    (χ : IrreducibleCharacter G) :
    FDRep.characterClassFunction
        (FDRep.res φ χ.realization) =
      IrreducibleCharacter.integerCharacterCombination
        (fun η : IrreducibleCharacter H =>
          (restrictionMultiplicity φ η χ : ℤ)) := by
  apply
    ClassFunction.eq_integerCharacterCombination_of_normalizedPairing_eq_int
  intro η
  rw [
    normalizedPairing_restrictedCharacter_eq_restrictionMultiplicity]
  norm_num

end CliffordCorrespondence
end McKayConjecture
