/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionConstituent
import McKayConjecture.CharacterTriple.CentralCharacterBijection

/-!
# Central character-triple correspondences preserve extensions

The character correspondence attached to a central isomorphism transports
the same projective multiplicity space on both sides.  If the source
character is an actual extension of the distinguished normal character,
that multiplicity space has dimension one.  Consequently the transported
character is an actual extension on the target side, not merely a character
lying over the target normal character.

This is the representation-theoretic bridge needed when an iterated
inductive-McKay construction produces a complete central-isomorphism witness:
once its target character is identified with the proposed lifted-factor
image, the normal-character extension clause follows automatically.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

variable {A B : Type}
  [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- An extension has one-dimensional projective multiplicity space in any
associated projective realization of its character triple. -/
theorem leftMultiplicitySpace_finrank_eq_one_of_isExtension
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ :
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character χ) :
    Module.finrank ℂ (C.leftMultiplicitySpace χ) = 1 := by
  let hover := hχ.liesOver
  have hdim :=
    C.leftMultiplicityTensor_finrank χ hover
  have hdim' :
      T.character.degree *
          Module.finrank ℂ (C.leftMultiplicitySpace χ) =
        T.character.degree * 1 := by
    simpa only [Module.finrank_tensorProduct,
      C.leftAssociated.finrank_eq_character_degree,
      hχ.degree_eq, mul_one] using hdim
  exact
    Nat.eq_of_mul_eq_mul_left
      T.character.degree_pos hdim'

/-- The forward character attached to a central-isomorphism witness carries
an exact source extension to an exact target extension. -/
theorem rightMultiplicityCharacter_isExtension_of_isExtension
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ :
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character χ) :
    IrreducibleCharacter.IsExtensionAlong
      U.normalSubgroup.subtype U.character
      (C.rightMultiplicityCharacter χ hχ.liesOver) := by
  intro m
  change
    (C.rightMultiplicityCharacter χ hχ.liesOver).values (m : B) =
      U.character.values m
  rw [C.rightMultiplicityCharacter_on_normal
    χ hχ.liesOver m,
    C.leftMultiplicitySpace_finrank_eq_one_of_isExtension χ hχ]
  simp

/-- Subtype form: the all-character central correspondence sends a source
extension to a target extension. -/
theorem centralCharacterEquiv_apply_isExtension
    (C : CentralIsomorphismWitness T U V W)
    (χ : IrreducibleCharacter A)
    (hχ :
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character χ) :
    IrreducibleCharacter.IsExtensionAlong
      U.normalSubgroup.subtype U.character
      (C.centralCharacterEquiv ⟨χ, hχ.liesOver⟩).1 := by
  exact
    C.rightMultiplicityCharacter_isExtension_of_isExtension χ hχ

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
