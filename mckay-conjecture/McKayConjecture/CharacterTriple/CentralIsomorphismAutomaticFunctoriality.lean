/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCharacterFunctoriality
import McKayConjecture.CharacterTriple.CentralIsomorphismAutomaticTransitivity

/-!
# Character functoriality for automatic central-isomorphism composition

The strict automatic composite transports the second witness onto the first
middle representation space.  Its induced character correspondence is
therefore the literal composite through that transported witness.

The current character-bijection implementation uses representation spaces
and ambient groups in `Type`, so these functoriality statements inherit that
universe restriction.  The underlying automatic composition theorem remains
universe-polymorphic.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

variable {A B D : Type}
  [Finite A] [Finite B] [Finite D]
  [Group A] [Group B] [Group D]
variable {T : CharacterTriple A} {U : CharacterTriple B}
  {Z : CharacterTriple D}
variable {V W W' Y : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup W'] [Module ℂ W'] [Module.Finite ℂ W'] [Nontrivial W']
  [AddCommGroup Y] [Module ℂ Y] [Module.Finite ℂ Y] [Nontrivial Y]

/-- The all-character correspondence of the strict automatic composite is
the composite through the gauge-aligned second witness. -/
theorem centralCharacterEquiv_composeAutomaticStrict
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) :
    (C₁.composeAutomaticStrict C₂).centralCharacterEquiv =
      C₁.centralCharacterEquiv.trans
        (C₁.alignSecondOnFirstMiddleSpace C₂).centralCharacterEquiv :=
  centralCharacterEquiv_compose_of_projective_eq
    C₁ (C₁.alignSecondOnFirstMiddleSpace C₂) rfl

/-- Prime-to-`p` character functoriality for the strict automatic
composite. -/
theorem centralPPrimeCharacterEquiv_composeAutomaticStrict
    {p : ℕ} (hp : p.Prime)
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y)
    (hT : T.character.IsPPrimeDegree p)
    (hU : U.character.IsPPrimeDegree p)
    (hZ : Z.character.IsPPrimeDegree p) :
    (C₁.composeAutomaticStrict C₂).centralPPrimeCharacterEquiv
        hp hT hZ =
      (C₁.centralPPrimeCharacterEquiv hp hT hU).trans
        ((C₁.alignSecondOnFirstMiddleSpace C₂
          ).centralPPrimeCharacterEquiv hp hU hZ) :=
  centralPPrimeCharacterEquiv_compose_of_projective_eq
    hp C₁ (C₁.alignSecondOnFirstMiddleSpace C₂) rfl hT hU hZ

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
