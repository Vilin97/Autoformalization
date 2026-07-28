/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Twist

/-!
# Transport of extensions along group equivalences

An isomorphism of commuting group-homomorphism squares transports an
irreducible-character extension to an extension of the transported source
character.  Twisting by a linear character is natural for the same
pullback operation.

These elementary facts are the first transport step in the orbitwise
gluing argument of Navarro--Späth, Corollary 5.14: conjugating a selected
extension must carry the whole Gallagher family over that extension to the
corresponding conjugate family.
-/

noncomputable section

universe u₁ u₂ u₃ u₄

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u₁} {G' : Type u₂}
variable {H : Type u₃} {H' : Type u₄}
variable [Group G] [Group G'] [Group H] [Group H']

/-- A commuting square of group equivalences transports an extension.

The square is written with the equivalences pointing from the new groups
to the old groups, matching `IrreducibleCharacter.comap`. -/
theorem IsExtensionAlong.comap_equiv
    {f : H →* G} {f' : H' →* G'}
    (eG : G' ≃* G) (eH : H' ≃* H)
    (hcomm :
      eG.toMonoidHom.comp f' =
        f.comp eH.toMonoidHom)
    {χ : IrreducibleCharacter H}
    {ψ : IrreducibleCharacter G}
    (hψ : IsExtensionAlong f χ ψ) :
    IsExtensionAlong f'
      (χ.comap eH) (ψ.comap eG) := by
  intro h
  rw [comap_values, comap_values]
  have hpoint :=
    congrArg (fun k : H' →* G ↦ k h) hcomm
  change eG (f' h) = f (eH h) at hpoint
  rw [hpoint]
  exact hψ (eH h)

/-- Pullback along a group equivalence commutes with twisting by a
multiplicative linear character. -/
@[simp]
theorem twist_comap
    (e : G' ≃* G)
    (lam : G →* ℂˣ)
    (χ : IrreducibleCharacter G) :
    (twist lam χ).comap e =
      twist (lam.comp e.toMonoidHom) (χ.comap e) := by
  apply IrreducibleCharacter.ext
  funext g
  simp

end IrreducibleCharacter
end McKayConjecture
