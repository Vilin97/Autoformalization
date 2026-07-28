/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordPPrimeCorrespondence

/-!
# Transport of inertia character fibres

The inertia group, its inclusion, and the predicate of lying over a normal
character all depend on that character.  This file provides the small
equality-transport equivalences needed when a representative is obtained by
applying an equivalence and then its inverse.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G : Type} [Group G]
variable (N : Subgroup G) [N.Normal]

/-- Equality of normal-subgroup characters identifies their irreducible
inertia fibres. -/
def irreducibleCharactersOverInertiaCongr
    {θ φ : IrreducibleCharacter N}
    (h : θ = φ) :
    IrreducibleCharactersOverInertia N θ ≃
      IrreducibleCharactersOverInertia N φ := by
  subst φ
  exact Equiv.refl _

/-- Prime-to-`p` version of
`irreducibleCharactersOverInertiaCongr`. -/
def pPrimeIrreducibleCharactersOverInertiaCongr
    {θ φ : IrreducibleCharacter N}
    (h : θ = φ) (p : ℕ) :
    PPrimeIrreducibleCharactersOverInertia N θ p ≃
      PPrimeIrreducibleCharactersOverInertia N φ p := by
  subst φ
  exact Equiv.refl _

@[simp]
theorem pPrimeIrreducibleCharactersOverInertiaCongr_rfl
    (θ : IrreducibleCharacter N) (p : ℕ) :
    pPrimeIrreducibleCharactersOverInertiaCongr
      N (Eq.refl θ) p =
        Equiv.refl _ :=
  rfl

@[simp]
theorem pPrimeIrreducibleCharactersOverInertiaCongr_apply_coe
    {θ φ : IrreducibleCharacter N}
    (h : θ = φ) (p : ℕ)
    (χ : PPrimeIrreducibleCharactersOverInertia N θ p) :
    ((pPrimeIrreducibleCharactersOverInertiaCongr
      N h p χ).1.1).degree =
        χ.1.1.degree := by
  subst φ
  rfl

end CliffordCorrespondence
end McKayConjecture
