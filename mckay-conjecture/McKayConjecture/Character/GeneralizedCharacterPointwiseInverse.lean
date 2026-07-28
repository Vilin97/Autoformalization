/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionTheorem
import McKayConjecture.Character.GeneralizedCharacterNormOne

/-!
# Pointwise inverse criteria for linear characters

In the Dade--Glauberman--Nagao construction, a class function is first
shown to be a generalized character by Brauer's elementary-local
criterion.  Its defining formula also gives the pointwise identity

`f(g) * f(g⁻¹) = 1`.

The identity makes the normalized self-pairing equal to one.  If the
value at the identity is one, the integral norm-one criterion then
identifies the class function with an actual multiplicative linear
character.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- The pointwise inverse identity makes the normalized bilinear
self-pairing equal to one. -/
theorem normalizedPairing_self_eq_one_of_pointwise_inverse
    (f : ClassFunction G)
    (hinv : ∀ g : G, f g * f g⁻¹ = 1) :
    normalizedPairing f f = 1 := by
  letI : Fintype G := Fintype.ofFinite G
  change
    (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, f g * f g⁻¹ = 1
  rw [Finset.sum_congr rfl (fun g _ ↦ hinv g)]
  simp

/-- A generalized character satisfying the pointwise inverse identity
and taking value one at the identity is a linear character. -/
theorem IsGeneralizedCharacter.eq_linear_of_pointwise_inverse
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (hinv : ∀ g : G, f g * f g⁻¹ = 1)
    (hone : f 1 = 1) :
    ∃ lam : G →* ℂˣ,
      f = (IrreducibleCharacter.linear lam).toClassFunction :=
  hf.eq_linear_of_norm_one_of_value_one
    (normalizedPairing_self_eq_one_of_pointwise_inverse f hinv)
    hone

/-- Elementary-local generalizedness, the pointwise inverse identity, and
normalization at one directly produce a multiplicative linear character.

This is the form used in the Dade--Glauberman--Nagao correction-character
construction: Brauer's theorem supplies ambient generalizedness from the
elementary restrictions, while the pointwise identity supplies norm one. -/
theorem eq_linear_of_elementary_local_of_pointwise_inverse
    {f : ClassFunction G}
    (hlocal :
      ∀ (p : ℕ), p.Prime →
        ∀ (S : Subgroup G)
          (D : PElementaryDecomposition p S),
          IsGeneralizedCharacter
            (restrictToPElementaryProduct S D f))
    (hinv : ∀ g : G, f g * f g⁻¹ = 1)
    (hone : f 1 = 1) :
    ∃ lam : G →* ℂˣ,
      f = (IrreducibleCharacter.linear lam).toClassFunction :=
  (isGeneralizedCharacter_of_elementary_local_unconditional hlocal)
    |>.eq_linear_of_pointwise_inverse hinv hone

end ClassFunction
end McKayConjecture
