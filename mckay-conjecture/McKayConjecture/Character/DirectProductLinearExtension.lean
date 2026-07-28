/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DirectProductCorrespondence
import McKayConjecture.Character.Linear

/-!
# Extending a direct-factor character by a linear character

An irreducible character of the first factor of `A × B` extends after
choosing any multiplicative linear character of `B`.  This is the
normalized variant of extension by the trivial second-factor character.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

variable {A B : Type} [Group A] [Group B]

/-- Extend a character of the first direct factor by a prescribed linear
character of the second factor. -/
def directProductFirstFactorLinearExtension
    (χ :
      IrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)))
    (lam : B →* ℂˣ) :
    IrreducibleCharacter (A × B) :=
  externalTensor
    (χ.comap
      (directProductFirstFactorEquiv
        (G := A) (H := B)).symm)
    (linear lam)

/-- The prescribed linear extension restricts to the original
first-factor character. -/
theorem directProductFirstFactorLinearExtension_isExtension
    (χ :
      IrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)))
    (lam : B →* ℂˣ) :
    IsExtensionAlong
      (directProductFirstFactor
        (G := A) (H := B)).subtype
      χ
      (directProductFirstFactorLinearExtension χ lam) := by
  intro x
  rw [directProductFirstFactorLinearExtension,
    externalTensor_values, comap_values,
    linear_values]
  have hx :
      x.1 ∈
        (⊤ : Subgroup A).prod (⊥ : Subgroup B) := by
    simpa [directProductFirstFactor] using x.property
  have hx2 : x.1.2 = 1 :=
    Subgroup.mem_bot.mp
      (Subgroup.mem_prod.mp hx).2
  change
    χ.values
          ((directProductFirstFactorEquiv
            (G := A) (H := B)).symm x.1.1) *
        (lam x.1.2 : ℂ) =
      χ.values x
  rw [hx2, map_one, Units.val_one, mul_one]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hx2.symm

variable [Finite A] [Finite B]
variable {p : ℕ} [Fact p.Prime]

/-- The prescribed linear extension, packaged with its prime-to-`p`
degree. -/
def directProductFirstFactorLinearPPrimeExtension
    (χ :
      PPrimeIrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)) p)
    (lam : B →* ℂˣ) :
    PPrimeIrreducibleCharacter (A × B) p :=
  ⟨directProductFirstFactorLinearExtension χ.1 lam,
    by
      rw [directProductFirstFactorLinearExtension,
        externalTensor_isPPrimeDegree_iff]
      exact
        ⟨by
            rw [IsPPrimeDegree, comap_degree]
            exact χ.2,
          linear_isPPrimeDegree lam p⟩⟩

@[simp]
theorem directProductFirstFactorLinearPPrimeExtension_coe
    (χ :
      PPrimeIrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)) p)
    (lam : B →* ℂˣ) :
    (directProductFirstFactorLinearPPrimeExtension
      χ lam).1 =
      directProductFirstFactorLinearExtension χ.1 lam :=
  rfl

/-- The prime-to-`p` package retains the extension property. -/
theorem directProductFirstFactorLinearPPrimeExtension_isExtension
    (χ :
      PPrimeIrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)) p)
    (lam : B →* ℂˣ) :
    IsExtensionAlong
      (directProductFirstFactor
        (G := A) (H := B)).subtype
      χ.1
      (directProductFirstFactorLinearPPrimeExtension
        χ lam).1 :=
  directProductFirstFactorLinearExtension_isExtension
    χ.1 lam

end IrreducibleCharacter
end McKayConjecture
