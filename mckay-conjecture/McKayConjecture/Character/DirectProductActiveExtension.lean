/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveExtension
import McKayConjecture.Character.DirectProductCorrespondence

/-!
# Active characters on a direct factor

Every prime-to-`p` character of the first factor of a finite direct product
extends by the trivial character of the second factor.  Consequently every
such character belongs to an active Clifford orbit.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
variable {p : ℕ} [Fact p.Prime]

/-- Extension by the trivial character, packaged with its prime-to-`p`
degree proof. -/
def directProductFirstFactorPPrimeExtension
    (χ :
      PPrimeIrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)) p) :
    PPrimeIrreducibleCharacter (A × B) p :=
  ⟨directProductFirstFactorExtension χ.1,
    by
      rw [directProductFirstFactorExtension,
        externalTensor_isPPrimeDegree_iff]
      exact
        ⟨by
            simpa [IsPPrimeDegree] using χ.2,
          trivial_isPPrimeDegree B p⟩⟩

@[simp]
theorem directProductFirstFactorPPrimeExtension_coe
    (χ :
      PPrimeIrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)) p) :
    (directProductFirstFactorPPrimeExtension χ).1 =
      directProductFirstFactorExtension χ.1 :=
  rfl

/-- The prime-to-`p` extension restricts to the original first-factor
character. -/
theorem directProductFirstFactorPPrimeExtension_isExtension
    (χ :
      PPrimeIrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)) p) :
    IsExtensionAlong
      (directProductFirstFactor (G := A) (H := B)).subtype
      χ.1 (directProductFirstFactorPPrimeExtension χ).1 :=
  directProductFirstFactorExtension_isExtension χ.1

/-- Every prime-to-`p` character of a direct factor is active in the full
direct product. -/
theorem directProductFirstFactor_isActivePPrimeCharacter
    (χ :
      PPrimeIrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)) p) :
    CliffordPartition.IsActivePPrimeCharacter
      (directProductFirstFactor (G := A) (H := B)) χ :=
  CliffordPartition.isActivePPrimeCharacter_of_isExtension
    (directProductFirstFactor (G := A) (H := B))
    χ (directProductFirstFactorPPrimeExtension χ)
    (directProductFirstFactorPPrimeExtension_isExtension χ)

end IrreducibleCharacter
end McKayConjecture
