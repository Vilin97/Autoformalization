/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanAction

/-!
# Strong action-level Glauberman correspondences

For transitivity one needs the classical uniqueness statement against
*every* irreducible character of the fixed-point group, not merely the
prime-to-`p` characters.  This strengthened interface records exactly that
property while retaining the prime-to-`p` character equivalence used by the
McKay reduction.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable (P A : Type) [Group P] [Group A]
variable [MulDistribMulAction P A]
variable [Finite P] [Finite A]
variable {p : ℕ}

/-- An action-level Glauberman correspondence whose defining multiplicity
property uniquely determines the correspondent among all irreducible
characters of the fixed-point group. -/
structure StrongActionGlaubermanCorrespondence (p : ℕ) where
  /-- The prime-to-`p` character correspondence. -/
  characterEquiv :
    ActionInvariantPPrimeIrreducibleCharacter P A p ≃
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup P A) p
  /-- The selected correspondent has multiplicity prime to `p`. -/
  multiplicity_isPPrime :
    ∀ θ : ActionInvariantPPrimeIrreducibleCharacter P A p,
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion P A)
          (characterEquiv θ).1 θ.1.1
  /-- No other irreducible character, of any degree, has multiplicity
  prime to `p`. -/
  eq_correspondent_of_multiplicity_isPPrime :
    ∀ (θ : ActionInvariantPPrimeIrreducibleCharacter P A p)
      (φ : IrreducibleCharacter
        (FixedPoints.subgroup P A)),
      (¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion P A)
          φ θ.1.1) →
        φ = (characterEquiv θ).1

namespace StrongActionGlaubermanCorrespondence

variable {P A}

/-- Forgetting full uniqueness gives the ordinary action-level
correspondence interface. -/
def toAction
    (d : StrongActionGlaubermanCorrespondence P A p) :
    ActionGlaubermanCorrespondence P A p where
  characterEquiv := d.characterEquiv
  multiplicity_isPPrime := d.multiplicity_isPPrime
  eq_correspondent_of_multiplicity_isPPrime := by
    intro θ φ hφ
    apply Subtype.ext
    exact
      d.eq_correspondent_of_multiplicity_isPPrime
        θ φ.1 hφ

/-- Every irreducible character other than the correspondent has
multiplicity divisible by `p`. -/
theorem multiplicity_dvd_of_ne
    (d : StrongActionGlaubermanCorrespondence P A p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p)
    (φ : IrreducibleCharacter
      (FixedPoints.subgroup P A))
    (hne : φ ≠ (d.characterEquiv θ).1) :
    p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        φ θ.1.1 := by
  by_contra hprime
  exact hne
    (d.eq_correspondent_of_multiplicity_isPPrime
      θ φ hprime)

/-- The selected irreducible character occurs in the restricted source
character. -/
theorem liesOver
    (d : StrongActionGlaubermanCorrespondence P A p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    LiesOverAlong
      (actionFixedPointsInclusion P A)
      (d.characterEquiv θ).1 θ.1.1 :=
  d.toAction.liesOver θ

end StrongActionGlaubermanCorrespondence
end McKayConjecture
