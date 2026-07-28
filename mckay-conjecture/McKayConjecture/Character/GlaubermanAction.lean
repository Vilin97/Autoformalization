/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.OfQuotient
import McKayConjecture.Character.CliffordCorrespondence

/-!
# Glauberman correspondence for an abstract group action

The ambient-subgroup formulation is convenient in applications, while
transitivity is most naturally expressed for an abstract action of `P` on
`A`.  This file provides the action-level interface.  It has the same
defining property: the correspondent is uniquely characterized by
restriction multiplicity prime to `p`.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable (P A : Type) [Group P] [Group A]
variable [MulDistribMulAction P A]

/-- The canonical inclusion of the action fixed-point subgroup into `A`. -/
def actionFixedPointsInclusion :
    FixedPoints.subgroup P A →* A :=
  (FixedPoints.subgroup P A).subtype

@[simp]
theorem actionFixedPointsInclusion_apply
    (a : FixedPoints.subgroup P A) :
    actionFixedPointsInclusion P A a = a :=
  rfl

/-- A prime-to-`p` irreducible character fixed by the action of `P`. -/
abbrev ActionInvariantPPrimeIrreducibleCharacter
    (P A : Type) [Group P] [Group A]
    [MulDistribMulAction P A] (p : ℕ) :=
  {θ : PPrimeIrreducibleCharacter A p //
    ∀ g : P, ∀ a : A,
      θ.1.values (g • a) = θ.1.values a}

/-- The numerical Glauberman correspondence for an abstract action. -/
structure ActionGlaubermanCorrespondence
    (P A : Type) [Group P] [Group A]
    [MulDistribMulAction P A] (p : ℕ) where
  /-- The character correspondence. -/
  characterEquiv :
    ActionInvariantPPrimeIrreducibleCharacter P A p ≃
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup P A) p
  /-- The correspondent occurs with multiplicity prime to `p`. -/
  multiplicity_isPPrime :
    ∀ θ : ActionInvariantPPrimeIrreducibleCharacter P A p,
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion P A)
          (characterEquiv θ).1 θ.1.1
  /-- This property uniquely characterizes the correspondent. -/
  eq_correspondent_of_multiplicity_isPPrime :
    ∀ (θ : ActionInvariantPPrimeIrreducibleCharacter P A p)
      (φ :
        PPrimeIrreducibleCharacter
          (FixedPoints.subgroup P A) p),
      (¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion P A)
          φ.1 θ.1.1) →
        φ = characterEquiv θ

namespace ActionGlaubermanCorrespondence

variable {P A}
variable {p : ℕ}

/-- The action-level numerical relation defining the correspondent. -/
def HasPPrimeRestrictionMultiplicity
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p)
    (φ :
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup P A) p) : Prop :=
  ¬p ∣
    restrictionMultiplicity
      (actionFixedPointsInclusion P A)
      φ.1 θ.1.1

/-- A relation uniquely solvable in both variables packages into an
action-level Glauberman equivalence. -/
def of_biunique_multiplicity
    (hsource :
      ∀ θ : ActionInvariantPPrimeIrreducibleCharacter P A p,
        ∃! φ :
          PPrimeIrreducibleCharacter
            (FixedPoints.subgroup P A) p,
          HasPPrimeRestrictionMultiplicity θ φ)
    (htarget :
      ∀ φ :
          PPrimeIrreducibleCharacter
            (FixedPoints.subgroup P A) p,
        ∃! θ :
          ActionInvariantPPrimeIrreducibleCharacter P A p,
          HasPPrimeRestrictionMultiplicity θ φ) :
    ActionGlaubermanCorrespondence P A p := by
  let f :
      ActionInvariantPPrimeIrreducibleCharacter P A p →
        PPrimeIrreducibleCharacter
          (FixedPoints.subgroup P A) p :=
    fun θ ↦ Classical.choose (hsource θ)
  have hf :
      ∀ θ, HasPPrimeRestrictionMultiplicity θ (f θ) :=
    fun θ ↦ Classical.choose_spec (hsource θ) |>.1
  have hfinjective : Function.Injective f := by
    intro θ₁ θ₂ heq
    exact
      (htarget (f θ₁)).unique
        (hf θ₁)
        (heq ▸ hf θ₂)
  have hfsurjective : Function.Surjective f := by
    intro φ
    let θ :=
      Classical.choose (htarget φ)
    have hθφ :
        HasPPrimeRestrictionMultiplicity θ φ :=
      Classical.choose_spec (htarget φ) |>.1
    refine ⟨θ, ?_⟩
    exact (hsource θ).unique (hf θ) hθφ
  let e := Equiv.ofBijective f
    ⟨hfinjective, hfsurjective⟩
  exact
    { characterEquiv := e
      multiplicity_isPPrime := hf
      eq_correspondent_of_multiplicity_isPPrime :=
        fun θ φ hφ ↦
          (hsource θ).unique hφ (hf θ) }

/-- The action-level correspondent really is a constituent of ordinary
restriction to the fixed-point subgroup. -/
theorem liesOver
    (d : ActionGlaubermanCorrespondence P A p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    LiesOverAlong
      (actionFixedPointsInclusion P A)
      (d.characterEquiv θ).1 θ.1.1 := by
  apply Nat.pos_of_ne_zero
  intro hzero
  exact
    d.multiplicity_isPPrime θ
      (hzero ▸ dvd_zero p)

end ActionGlaubermanCorrespondence
end McKayConjecture
