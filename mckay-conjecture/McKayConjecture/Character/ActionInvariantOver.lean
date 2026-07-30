/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordPPrimeCorrespondence
import McKayConjecture.Character.InnerAutomorphism

/-!
# Action-invariant characters lying over a fixed character

For an explicitly supplied action `A →* MulAut G`, this file defines the
ordinary and prime-to-`p` irreducible characters of `G` that are fixed by
`A` and lie over a fixed irreducible character along a homomorphism
`H →* G`.

The ordinary carrier is kept separate from its prime-to-`p` restriction.
This is important for invariant-character counting results, whose natural
statements concern ordinary irreducible characters even when a later
degree argument shows that every character being counted has prime-to-`p`
degree.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordCorrespondence

variable {A H G : Type}
variable [Group A] [Group H] [Group G]

/-- The irreducible characters of `G` that lie over `θ` along `φ` and are
fixed by the explicitly supplied action of `A` on `G`. -/
def ActionInvariantIrreducibleCharactersOverAlong
    (action : A →* MulAut G)
    (φ : H →* G)
    (θ : IrreducibleCharacter H) :=
  {χ : IrreducibleCharactersOverAlong φ θ //
    ∀ a : A, action a • χ.1 = χ.1}

/-- The prime-to-`p` irreducible characters of `G` that lie over `θ` along
`φ` and are fixed by the explicitly supplied action of `A` on `G`. -/
def ActionInvariantPPrimeIrreducibleCharactersOverAlong
    (action : A →* MulAut G)
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ) :=
  {χ : PPrimeIrreducibleCharactersOverAlong φ θ p //
    ∀ a : A, action a • χ.1.1 = χ.1.1}

/-- Lying-over ordinary character fibres are finite when the target group
is finite.  This explicit instance avoids relying on typeclass reduction
through nested subtype definitions. -/
instance finiteIrreducibleCharactersOverAlong
    [Finite G]
    (φ : H →* G)
    (θ : IrreducibleCharacter H) :
    Finite (IrreducibleCharactersOverAlong φ θ) :=
  Finite.of_injective
    (fun χ : IrreducibleCharactersOverAlong φ θ => χ.1)
    (fun _ _ h => Subtype.ext h)

/-- Prime-to-`p` lying-over character fibres are finite when the target
group is finite. -/
instance finitePPrimeIrreducibleCharactersOverAlong
    [Finite G]
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ) :
    Finite (PPrimeIrreducibleCharactersOverAlong φ θ p) :=
  Finite.of_injective
    (fun χ : PPrimeIrreducibleCharactersOverAlong φ θ p => χ.1.1)
    (fun _ _ h => Subtype.ext (Subtype.ext h))

/-- Action-invariant ordinary lying-over character fibres are finite when
the target group is finite. -/
instance finiteActionInvariantIrreducibleCharactersOverAlong
    [Finite G]
    (action : A →* MulAut G)
    (φ : H →* G)
    (θ : IrreducibleCharacter H) :
    Finite
      (ActionInvariantIrreducibleCharactersOverAlong
        action φ θ) :=
  Finite.of_injective
    (fun χ :
      ActionInvariantIrreducibleCharactersOverAlong
        action φ θ => χ.1.1)
    (fun _ _ h => Subtype.ext (Subtype.ext h))

/-- Action-invariant prime-to-`p` lying-over character fibres are finite
when the target group is finite. -/
instance finiteActionInvariantPPrimeIrreducibleCharactersOverAlong
    [Finite G]
    (action : A →* MulAut G)
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ) :
    Finite
      (ActionInvariantPPrimeIrreducibleCharactersOverAlong
        action φ θ p) :=
  Finite.of_injective
    (fun χ :
      ActionInvariantPPrimeIrreducibleCharactersOverAlong
        action φ θ p => χ.1.1.1)
    (fun _ _ h =>
      Subtype.ext (Subtype.ext (Subtype.ext h)))

/-- The ordinary invariant lying-over type for the inner conjugation action
of `G` on itself. -/
abbrev SelfConjugationInvariantIrreducibleCharactersOverAlong
    (φ : H →* G)
    (θ : IrreducibleCharacter H) :=
  ActionInvariantIrreducibleCharactersOverAlong
    (MulAut.conj : G →* MulAut G) φ θ

/-- The prime-to-`p` invariant lying-over type for the inner conjugation
action of `G` on itself. -/
abbrev SelfConjugationInvariantPPrimeIrreducibleCharactersOverAlong
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ) :=
  ActionInvariantPPrimeIrreducibleCharactersOverAlong
    (MulAut.conj : G →* MulAut G) φ θ p

/-- Inner conjugation fixes every ordinary irreducible character, so the
invariance proof can be erased from an ordinary lying-over fibre. -/
def selfConjugationInvariantIrreducibleCharactersOverAlongEquiv
    (φ : H →* G)
    (θ : IrreducibleCharacter H) :
    SelfConjugationInvariantIrreducibleCharactersOverAlong φ θ ≃
      IrreducibleCharactersOverAlong φ θ :=
  Equiv.subtypeUnivEquiv fun χ g =>
    IrreducibleCharacter.conj_smul g χ.1

/-- Inner conjugation fixes every prime-to-`p` irreducible character, so
the invariance proof can be erased from a prime-to-`p` lying-over fibre. -/
def selfConjugationInvariantPPrimeIrreducibleCharactersOverAlongEquiv
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ) :
    SelfConjugationInvariantPPrimeIrreducibleCharactersOverAlong
        φ θ p ≃
      PPrimeIrreducibleCharactersOverAlong φ θ p :=
  Equiv.subtypeUnivEquiv fun χ g =>
    IrreducibleCharacter.conj_smul g χ.1.1

@[simp]
theorem selfConjugationInvariantIrreducibleCharactersOverAlongEquiv_apply
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (χ :
      SelfConjugationInvariantIrreducibleCharactersOverAlong
        φ θ) :
    selfConjugationInvariantIrreducibleCharactersOverAlongEquiv
        φ θ χ =
      χ.1 :=
  rfl

@[simp]
theorem selfConjugationInvariantPPrimeIrreducibleCharactersOverAlongEquiv_apply
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ)
    (χ :
      SelfConjugationInvariantPPrimeIrreducibleCharactersOverAlong
        φ θ p) :
    selfConjugationInvariantPPrimeIrreducibleCharactersOverAlongEquiv
        φ θ p χ =
      χ.1 :=
  rfl

/-- If every ordinary character in a lying-over fibre has prime-to-`p`
degree, the prime-to-`p` restriction carries no additional data. -/
def pPrimeIrreducibleCharactersOverAlongEquivOfForallIsPPrimeDegree
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ)
    (hdegree :
      ∀ χ : IrreducibleCharactersOverAlong φ θ,
        χ.1.IsPPrimeDegree p) :
    PPrimeIrreducibleCharactersOverAlong φ θ p ≃
      IrreducibleCharactersOverAlong φ θ :=
  Equiv.subtypeUnivEquiv hdegree

/-- If every action-invariant ordinary character in a lying-over fibre has
prime-to-`p` degree, the prime-to-`p` restriction carries no additional
data. -/
def actionInvariantPPrimeIrreducibleCharactersOverAlongEquivOfForallIsPPrimeDegree
    (action : A →* MulAut G)
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ)
    (hdegree :
      ∀ χ :
          ActionInvariantIrreducibleCharactersOverAlong
            action φ θ,
        χ.1.1.IsPPrimeDegree p) :
    ActionInvariantPPrimeIrreducibleCharactersOverAlong
        action φ θ p ≃
      ActionInvariantIrreducibleCharactersOverAlong
        action φ θ where
  toFun χ := ⟨χ.1.1, χ.2⟩
  invFun χ := ⟨⟨χ.1, hdegree χ⟩, χ.2⟩
  left_inv χ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv χ := by
    apply Subtype.ext
    rfl

/-- Erasing self-conjugation invariance does not change the cardinality of
an ordinary lying-over fibre. -/
theorem natCard_selfConjugationInvariantIrreducibleCharactersOverAlong
    (φ : H →* G)
    (θ : IrreducibleCharacter H) :
    Nat.card
        (SelfConjugationInvariantIrreducibleCharactersOverAlong
          φ θ) =
      Nat.card (IrreducibleCharactersOverAlong φ θ) :=
  Nat.card_congr
    (selfConjugationInvariantIrreducibleCharactersOverAlongEquiv
      φ θ)

/-- Erasing self-conjugation invariance does not change the cardinality of
a prime-to-`p` lying-over fibre. -/
theorem natCard_selfConjugationInvariantPPrimeIrreducibleCharactersOverAlong
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ) :
    Nat.card
        (SelfConjugationInvariantPPrimeIrreducibleCharactersOverAlong
          φ θ p) =
      Nat.card
        (PPrimeIrreducibleCharactersOverAlong φ θ p) :=
  Nat.card_congr
    (selfConjugationInvariantPPrimeIrreducibleCharactersOverAlongEquiv
      φ θ p)

/-- Under a pointwise prime-to-`p` degree hypothesis, restricting an
ordinary lying-over fibre to prime-to-`p` degree does not change its
cardinality. -/
theorem natCard_pPrimeIrreducibleCharactersOverAlong_eq_of_forall_isPPrimeDegree
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ)
    (hdegree :
      ∀ χ : IrreducibleCharactersOverAlong φ θ,
        χ.1.IsPPrimeDegree p) :
    Nat.card
        (PPrimeIrreducibleCharactersOverAlong φ θ p) =
      Nat.card (IrreducibleCharactersOverAlong φ θ) :=
  Nat.card_congr
    (pPrimeIrreducibleCharactersOverAlongEquivOfForallIsPPrimeDegree
      φ θ p hdegree)

/-- Under a pointwise prime-to-`p` degree hypothesis, restricting an
action-invariant ordinary lying-over fibre to prime-to-`p` degree does not
change its cardinality. -/
theorem natCard_actionInvariantPPrimeIrreducibleCharactersOverAlong_eq_of_forall_isPPrimeDegree
    (action : A →* MulAut G)
    (φ : H →* G)
    (θ : IrreducibleCharacter H)
    (p : ℕ)
    (hdegree :
      ∀ χ :
          ActionInvariantIrreducibleCharactersOverAlong
            action φ θ,
        χ.1.1.IsPPrimeDegree p) :
    Nat.card
        (ActionInvariantPPrimeIrreducibleCharactersOverAlong
          action φ θ p) =
      Nat.card
        (ActionInvariantIrreducibleCharactersOverAlong
          action φ θ) :=
  Nat.card_congr
    (actionInvariantPPrimeIrreducibleCharactersOverAlongEquivOfForallIsPPrimeDegree
      action φ θ p hdegree)

section Inertia

variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- Action-invariant ordinary characters of the inertia group lying over
the character that defines it. -/
abbrev ActionInvariantIrreducibleCharactersOverInertia
    (action :
      A →* MulAut (IrreducibleCharacter.inertia N θ)) :=
  ActionInvariantIrreducibleCharactersOverAlong
    action (inertiaInclusion N θ) θ

/-- Action-invariant prime-to-`p` characters of the inertia group lying
over the character that defines it. -/
abbrev ActionInvariantPPrimeIrreducibleCharactersOverInertia
    (action :
      A →* MulAut (IrreducibleCharacter.inertia N θ))
    (p : ℕ) :=
  ActionInvariantPPrimeIrreducibleCharactersOverAlong
    action (inertiaInclusion N θ) θ p

/-- Self-conjugation-invariant ordinary characters in an inertia fibre. -/
abbrev SelfConjugationInvariantIrreducibleCharactersOverInertia :=
  ActionInvariantIrreducibleCharactersOverInertia N θ
    (MulAut.conj :
      IrreducibleCharacter.inertia N θ →*
        MulAut (IrreducibleCharacter.inertia N θ))

/-- Self-conjugation-invariant prime-to-`p` characters in an inertia
fibre. -/
abbrev SelfConjugationInvariantPPrimeIrreducibleCharactersOverInertia
    (p : ℕ) :=
  ActionInvariantPPrimeIrreducibleCharactersOverInertia N θ
    (MulAut.conj :
      IrreducibleCharacter.inertia N θ →*
        MulAut (IrreducibleCharacter.inertia N θ))
    p

/-- Self-conjugation invariance can be erased from an ordinary inertia
fibre. -/
def selfConjugationInvariantIrreducibleCharactersOverInertiaEquiv :
    SelfConjugationInvariantIrreducibleCharactersOverInertia
        N θ ≃
      IrreducibleCharactersOverInertia N θ :=
  selfConjugationInvariantIrreducibleCharactersOverAlongEquiv
    (inertiaInclusion N θ) θ

/-- Self-conjugation invariance can be erased from a prime-to-`p` inertia
fibre. -/
def selfConjugationInvariantPPrimeIrreducibleCharactersOverInertiaEquiv
    (p : ℕ) :
    SelfConjugationInvariantPPrimeIrreducibleCharactersOverInertia
        N θ p ≃
      PPrimeIrreducibleCharactersOverInertia N θ p :=
  selfConjugationInvariantPPrimeIrreducibleCharactersOverAlongEquiv
    (inertiaInclusion N θ) θ p

/-- If every ordinary character in an inertia fibre has prime-to-`p`
degree, the prime-to-`p` restriction carries no additional data. -/
def pPrimeIrreducibleCharactersOverInertiaEquivOfForallIsPPrimeDegree
    (p : ℕ)
    (hdegree :
      ∀ χ : IrreducibleCharactersOverInertia N θ,
        χ.1.IsPPrimeDegree p) :
    PPrimeIrreducibleCharactersOverInertia N θ p ≃
      IrreducibleCharactersOverInertia N θ :=
  pPrimeIrreducibleCharactersOverAlongEquivOfForallIsPPrimeDegree
    (inertiaInclusion N θ) θ p hdegree

/-- Ordinary self-conjugation invariance does not change the cardinality
of an inertia fibre. -/
theorem natCard_selfConjugationInvariantIrreducibleCharactersOverInertia :
    Nat.card
        (SelfConjugationInvariantIrreducibleCharactersOverInertia
          N θ) =
      Nat.card (IrreducibleCharactersOverInertia N θ) :=
  Nat.card_congr
    (selfConjugationInvariantIrreducibleCharactersOverInertiaEquiv
      N θ)

/-- Prime-to-`p` self-conjugation invariance does not change the
cardinality of an inertia fibre. -/
theorem natCard_selfConjugationInvariantPPrimeIrreducibleCharactersOverInertia
    (p : ℕ) :
    Nat.card
        (SelfConjugationInvariantPPrimeIrreducibleCharactersOverInertia
          N θ p) =
      Nat.card
        (PPrimeIrreducibleCharactersOverInertia N θ p) :=
  Nat.card_congr
    (selfConjugationInvariantPPrimeIrreducibleCharactersOverInertiaEquiv
      N θ p)

/-- Under a pointwise prime-to-`p` degree hypothesis, restricting an
ordinary inertia fibre to prime-to-`p` degree does not change its
cardinality. -/
theorem
    natCard_pPrimeIrreducibleCharactersOverInertia_eq_of_forall_isPPrimeDegree
    (p : ℕ)
    (hdegree :
      ∀ χ : IrreducibleCharactersOverInertia N θ,
        χ.1.IsPPrimeDegree p) :
    Nat.card
        (PPrimeIrreducibleCharactersOverInertia N θ p) =
      Nat.card (IrreducibleCharactersOverInertia N θ) :=
  Nat.card_congr
    (pPrimeIrreducibleCharactersOverInertiaEquivOfForallIsPPrimeDegree
      N θ p hdegree)

end Inertia

end CliffordCorrespondence
end McKayConjecture
