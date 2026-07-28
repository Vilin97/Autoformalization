/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicEightCharacterTable
import McKayConjecture.GroupTheory.AlternatingSixSchurThreeNormalizerSemidirect

/-!
# The eight linear `3'`-rows of the `3^{1+2} ⋊ C₈` normalizer

The concrete normalizer semidirect product has a canonical quotient onto
its `C₈` factor.  Pulling back the eight explicit characters of `C₈`
gives eight pairwise distinct degree-one `3'`-characters.

External computation predicts that the remaining `3'`-table consists of
four degree-four rows.  This file does not assume that prediction.
Instead, `DegreeFourCompletion` states the exact finite obligation needed
to complete the model table: exhibit four degree-four characters and
prove that the resulting twelve rows are bijective.
-/

noncomputable section

namespace McKayConjecture
namespace AlternatingSixThreeNormalizer

open GroupTheory

local instance alternatingSixThreeNormalizerLinearRowsFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The explicit `3^{1+2} ⋊ C₈` group. -/
abbrev Group :=
  AlternatingSixThreeHeisenbergCyclicEightSemidirect

/-- The `j`-th linear homomorphism inflated from the `C₈` quotient. -/
def quotientLinearHom (j : Fin 8) :
    Group →* ℂˣ :=
  (CyclicEight.linearHom j).comp
    SemidirectProduct.rightHom

@[simp]
theorem quotientLinearHom_apply
    (j : Fin 8) (g : Group) :
    quotientLinearHom j g =
      CyclicEight.linearHom j g.right :=
  rfl

@[simp]
theorem quotientLinearHom_inr
    (j : Fin 8) (c : AlternatingSixThreeCyclicEight) :
    quotientLinearHom j (SemidirectProduct.inr c) =
      CyclicEight.linearHom j c := by
  simp [quotientLinearHom]

/-- The eight inflated linear homomorphisms are pairwise distinct. -/
theorem quotientLinearHom_injective :
    Function.Injective quotientLinearHom := by
  intro i j hij
  apply CyclicEight.linearHom_injective
  apply DFunLike.ext
  intro c
  have hc :=
    DFunLike.congr_fun hij
      (SemidirectProduct.inr c :
        Group)
  simpa only [quotientLinearHom_inr] using hc

/-- The inflated degree-one irreducible character. -/
def linearCharacter (j : Fin 8) :
    IrreducibleCharacter Group :=
  IrreducibleCharacter.linear (quotientLinearHom j)

@[simp]
theorem linearCharacter_values
    (j : Fin 8) (g : Group) :
    (linearCharacter j).values g =
      (CyclicEight.linearHom j g.right : ℂ) := by
  rw [linearCharacter, IrreducibleCharacter.linear_values]
  rfl

@[simp]
theorem linearCharacter_degree (j : Fin 8) :
    (linearCharacter j).degree = 1 :=
  IrreducibleCharacter.linear_degree
    (quotientLinearHom j)

theorem linearCharacter_injective :
    Function.Injective linearCharacter :=
  IrreducibleCharacter.linear_injective.comp
    quotientLinearHom_injective

/-- The inflated row as a `3'`-degree irreducible character. -/
def linearPPrimeCharacter (j : Fin 8) :
    PPrimeIrreducibleCharacter Group 3 :=
  ⟨linearCharacter j,
    IrreducibleCharacter.linear_isPPrimeDegree
      (quotientLinearHom j) 3⟩

@[simp]
theorem linearPPrimeCharacter_degree (j : Fin 8) :
    (linearPPrimeCharacter j).1.degree = 1 :=
  linearCharacter_degree j

theorem linearPPrimeCharacter_injective :
    Function.Injective linearPPrimeCharacter := by
  intro i j hij
  apply linearCharacter_injective
  exact congrArg Subtype.val hij

/-- The expected twelve-row index shape, split into the eight already
constructed linear rows and four prospective degree-four rows. -/
abbrev PPrimeCharacterRow :=
  Fin 8 ⊕ Fin 4

/-- The exact residual certificate for completing the `3'`-table of the
semidirect normalizer model.

No existence is asserted here: the four rows and the completeness proof
remain kernel-checked obligations. -/
structure DegreeFourCompletion where
  /-- The four remaining prospective rows. -/
  degreeFourCharacter :
    Fin 4 → PPrimeIrreducibleCharacter Group 3
  /-- Each prospective row has the predicted degree four. -/
  degree_four :
    ∀ j : Fin 4,
      (degreeFourCharacter j).1.degree = 4
  /-- Together with the eight proved linear rows, these are exactly all
  `3'`-degree irreducible characters. -/
  combined_bijective :
    Function.Bijective
      (fun r : PPrimeCharacterRow ↦
        match r with
        | Sum.inl j => linearPPrimeCharacter j
        | Sum.inr j => degreeFourCharacter j)

namespace DegreeFourCompletion

variable (d : DegreeFourCompletion)

/-- The combined twelve-row model enumeration. -/
def pPrimeCharacterEquiv :
    PPrimeCharacterRow ≃
      PPrimeIrreducibleCharacter Group 3 :=
  Equiv.ofBijective
    (fun r : PPrimeCharacterRow ↦
      match r with
      | Sum.inl j => linearPPrimeCharacter j
      | Sum.inr j => d.degreeFourCharacter j)
    d.combined_bijective

@[simp]
theorem pPrimeCharacterEquiv_linear
    (j : Fin 8) :
    d.pPrimeCharacterEquiv (Sum.inl j) =
      linearPPrimeCharacter j :=
  rfl

@[simp]
theorem pPrimeCharacterEquiv_degreeFour
    (j : Fin 4) :
    d.pPrimeCharacterEquiv (Sum.inr j) =
      d.degreeFourCharacter j :=
  rfl

@[simp]
theorem pPrimeCharacterEquiv_degree_linear
    (j : Fin 8) :
    (d.pPrimeCharacterEquiv (Sum.inl j)).1.degree = 1 :=
  linearPPrimeCharacter_degree j

@[simp]
theorem pPrimeCharacterEquiv_degree_degreeFour
    (j : Fin 4) :
    (d.pPrimeCharacterEquiv (Sum.inr j)).1.degree = 4 :=
  d.degree_four j

/-- A completed table has exactly twelve `3'`-rows. -/
theorem natCard_pPrimeIrreducibleCharacter
    (d : DegreeFourCompletion) :
    Nat.card (PPrimeIrreducibleCharacter Group 3) = 12 := by
  calc
      Nat.card (PPrimeIrreducibleCharacter Group 3) =
        Nat.card PPrimeCharacterRow :=
      Nat.card_congr (pPrimeCharacterEquiv d).symm
    _ = 12 := by
      rw [Nat.card_sum, Nat.card_fin, Nat.card_fin]

end DegreeFourCompletion

end AlternatingSixThreeNormalizer
end McKayConjecture
