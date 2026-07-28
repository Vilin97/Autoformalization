/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordCorrespondence
import McKayConjecture.Character.DegreeOneLinear
import McKayConjecture.Character.Determination
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# Restriction multiplicities of linear characters

The restriction of a degree-one irreducible character along an arbitrary
group homomorphism is again a degree-one irreducible character.  It occurs
with multiplicity one, and every other irreducible character occurs with
multiplicity zero.

For the Glauberman correspondence this settles the constituent and
uniqueness clauses for every invariant linear character.  No coprime-action
hypothesis is needed for this part.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

variable {G : Type u} {H : Type v}
variable [Group G] [Group H]

/-- Every irreducible complex character of a commutative group has degree
one. -/
theorem degree_eq_one_of_isMulCommutative
    [IsMulCommutative G]
    (χ : IrreducibleCharacter G) :
    χ.degree = 1 := by
  rw [← χ.realization_finrank]
  exact
    (CliffordRestriction.isIrreducible_of_simple
      χ.realization).finrank_eq_one_of_isMulCommutative

/-- Restrict a degree-one irreducible character along an arbitrary group
homomorphism. -/
def linearRestriction
    (f : H →* G)
    (χ : IrreducibleCharacter G)
    (hχ : χ.degree = 1) :
    IrreducibleCharacter H :=
  linear
    ((linearParameterOfDegreeOne χ hχ).comp f)

@[simp]
theorem linearRestriction_values
    (f : H →* G)
    (χ : IrreducibleCharacter G)
    (hχ : χ.degree = 1)
    (h : H) :
    (linearRestriction f χ hχ).values h =
      χ.values (f h) := by
  rw [linearRestriction, linear_values,
    MonoidHom.comp_apply,
    linearParameterOfDegreeOne_values]

@[simp]
theorem linearRestriction_degree
    (f : H →* G)
    (χ : IrreducibleCharacter G)
    (hχ : χ.degree = 1) :
    (linearRestriction f χ hχ).degree = 1 :=
  linear_degree _

/-- Prime-to-`p` irreducible characters of a commutative group are
exactly its multiplicative complex characters.  Finiteness is not needed:
commutativity alone forces every finite-dimensional simple complex
representation to have dimension one. -/
def commutativePPrimeLinearEquiv
    [IsMulCommutative G]
    (p : ℕ) [Fact p.Prime] :
    PPrimeIrreducibleCharacter G p ≃
      (G →* ℂˣ) where
  toFun χ :=
    linearParameterOfDegreeOne χ.1
      (degree_eq_one_of_isMulCommutative χ.1)
  invFun lam :=
    ⟨linear lam, linear_isPPrimeDegree lam p⟩
  left_inv χ := by
    apply Subtype.ext
    exact
      linear_linearParameterOfDegreeOne χ.1
        (degree_eq_one_of_isMulCommutative χ.1)
  right_inv lam := by
    apply linear_injective
    exact
      linear_linearParameterOfDegreeOne
        (linear lam) (linear_degree lam)

@[simp]
theorem commutativePPrimeLinearEquiv_apply
    [IsMulCommutative G]
    (p : ℕ) [Fact p.Prime]
    (χ : PPrimeIrreducibleCharacter G p) :
    commutativePPrimeLinearEquiv p χ =
      linearParameterOfDegreeOne χ.1
        (degree_eq_one_of_isMulCommutative χ.1) :=
  rfl

@[simp]
theorem commutativePPrimeLinearEquiv_symm_apply_coe
    [IsMulCommutative G]
    (p : ℕ) [Fact p.Prime]
    (lam : G →* ℂˣ) :
    ((commutativePPrimeLinearEquiv p).symm lam).1 =
      linear lam :=
  rfl

end IrreducibleCharacter

namespace CliffordCorrespondence

variable {G H : Type}
variable [Group G] [Group H] [Finite H]

/-- The restricted linear character occurs with multiplicity one. -/
theorem restrictionMultiplicity_linearRestriction_eq_one
    (f : H →* G)
    (χ : IrreducibleCharacter G)
    (hχ : χ.degree = 1) :
    restrictionMultiplicity f
      (χ.linearRestriction f hχ) χ = 1 := by
  letI : Fintype H := Fintype.ofFinite H
  let W : FDRep ℂ H :=
    FDRep.res f χ.realization
  have hchar :
      W.character =
        (χ.linearRestriction f hχ).values := by
    funext h
    rw [FDRep.res_character_apply,
      χ.realization_character,
      IrreducibleCharacter.linearRestriction_values]
  letI : Simple W := by
    rw [FDRep.simple_iff_char_is_norm_one]
    rw [hchar,
      ← (χ.linearRestriction f hχ).realization_character]
    exact
      (FDRep.simple_iff_char_is_norm_one
        (χ.linearRestriction f hχ).realization).mp
        inferInstance
  obtain ⟨i :
      (χ.linearRestriction f hχ).realization ≅ W⟩ :=
    FDRep.nonempty_iso_of_character_eq
      (χ.linearRestriction f hχ).realization W (by
        rw [
          (χ.linearRestriction f hχ).realization_character,
          hchar])
  exact
    (finrank_hom_simple_simple_eq_one_iff
      ℂ (χ.linearRestriction f hχ).realization W).2
      ⟨i⟩

/-- Every other irreducible character has multiplicity zero in the
restriction of a linear character. -/
theorem restrictionMultiplicity_linearRestriction_eq_zero_of_ne
    (f : H →* G)
    (χ : IrreducibleCharacter G)
    (hχ : χ.degree = 1)
    (η : IrreducibleCharacter H)
    (hne : η ≠ χ.linearRestriction f hχ) :
    restrictionMultiplicity f η χ = 0 := by
  letI : Fintype H := Fintype.ofFinite H
  let W : FDRep ℂ H :=
    FDRep.res f χ.realization
  have hchar :
      W.character =
        (χ.linearRestriction f hχ).values := by
    funext h
    rw [FDRep.res_character_apply,
      χ.realization_character,
      IrreducibleCharacter.linearRestriction_values]
  letI : Simple W := by
    rw [FDRep.simple_iff_char_is_norm_one]
    rw [hchar,
      ← (χ.linearRestriction f hχ).realization_character]
    exact
      (FDRep.simple_iff_char_is_norm_one
        (χ.linearRestriction f hχ).realization).mp
        inferInstance
  apply
    (finrank_hom_simple_simple_eq_zero_iff
      ℂ η.realization W).2
  exact
    ⟨fun i ↦ hne (by
      apply IrreducibleCharacter.ext
      exact η.realization_character.symm.trans
        ((FDRep.char_iso i).trans hchar))⟩

end CliffordCorrespondence
end McKayConjecture
