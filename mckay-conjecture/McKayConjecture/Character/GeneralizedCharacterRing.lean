/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionPointwiseRing
import McKayConjecture.Character.GeneralizedCharacter
import McKayConjecture.Character.Multiplicity
import McKayConjecture.Character.Tensor
import McKayConjecture.Character.Trivial

/-!
# The ring of integral generalized characters

Characters of finite-dimensional representations are nonnegative integral
combinations of irreducible characters.  Tensor products multiply
characters pointwise, so integral generalized characters form a subring of
the pointwise class-function ring.

This closure is the representation-ring input in the ideal step of
Brauer induction.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidalCategory

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- The character of every finite-dimensional representation is an
integral generalized character. -/
theorem isGeneralizedCharacter_characterClassFunction
    (V : FDRep ℂ G) :
    IsGeneralizedCharacter
      (FDRep.characterClassFunction V) := by
  rw [isGeneralizedCharacter_iff_pairings_integral]
  intro χ
  refine
    ⟨(IrreducibleCharacter.multiplicity χ V : ℤ), ?_⟩
  letI : Fintype G := Fintype.ofFinite _
  change
    ClassFunction.characterPairing
        (FDRep.characterClassFunction V)
        χ.toClassFunction =
      ((IrreducibleCharacter.multiplicity χ V : ℤ) : ℂ)
  rw [IrreducibleCharacter.characterPairing_eq_multiplicity]
  norm_num

/-- Every irreducible character is an integral generalized character. -/
theorem isGeneralizedCharacter_irreducible
    (χ : IrreducibleCharacter G) :
    IsGeneralizedCharacter χ.toClassFunction := by
  have h :=
    isGeneralizedCharacter_characterClassFunction
      χ.realization
  convert h using 1
  apply ClassFunction.ext
  intro g
  exact
    (congrFun χ.realization_character g).symm

/-- The pointwise product of two irreducible characters is a generalized
character, being the character of their tensor product. -/
theorem isGeneralizedCharacter_mul_irreducible
    (χ ψ : IrreducibleCharacter G) :
    IsGeneralizedCharacter
      (χ.toClassFunction * ψ.toClassFunction) := by
  have htensor :=
    isGeneralizedCharacter_characterClassFunction
      (χ.realization ⊗ ψ.realization)
  convert htensor using 1
  apply ClassFunction.ext
  intro g
  rw [mul_apply]
  change
    χ.values g * ψ.values g =
      (χ.realization ⊗ ψ.realization).character g
  rw [FDRep.char_tensor,
    Pi.mul_apply,
    χ.realization_character,
    ψ.realization_character]

/-- Multiplication by one irreducible character preserves generalized
characters. -/
theorem IsGeneralizedCharacter.mul_irreducible
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (ψ : IrreducibleCharacter G) :
    IsGeneralizedCharacter
      (f * ψ.toClassFunction) := by
  obtain ⟨c, rfl⟩ := hf
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  classical
  rw [IrreducibleCharacter.integerCharacterCombination,
    Finset.sum_mul]
  apply isGeneralizedCharacter_finset_sum
  intro χ _hχ
  have hprod :=
    isGeneralizedCharacter_mul_irreducible χ ψ
  have hz := hprod.zsmul (c χ)
  convert hz using 1
  rw [← Int.cast_smul_eq_zsmul ℂ]
  ext g
  simp

/-- Integral generalized characters are closed under pointwise
multiplication. -/
theorem IsGeneralizedCharacter.mul
    {f k : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (hk : IsGeneralizedCharacter k) :
    IsGeneralizedCharacter (f * k) := by
  obtain ⟨d, rfl⟩ := hk
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  classical
  rw [IrreducibleCharacter.integerCharacterCombination,
    Finset.mul_sum]
  apply isGeneralizedCharacter_finset_sum
  intro ψ _hψ
  have hprod := hf.mul_irreducible ψ
  have hz := hprod.zsmul (d ψ)
  convert hz using 1
  rw [← Int.cast_smul_eq_zsmul ℂ]
  ext g
  simp

/-- Every natural power of a generalized character is generalized. -/
theorem IsGeneralizedCharacter.pow
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (n : ℕ) :
    IsGeneralizedCharacter (f ^ n) := by
  induction n with
  | zero =>
      have hone :
          (1 : ClassFunction G) =
            FDRep.characterClassFunction
              (IrreducibleCharacter.trivial G).realization := by
        apply ClassFunction.ext
        intro g
        rw [one_apply]
        change
          1 =
            (IrreducibleCharacter.trivial G).realization.character g
        rw [
          (IrreducibleCharacter.trivial G).realization_character,
          IrreducibleCharacter.trivial_values]
      rw [pow_zero, hone]
      exact
        isGeneralizedCharacter_characterClassFunction
          (IrreducibleCharacter.trivial G).realization
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul hf

/-- Integral generalized characters as a subring of all complex class
functions. -/
def generalizedCharacterSubring :
    Subring (ClassFunction G) where
  carrier := {f | IsGeneralizedCharacter f}
  zero_mem' := isGeneralizedCharacter_zero
  one_mem' := by
    have h :=
      isGeneralizedCharacter_characterClassFunction
        (IrreducibleCharacter.trivial G).realization
    have hone :
        (1 : ClassFunction G) =
          FDRep.characterClassFunction
            (IrreducibleCharacter.trivial G).realization := by
      apply ClassFunction.ext
      intro g
      rw [one_apply]
      change
        1 =
          (IrreducibleCharacter.trivial G).realization.character g
      rw [
        (IrreducibleCharacter.trivial G).realization_character,
        IrreducibleCharacter.trivial_values]
    rw [hone]
    exact h
  add_mem' := IsGeneralizedCharacter.add
  neg_mem' := IsGeneralizedCharacter.neg
  mul_mem' := IsGeneralizedCharacter.mul

end ClassFunction
end McKayConjecture
