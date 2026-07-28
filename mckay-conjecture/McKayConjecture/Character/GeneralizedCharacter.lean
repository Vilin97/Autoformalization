/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionCompleteness
import McKayConjecture.Character.ClassFunctionRestriction
import McKayConjecture.Character.RestrictionMultiplicityPairing

/-!
# Integral generalized characters

An integral generalized character of a finite group is an integral linear
combination of its ordinary irreducible complex characters.  This file gives
that definition as a property of class functions, proves the equivalent
Fourier-coefficient criterion, and proves that generalized characters pull
back along arbitrary homomorphisms of finite groups.

The last result supplies one direction of the restriction technology used in
Brauer's characterization of generalized characters.  The converse local-to-
global implication over elementary subgroups is a separate, substantive
theorem and is not assumed here.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G H : Type} [Group G] [Group H]

/-- A complex class function is an integral generalized character when it is
an integral linear combination of irreducible ordinary characters. -/
def IsGeneralizedCharacter [Finite G] (f : ClassFunction G) : Prop :=
  ∃ c : IrreducibleCharacter G → ℤ,
    f = IrreducibleCharacter.integerCharacterCombination c

variable [Finite G]

/-- An integral irreducible-character combination is a generalized
character. -/
theorem isGeneralizedCharacter_integerCharacterCombination
    (c : IrreducibleCharacter G → ℤ) :
    IsGeneralizedCharacter
      (IrreducibleCharacter.integerCharacterCombination c) :=
  ⟨c, rfl⟩

/-- The zero class function is a generalized character. -/
theorem isGeneralizedCharacter_zero :
    IsGeneralizedCharacter (0 : ClassFunction G) := by
  refine ⟨0, ?_⟩
  classical
  simp [IrreducibleCharacter.integerCharacterCombination]

/-- Generalized characters are closed under addition. -/
theorem IsGeneralizedCharacter.add
    {f k : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (hk : IsGeneralizedCharacter k) :
    IsGeneralizedCharacter (f + k) := by
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨d, rfl⟩ := hk
  refine ⟨c + d, ?_⟩
  classical
  simp only [IrreducibleCharacter.integerCharacterCombination,
    Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]

/-- Generalized characters are closed under negation. -/
theorem IsGeneralizedCharacter.neg
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) :
    IsGeneralizedCharacter (-f) := by
  obtain ⟨c, rfl⟩ := hf
  refine ⟨-c, ?_⟩
  classical
  apply ClassFunction.ext
  intro g
  simp [IrreducibleCharacter.integerCharacterCombination]

/-- Generalized characters are closed under subtraction. -/
theorem IsGeneralizedCharacter.sub
    {f k : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (hk : IsGeneralizedCharacter k) :
    IsGeneralizedCharacter (f - k) := by
  simpa only [sub_eq_add_neg] using hf.add hk.neg

/-- Generalized characters are closed under integral scalar multiplication. -/
theorem IsGeneralizedCharacter.zsmul
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f)
    (n : ℤ) :
    IsGeneralizedCharacter (n • f) := by
  obtain ⟨c, rfl⟩ := hf
  refine ⟨n • c, ?_⟩
  classical
  rw [← Int.cast_smul_eq_zsmul ℂ]
  simp [IrreducibleCharacter.integerCharacterCombination,
    Finset.smul_sum, smul_smul]

/-- A finite sum of generalized characters is generalized. -/
theorem isGeneralizedCharacter_finset_sum
    {ι : Type} (s : Finset ι) (f : ι → ClassFunction G)
    (hf : ∀ i ∈ s, IsGeneralizedCharacter (f i)) :
    IsGeneralizedCharacter (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isGeneralizedCharacter_zero (G := G))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- A class function is generalized exactly when every irreducible Fourier
coefficient is an ordinary integer. -/
theorem isGeneralizedCharacter_iff_pairings_integral
    (f : ClassFunction G) :
    IsGeneralizedCharacter f ↔
      ∀ χ : IrreducibleCharacter G,
        ∃ z : ℤ,
          normalizedPairing f χ.toClassFunction = (z : ℂ) := by
  constructor
  · rintro ⟨c, rfl⟩ χ
    exact
      ⟨c χ,
        IrreducibleCharacter.normalizedPairing_integerCharacterCombination_irreducible c χ⟩
  · exact exists_integerCharacterCombination_of_pairings_integral f

/-- The integral coefficient family of a generalized character is unique. -/
theorem integerCharacterCombination_injective :
    Function.Injective
      (IrreducibleCharacter.integerCharacterCombination :
        (IrreducibleCharacter G → ℤ) → ClassFunction G) := by
  intro c d h
  funext χ
  have hcast : (c χ : ℂ) = (d χ : ℂ) := by
    rw [← IrreducibleCharacter.normalizedPairing_integerCharacterCombination_irreducible c χ,
      ← IrreducibleCharacter.normalizedPairing_integerCharacterCombination_irreducible d χ, h]
  exact Int.cast_injective hcast

/-- Restricting an irreducible character gives a generalized character. -/
theorem isGeneralizedCharacter_comap_irreducible
    [Finite H] (φ : H →* G)
    (χ : IrreducibleCharacter G) :
    IsGeneralizedCharacter
      (comapLinearMap φ χ.toClassFunction) := by
  have hres :
      comapLinearMap φ χ.toClassFunction =
        FDRep.characterClassFunction
          (FDRep.res φ χ.realization) := by
    ext h
    change χ.values (φ h) = χ.realization.character (φ h)
    rw [χ.realization_character]
  rw [hres,
    CliffordCorrespondence.restrictedCharacter_eq_integerCharacterCombination]
  exact isGeneralizedCharacter_integerCharacterCombination _

/-- Pullback along a homomorphism of finite groups preserves generalized
characters.  In particular, restriction to every subgroup preserves them. -/
theorem IsGeneralizedCharacter.comap
    [Finite H] (φ : H →* G)
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) :
    IsGeneralizedCharacter (comapLinearMap φ f) := by
  obtain ⟨c, rfl⟩ := hf
  letI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  classical
  rw [IrreducibleCharacter.integerCharacterCombination,
    map_sum]
  apply isGeneralizedCharacter_finset_sum
  intro χ _hχ
  rw [map_smul]
  have hχ :
      IsGeneralizedCharacter
        (comapLinearMap φ χ.toClassFunction) :=
    isGeneralizedCharacter_comap_irreducible φ χ
  have hz :
      IsGeneralizedCharacter
        (c χ • comapLinearMap φ χ.toClassFunction) :=
    hχ.zsmul (c χ)
  have heq :
      (c χ : ℂ) • comapLinearMap φ χ.toClassFunction =
        (c χ : ℤ) • comapLinearMap φ χ.toClassFunction :=
    Int.cast_smul_eq_zsmul ℂ (c χ)
      (comapLinearMap φ χ.toClassFunction)
  rw [heq]
  exact hz

end ClassFunction
end McKayConjecture
