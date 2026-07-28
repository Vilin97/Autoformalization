/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionCyclotomicLift
import McKayConjecture.Character.GeneralizedCharacterRing

/-!
# Generalized characters with integral cyclotomic coefficients

Fix a positive integer `n` and evaluate the integral cyclotomic ring
`CyclotomicCoefficientRing n` in `ℂ`.  A cyclotomic generalized character
is a class function that is a finite linear combination of irreducible
characters with coefficients in the image of that evaluation.

For finite groups these functions form a subring.  Integral generalized
characters embed by casting their integral coefficients, and restriction
along a homomorphism preserves cyclotomic generalized characters.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G H : Type}
variable [Group G] [Group H] [Finite G] [Finite H]

/-- Evaluate a full irreducible coefficient vector in the `n`-th integral
cyclotomic ring. -/
def cyclotomicCharacterCombination
    (n : ℕ) (hn : 0 < n)
    (c :
      IrreducibleCharacter G →
        CyclotomicCoefficientRing n) :
    ClassFunction G := by
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  exact
    ∑ χ : IrreducibleCharacter G,
      cyclotomicCoefficientEvaluation n hn (c χ) •
        χ.toClassFunction

/-- A class function is a generalized character over the evaluated
integral `n`-th cyclotomic coefficient ring. -/
def IsCyclotomicGeneralizedCharacter
    (n : ℕ) (hn : 0 < n)
    (f : ClassFunction G) : Prop :=
  ∃ c :
      IrreducibleCharacter G →
        CyclotomicCoefficientRing n,
    f = cyclotomicCharacterCombination n hn c

/-- Integral generalized characters are cyclotomic generalized characters
for every positive cyclotomic index. -/
theorem IsGeneralizedCharacter.isCyclotomic
    (n : ℕ) (hn : 0 < n)
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) :
    IsCyclotomicGeneralizedCharacter n hn f := by
  obtain ⟨c, rfl⟩ := hf
  refine
    ⟨fun χ =>
      (c χ : CyclotomicCoefficientRing n), ?_⟩
  classical
  simp only [cyclotomicCharacterCombination,
    IrreducibleCharacter.integerCharacterCombination,
    map_intCast]

/-- The zero class function is cyclotomic generalized. -/
theorem isCyclotomicGeneralizedCharacter_zero
    (n : ℕ) (hn : 0 < n) :
    IsCyclotomicGeneralizedCharacter
      (G := G) n hn 0 :=
  (isGeneralizedCharacter_zero (G := G)).isCyclotomic
    n hn

/-- Cyclotomic generalized characters are closed under addition. -/
theorem IsCyclotomicGeneralizedCharacter.add
    {n : ℕ} {hn : 0 < n}
    {f k : ClassFunction G}
    (hf : IsCyclotomicGeneralizedCharacter n hn f)
    (hk : IsCyclotomicGeneralizedCharacter n hn k) :
    IsCyclotomicGeneralizedCharacter n hn (f + k) := by
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨d, rfl⟩ := hk
  refine ⟨c + d, ?_⟩
  classical
  rw [cyclotomicCharacterCombination,
    cyclotomicCharacterCombination,
    cyclotomicCharacterCombination,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro χ _hχ
  simp only [Pi.add_apply, map_add, add_smul]

/-- Cyclotomic generalized characters are closed under negation. -/
theorem IsCyclotomicGeneralizedCharacter.neg
    {n : ℕ} {hn : 0 < n}
    {f : ClassFunction G}
    (hf : IsCyclotomicGeneralizedCharacter n hn f) :
    IsCyclotomicGeneralizedCharacter n hn (-f) := by
  obtain ⟨c, rfl⟩ := hf
  refine ⟨-c, ?_⟩
  classical
  simp [cyclotomicCharacterCombination]

/-- Cyclotomic generalized characters are closed under subtraction. -/
theorem IsCyclotomicGeneralizedCharacter.sub
    {n : ℕ} {hn : 0 < n}
    {f k : ClassFunction G}
    (hf : IsCyclotomicGeneralizedCharacter n hn f)
    (hk : IsCyclotomicGeneralizedCharacter n hn k) :
    IsCyclotomicGeneralizedCharacter n hn (f - k) := by
  simpa only [sub_eq_add_neg] using hf.add hk.neg

/-- Scalar multiplication by a coefficient in the integral cyclotomic
ring preserves cyclotomic generalized characters. -/
theorem IsCyclotomicGeneralizedCharacter.smul
    {n : ℕ} {hn : 0 < n}
    {f : ClassFunction G}
    (hf : IsCyclotomicGeneralizedCharacter n hn f)
    (a : CyclotomicCoefficientRing n) :
    IsCyclotomicGeneralizedCharacter n hn
      (cyclotomicCoefficientEvaluation n hn a • f) := by
  obtain ⟨c, rfl⟩ := hf
  refine ⟨fun χ => a * c χ, ?_⟩
  classical
  simp [cyclotomicCharacterCombination,
    Finset.smul_sum, smul_smul]

/-- A finite sum of cyclotomic generalized characters is cyclotomic
generalized. -/
theorem isCyclotomicGeneralizedCharacter_finset_sum
    {ι : Type} {n : ℕ} {hn : 0 < n}
    (s : Finset ι)
    (f : ι → ClassFunction G)
    (hf :
      ∀ i ∈ s,
        IsCyclotomicGeneralizedCharacter n hn (f i)) :
    IsCyclotomicGeneralizedCharacter n hn
      (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (isCyclotomicGeneralizedCharacter_zero
          (G := G) n hn)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact
        (hf a (Finset.mem_insert_self a s)).add
          (ih fun i hi =>
            hf i (Finset.mem_insert_of_mem hi))

/-- Multiplication by an irreducible character preserves cyclotomic
generalized characters. -/
theorem IsCyclotomicGeneralizedCharacter.mul_irreducible
    {n : ℕ} {hn : 0 < n}
    {f : ClassFunction G}
    (hf : IsCyclotomicGeneralizedCharacter n hn f)
    (ψ : IrreducibleCharacter G) :
    IsCyclotomicGeneralizedCharacter n hn
      (f * ψ.toClassFunction) := by
  obtain ⟨c, rfl⟩ := hf
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  classical
  rw [cyclotomicCharacterCombination,
    Finset.sum_mul]
  apply isCyclotomicGeneralizedCharacter_finset_sum
  intro χ _hχ
  have hprod :
      IsCyclotomicGeneralizedCharacter n hn
        (χ.toClassFunction * ψ.toClassFunction) :=
    (isGeneralizedCharacter_mul_irreducible
      χ ψ).isCyclotomic n hn
  simpa only [smul_mul_assoc] using
    hprod.smul (c χ)

/-- Cyclotomic generalized characters are closed under pointwise
multiplication. -/
theorem IsCyclotomicGeneralizedCharacter.mul
    {n : ℕ} {hn : 0 < n}
    {f k : ClassFunction G}
    (hf : IsCyclotomicGeneralizedCharacter n hn f)
    (hk : IsCyclotomicGeneralizedCharacter n hn k) :
    IsCyclotomicGeneralizedCharacter n hn (f * k) := by
  obtain ⟨d, rfl⟩ := hk
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  classical
  rw [cyclotomicCharacterCombination,
    Finset.mul_sum]
  apply isCyclotomicGeneralizedCharacter_finset_sum
  intro ψ _hψ
  have hprod := hf.mul_irreducible ψ
  simpa only [mul_smul_comm] using
    hprod.smul (d ψ)

/-- Every natural power of a cyclotomic generalized character is
cyclotomic generalized. -/
theorem IsCyclotomicGeneralizedCharacter.pow
    {n : ℕ} {hn : 0 < n}
    {f : ClassFunction G}
    (hf : IsCyclotomicGeneralizedCharacter n hn f)
    (m : ℕ) :
    IsCyclotomicGeneralizedCharacter n hn (f ^ m) := by
  induction m with
  | zero =>
      exact
        (ClassFunction.generalizedCharacterSubring
          (G := G)).one_mem.isCyclotomic n hn
  | succ m ih =>
      rw [pow_succ]
      exact ih.mul hf

/-- Pullback along a homomorphism preserves cyclotomic generalized
characters. -/
theorem IsCyclotomicGeneralizedCharacter.comap
    {n : ℕ} {hn : 0 < n}
    (φ : H →* G)
    {f : ClassFunction G}
    (hf : IsCyclotomicGeneralizedCharacter n hn f) :
    IsCyclotomicGeneralizedCharacter n hn
      (comapLinearMap φ f) := by
  obtain ⟨c, rfl⟩ := hf
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  classical
  rw [cyclotomicCharacterCombination, map_sum]
  apply isCyclotomicGeneralizedCharacter_finset_sum
  intro χ _hχ
  rw [map_smul]
  have hres :
      IsCyclotomicGeneralizedCharacter n hn
        (comapLinearMap φ χ.toClassFunction) :=
    (isGeneralizedCharacter_comap_irreducible
      φ χ).isCyclotomic n hn
  exact hres.smul (c χ)

/-- Cyclotomic generalized characters as a subring of the complex
class-function ring. -/
def cyclotomicGeneralizedCharacterSubring
    (n : ℕ) (hn : 0 < n) :
    Subring (ClassFunction G) where
  carrier := {f |
    IsCyclotomicGeneralizedCharacter n hn f}
  zero_mem' :=
    isCyclotomicGeneralizedCharacter_zero n hn
  one_mem' :=
    (generalizedCharacterSubring
      (G := G)).one_mem.isCyclotomic n hn
  add_mem' := IsCyclotomicGeneralizedCharacter.add
  neg_mem' := IsCyclotomicGeneralizedCharacter.neg
  mul_mem' := IsCyclotomicGeneralizedCharacter.mul

end ClassFunction
end McKayConjecture
