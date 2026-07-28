/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionCosetFormula
import McKayConjecture.Character.CyclotomicGeneralizedCharacter
import McKayConjecture.Character.InductionCharacter

/-!
# Integer-valued cyclotomic generalized characters

Bernstein's short proof of Brauer induction works inside the ring `Q_n(G)`
of class functions which are simultaneously

* integral linear combinations of irreducible characters with coefficients
  in the evaluated integral cyclotomic ring of index `n`; and
* integer-valued.

This file defines that ring and proves the functorial facts needed in the
ideal argument: restriction and subgroup induction preserve it.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G H : Type}
variable [Group G] [Group H] [Finite G] [Finite H]

noncomputable local instance cyclotomicIntegerCharacterFintypeG :
    Fintype G :=
  Fintype.ofFinite _

noncomputable local instance cyclotomicIntegerCharacterFintypeH :
    Fintype H :=
  Fintype.ofFinite _

/-- A complex class function whose values are rational integers. -/
def IsIntegerValued (f : ClassFunction G) : Prop :=
  ∀ g : G, ∃ z : ℤ, f g = (z : ℂ)

/-- The zero class function is integer-valued. -/
theorem isIntegerValued_zero :
    IsIntegerValued (0 : ClassFunction G) := by
  intro g
  exact ⟨0, by simp⟩

/-- The constant-one class function is integer-valued. -/
theorem isIntegerValued_one :
    IsIntegerValued (1 : ClassFunction G) := by
  intro g
  exact ⟨1, by simp⟩

/-- Integer-valued class functions are closed under addition. -/
theorem IsIntegerValued.add
    {f k : ClassFunction G}
    (hf : IsIntegerValued f)
    (hk : IsIntegerValued k) :
    IsIntegerValued (f + k) := by
  intro g
  obtain ⟨a, ha⟩ := hf g
  obtain ⟨b, hb⟩ := hk g
  exact ⟨a + b, by simp [ha, hb]⟩

/-- Integer-valued class functions are closed under negation. -/
theorem IsIntegerValued.neg
    {f : ClassFunction G}
    (hf : IsIntegerValued f) :
    IsIntegerValued (-f) := by
  intro g
  obtain ⟨a, ha⟩ := hf g
  exact ⟨-a, by simp [ha]⟩

/-- Integer-valued class functions are closed under subtraction. -/
theorem IsIntegerValued.sub
    {f k : ClassFunction G}
    (hf : IsIntegerValued f)
    (hk : IsIntegerValued k) :
    IsIntegerValued (f - k) := by
  simpa only [sub_eq_add_neg] using hf.add hk.neg

/-- Integer-valued class functions are closed under multiplication. -/
theorem IsIntegerValued.mul
    {f k : ClassFunction G}
    (hf : IsIntegerValued f)
    (hk : IsIntegerValued k) :
    IsIntegerValued (f * k) := by
  intro g
  obtain ⟨a, ha⟩ := hf g
  obtain ⟨b, hb⟩ := hk g
  exact ⟨a * b, by simp [ha, hb]⟩

/-- Integer-valued class functions are closed under natural powers. -/
theorem IsIntegerValued.pow
    {f : ClassFunction G}
    (hf : IsIntegerValued f)
    (m : ℕ) :
    IsIntegerValued (f ^ m) := by
  intro g
  obtain ⟨a, ha⟩ := hf g
  exact ⟨a ^ m, by simp [ha]⟩

/-- A finite sum of integer-valued class functions is integer-valued. -/
theorem isIntegerValued_finset_sum
    {ι : Type}
    (s : Finset ι)
    (f : ι → ClassFunction G)
    (hf : ∀ i ∈ s, IsIntegerValued (f i)) :
    IsIntegerValued (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isIntegerValued_zero (G := G))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact
        (hf a (Finset.mem_insert_self a s)).add
          (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Pullback along a homomorphism preserves integer values. -/
theorem IsIntegerValued.comap
    (φ : H →* G)
    {f : ClassFunction G}
    (hf : IsIntegerValued f) :
    IsIntegerValued (comapLinearMap φ f) := by
  intro h
  exact hf (φ h)

/-- Every individual coset summand in the induction formula for an
integer-valued class function is an integer. -/
theorem IsIntegerValued.inductionTerm
    (S : Subgroup G)
    {θ : ClassFunction S}
    (hθ : IsIntegerValued θ)
    (x g : G) :
    ∃ z : ℤ, inductionTerm S θ x g = (z : ℂ) := by
  classical
  by_cases hx : x⁻¹ * g * x ∈ S
  · rw [inductionTerm_of_mem S θ hx]
    exact hθ ⟨x⁻¹ * g * x, hx⟩
  · exact ⟨0, by simp [inductionTerm_of_not_mem S θ hx]⟩

/-- Subgroup induction preserves integer-valued class functions.  The
right-coset form of the induction formula is crucial here: it contains no
division by the subgroup order. -/
theorem IsIntegerValued.induce
    (S : Subgroup G)
    {θ : ClassFunction S}
    (hθ : IsIntegerValued θ) :
    IsIntegerValued (induce S θ) := by
  letI : Fintype G := Fintype.ofFinite _
  letI : Fintype (G ⧸ S) := Fintype.ofFinite _
  intro g
  classical
  rw [induce_apply_eq_sum_quotient S θ g]
  choose z hz using
    fun q : G ⧸ S =>
      hθ.inductionTerm S q.out g
  refine ⟨∑ q : G ⧸ S, z q, ?_⟩
  simp only [Int.cast_sum]
  exact Finset.sum_congr rfl fun q _hq => hz q

/-- Subgroup induction preserves cyclotomic generalized characters. -/
theorem IsCyclotomicGeneralizedCharacter.induce
    {n : ℕ} {hn : 0 < n}
    (S : Subgroup G)
    {θ : ClassFunction S}
    (hθ : IsCyclotomicGeneralizedCharacter n hn θ) :
    IsCyclotomicGeneralizedCharacter n hn (induce S θ) := by
  obtain ⟨c, rfl⟩ := hθ
  letI : Fintype G := Fintype.ofFinite _
  letI : Fintype (IrreducibleCharacter S) :=
    Fintype.ofFinite _
  classical
  rw [← induceLinearMap_apply,
    cyclotomicCharacterCombination, map_sum]
  apply isCyclotomicGeneralizedCharacter_finset_sum
  intro χ _hχ
  rw [map_smul]
  have hcharacter :
      χ.realization.characterClassFunction =
        χ.toClassFunction := by
    ext s
    exact congrFun χ.realization_character s
  have hinduced :
      (FDRep.ind S.subtype χ.realization).characterClassFunction =
        ClassFunction.induce S χ.toClassFunction := by
    rw [
      InductionCharacter.ind_characterClassFunction_eq_induce
        S χ.realization,
      hcharacter]
  have hgeneralized :
      IsGeneralizedCharacter
        (ClassFunction.induce S χ.toClassFunction) := by
    rw [← hinduced]
    exact
      isGeneralizedCharacter_characterClassFunction
        (FDRep.ind S.subtype χ.realization)
  exact
    (hgeneralized.isCyclotomic n hn).smul
      (c χ)

/-- Membership in Bernstein's ring `Q_n(G)`: cyclotomic generalized and
integer-valued. -/
def IsCyclotomicIntegerCharacter
    (n : ℕ) (hn : 0 < n)
    (f : ClassFunction G) : Prop :=
  IsCyclotomicGeneralizedCharacter n hn f ∧
    IsIntegerValued f

/-- Cyclotomic integer characters are closed under addition. -/
theorem IsCyclotomicIntegerCharacter.add
    {n : ℕ} {hn : 0 < n}
    {f k : ClassFunction G}
    (hf : IsCyclotomicIntegerCharacter n hn f)
    (hk : IsCyclotomicIntegerCharacter n hn k) :
    IsCyclotomicIntegerCharacter n hn (f + k) :=
  ⟨hf.1.add hk.1, hf.2.add hk.2⟩

/-- Cyclotomic integer characters are closed under negation. -/
theorem IsCyclotomicIntegerCharacter.neg
    {n : ℕ} {hn : 0 < n}
    {f : ClassFunction G}
    (hf : IsCyclotomicIntegerCharacter n hn f) :
    IsCyclotomicIntegerCharacter n hn (-f) :=
  ⟨hf.1.neg, hf.2.neg⟩

/-- Cyclotomic integer characters are closed under multiplication. -/
theorem IsCyclotomicIntegerCharacter.mul
    {n : ℕ} {hn : 0 < n}
    {f k : ClassFunction G}
    (hf : IsCyclotomicIntegerCharacter n hn f)
    (hk : IsCyclotomicIntegerCharacter n hn k) :
    IsCyclotomicIntegerCharacter n hn (f * k) :=
  ⟨hf.1.mul hk.1, hf.2.mul hk.2⟩

/-- Cyclotomic integer characters are closed under natural powers. -/
theorem IsCyclotomicIntegerCharacter.pow
    {n : ℕ} {hn : 0 < n}
    {f : ClassFunction G}
    (hf : IsCyclotomicIntegerCharacter n hn f)
    (m : ℕ) :
    IsCyclotomicIntegerCharacter n hn (f ^ m) :=
  ⟨hf.1.pow m, hf.2.pow m⟩

/-- Bernstein's ring `Q_n(G)` of integer-valued cyclotomic generalized
characters. -/
def cyclotomicIntegerCharacterSubring
    (n : ℕ) (hn : 0 < n) :
    Subring (ClassFunction G) where
  carrier := {f | IsCyclotomicIntegerCharacter n hn f}
  zero_mem' :=
    ⟨isCyclotomicGeneralizedCharacter_zero n hn,
      isIntegerValued_zero⟩
  one_mem' :=
    ⟨(generalizedCharacterSubring
        (G := G)).one_mem.isCyclotomic n hn,
      isIntegerValued_one⟩
  add_mem' := IsCyclotomicIntegerCharacter.add
  neg_mem' := IsCyclotomicIntegerCharacter.neg
  mul_mem' := IsCyclotomicIntegerCharacter.mul

/-- Restriction carries `Q_n(G)` into `Q_n(H)`. -/
theorem IsCyclotomicIntegerCharacter.comap
    {n : ℕ} {hn : 0 < n}
    (φ : H →* G)
    {f : ClassFunction G}
    (hf : IsCyclotomicIntegerCharacter n hn f) :
    IsCyclotomicIntegerCharacter n hn
      (comapLinearMap φ f) :=
  ⟨hf.1.comap φ, hf.2.comap φ⟩

/-- Subgroup induction carries `Q_n(S)` into `Q_n(G)`. -/
theorem IsCyclotomicIntegerCharacter.induce
    {n : ℕ} {hn : 0 < n}
    (S : Subgroup G)
    {θ : ClassFunction S}
    (hθ : IsCyclotomicIntegerCharacter n hn θ) :
    IsCyclotomicIntegerCharacter n hn
      (induce S θ) :=
  ⟨hθ.1.induce S, hθ.2.induce S⟩

end ClassFunction
end McKayConjecture
