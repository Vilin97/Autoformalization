/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import McKayConjecture.Character.BrauerInductionGlobalCyclotomicExpansion

/-!
# The global Bernstein element

Summing the global fibres over all `p`-regular conjugacy classes produces
one class function.  At each group element exactly one summand survives,
and its value is a natural number prime to `p`.

The same sum of the common-cyclotomic coefficient families evaluates to
this global element.  Fermat--Euler then gives the pointwise prime-power
congruence used in Bernstein's power argument, independently of any
subsequent ideal packaging.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {p : ℕ}
variable {G : Type} [Group G] [Finite G] [Fact p.Prime]

noncomputable local instance bernsteinElementFiniteClasses :
    Finite (PRegularConjClasses p G) :=
  Finite.of_injective
    Subtype.val Subtype.val_injective

noncomputable local instance bernsteinElementFintypeClasses :
    Fintype (PRegularConjClasses p G) :=
  Fintype.ofFinite _

/-- The sum of the global fibres over all `p`-regular conjugacy
classes. -/
def bernsteinElement : ClassFunction G :=
  ∑ q ∈ (Finset.univ :
      Finset (PRegularConjClasses p G)),
    pRegularClassFiber q

/-- The sum of the common-cyclotomic elementary coefficient families of
all global fibres. -/
def bernsteinCyclotomicCoefficients :
    ElementaryInductionTerm G →₀
      CyclotomicCoefficientRing (Nat.card G) :=
  ∑ q ∈ (Finset.univ :
      Finset (PRegularConjClasses p G)),
    pRegularClassCyclotomicCoefficients q

/-- Evaluating the summed common-cyclotomic elementary expansion gives
the Bernstein element. -/
theorem evaluate_bernsteinCyclotomicCoefficients :
    evaluateElementaryInductionCombinationOver
        (Nat.card G) Nat.card_pos
        (bernsteinCyclotomicCoefficients
          (p := p) (G := G)) =
      bernsteinElement (p := p) (G := G) := by
  rw [bernsteinCyclotomicCoefficients,
    evaluateElementaryInductionCombinationOver_finsetSum]
  simp only [evaluate_pRegularClassCyclotomicCoefficients]
  rfl

/-- At a group element, the sum over class fibres collapses to the unique
fibre indexed by its canonical `p`-regular part. -/
theorem bernsteinElement_apply_eq_classFiber
    (g : G) :
    bernsteinElement (p := p) (G := G) g =
      pRegularClassFiber
        (PRegularConjClasses.classOfElement
          (p := p) g) g := by
  classical
  rw [bernsteinElement]
  rw [Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_eq_single_of_mem
  · exact Finset.mem_univ _
  · intro q _hq hq
    apply
      pRegularClassFiber_apply_eq_zero_of_classOfElement_ne
        q g
    exact fun h => hq h.symm

/-- Every pointwise value of the Bernstein element is a natural number
prime to `p`. -/
theorem exists_coprime_nat_bernsteinElement_apply
    (g : G) :
    ∃ k : ℕ, p.Coprime k ∧
      bernsteinElement (p := p) (G := G) g =
        (k : ℂ) := by
  rw [bernsteinElement_apply_eq_classFiber]
  exact
    exists_coprime_nat_pRegularClassFiber_apply
      (p := p) g

/-- Fermat--Euler applied to the pointwise Bernstein value: its
`φ(p^n)`-th power is congruent to `1` modulo `p^n`. -/
theorem exists_bernsteinElement_value_pow_totient_modEq
    (n : ℕ) (g : G) :
    ∃ k : ℕ,
      p.Coprime k ∧
      bernsteinElement (p := p) (G := G) g =
        (k : ℂ) ∧
      k ^ (p ^ n).totient ≡ 1 [MOD p ^ n] := by
  obtain ⟨k, hk, hvalue⟩ :=
    exists_coprime_nat_bernsteinElement_apply
      (p := p) g
  refine ⟨k, hk, hvalue, ?_⟩
  exact
    Nat.ModEq.pow_totient
      (hk.symm.pow_right n)

/-- Complex-value form of the pointwise Euler statement, retaining the
natural representative that satisfies the modular congruence. -/
theorem exists_bernsteinElement_pow_eq_nat_modEq
    (n : ℕ) (g : G) :
    ∃ k : ℕ,
      k ≡ 1 [MOD p ^ n] ∧
      bernsteinElement (p := p) (G := G) g ^
          (p ^ n).totient =
        (k : ℂ) := by
  obtain ⟨m, _hm, hvalue, hmod⟩ :=
    exists_bernsteinElement_value_pow_totient_modEq
      (p := p) n g
  refine
    ⟨m ^ (p ^ n).totient, hmod, ?_⟩
  rw [hvalue]
  norm_cast

/-- Exact divisibility form of the pointwise Euler congruence.  The
difference between the powered Bernstein value and `1` is an integral
multiple of `p^n`. -/
theorem exists_int_bernsteinElement_pow_eq_one_add_primePower_mul
    (n : ℕ) (g : G) :
    ∃ z : ℤ,
      bernsteinElement (p := p) (G := G) g ^
          (p ^ n).totient =
        1 + (p ^ n : ℂ) * (z : ℂ) := by
  obtain ⟨k, hmod, hvalue⟩ :=
    exists_bernsteinElement_pow_eq_nat_modEq
      (p := p) n g
  obtain ⟨z, hz⟩ := hmod.dvd
  refine ⟨-z, ?_⟩
  rw [hvalue]
  have hz' :
      (k : ℤ) =
        1 + (p ^ n : ℤ) * (-z) := by
    rw [Nat.cast_pow] at hz
    norm_num only [Nat.cast_one] at hz
    calc
      (k : ℤ) =
          1 - (1 - (k : ℤ)) := by ring
      _ =
          1 - (p : ℤ) ^ n * z := by rw [hz]
      _ =
          1 + (p : ℤ) ^ n * (-z) := by ring
  exact_mod_cast hz'

end ClassFunction
end McKayConjecture
