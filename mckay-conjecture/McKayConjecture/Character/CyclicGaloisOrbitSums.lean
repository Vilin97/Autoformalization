/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Galois orbit sums for cyclic characters

The Galois orbit of a primitive `n`-th root of unity consists of all
primitive `n`-th roots.  Its orbit sum is therefore the negative of
the next coefficient of the integral cyclotomic polynomial, and in
particular is an integer.

This is the cyclotomic arithmetic input in the Artin-induction
argument for cyclic character coefficients.
-/

noncomputable section

open scoped BigOperators

namespace Polynomial

/-- The sum of the primitive `n`-th complex roots of unity is the
negative of the next coefficient of the integral `n`-th cyclotomic
polynomial. -/
theorem sum_primitiveRoots_eq_neg_cyclotomic_nextCoeff
    (n : ℕ) [NeZero n] :
    ∑ ζ ∈ primitiveRoots n ℂ, ζ =
      ((-(cyclotomic n ℤ).nextCoeff : ℤ) : ℂ) := by
  have hnext :
      (cyclotomic n ℂ).nextCoeff =
        -((cyclotomic n ℂ).roots.sum) :=
    (IsAlgClosed.splits (cyclotomic n ℂ)).nextCoeff_eq_neg_sum_roots_of_monic
      (cyclotomic.monic n ℂ)
  rw [cyclotomic.roots_eq_primitiveRoots_val] at hnext
  have hsum :
      ∑ ζ ∈ primitiveRoots n ℂ, ζ =
        -(cyclotomic n ℂ).nextCoeff := by
    rw [Finset.sum_eq_multiset_sum, Multiset.map_id']
    simpa only [neg_neg] using
      (congrArg (fun z : ℂ ↦ -z) hnext).symm
  have hunit : IsUnit (cyclotomic n ℤ).leadingCoeff := by
    rw [(cyclotomic.monic n ℤ).leadingCoeff]
    exact isUnit_one
  rw [hsum, ← map_cyclotomic_int n ℂ,
    nextCoeff_map_eq_of_isUnit_leadingCoeff
      (Int.castRingHom ℂ) hunit]
  simp

/-- The sum of a primitive-root Galois orbit is an integer. -/
theorem exists_int_eq_sum_primitiveRoots
    (n : ℕ) [NeZero n] :
    ∃ z : ℤ, ∑ ζ ∈ primitiveRoots n ℂ, ζ = (z : ℂ) :=
  ⟨-(cyclotomic n ℤ).nextCoeff,
    sum_primitiveRoots_eq_neg_cyclotomic_nextCoeff n⟩

/-- A finite integer linear combination of primitive-root Galois
orbit sums is the corresponding integer linear combination of
cyclotomic coefficients. -/
theorem sum_mul_sum_primitiveRoots_eq_cyclotomic_nextCoeff
    (orders : Finset ℕ) (horders : ∀ n ∈ orders, n ≠ 0)
    (multiplicity : ℕ → ℤ) :
    ∑ n ∈ orders, (multiplicity n : ℂ) *
        (∑ ζ ∈ primitiveRoots n ℂ, ζ) =
      ((∑ n ∈ orders,
          multiplicity n * (-(cyclotomic n ℤ).nextCoeff) : ℤ) : ℂ) := by
  classical
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  letI : NeZero n := ⟨horders n hn⟩
  rw [sum_primitiveRoots_eq_neg_cyclotomic_nextCoeff]
  norm_cast

/-- Consequently, every finite integer linear combination of
primitive-root Galois orbit sums is an integer. -/
theorem exists_int_eq_sum_mul_sum_primitiveRoots
    (orders : Finset ℕ) (horders : ∀ n ∈ orders, n ≠ 0)
    (multiplicity : ℕ → ℤ) :
    ∃ z : ℤ,
      ∑ n ∈ orders, (multiplicity n : ℂ) *
          (∑ ζ ∈ primitiveRoots n ℂ, ζ) = (z : ℂ) :=
  ⟨∑ n ∈ orders,
      multiplicity n * (-(cyclotomic n ℤ).nextCoeff),
    sum_mul_sum_primitiveRoots_eq_cyclotomic_nextCoeff
      orders horders multiplicity⟩

/-- If the integer weight of an `N`-th root depends only on its exact
order, then the weighted sum of the roots is an integer.  This is the
root-multiplicity form of Galois-orbit invariance. -/
theorem sum_nthRoots_of_constant_on_primitiveRoots
    (N : ℕ) [NeZero N]
    (rootMultiplicity : ℂ → ℤ)
    (orbitMultiplicity : ℕ → ℤ)
    (hconstant :
      ∀ d ∈ N.divisors, ∀ ζ ∈ primitiveRoots d ℂ,
        rootMultiplicity ζ = orbitMultiplicity d) :
    ∑ ζ ∈ nthRootsFinset N (1 : ℂ),
        (rootMultiplicity ζ : ℂ) * ζ =
      ((∑ d ∈ N.divisors,
          orbitMultiplicity d *
            (-(cyclotomic d ℤ).nextCoeff) : ℤ) : ℂ) := by
  classical
  have hdisjoint :
      (N.divisors : Set ℕ).PairwiseDisjoint
        (fun d ↦ primitiveRoots d ℂ) :=
    fun d _ e _ hde ↦ IsPrimitiveRoot.disjoint hde
  calc
    ∑ ζ ∈ nthRootsFinset N (1 : ℂ),
          (rootMultiplicity ζ : ℂ) * ζ =
        ∑ d ∈ N.divisors,
          ∑ ζ ∈ primitiveRoots d ℂ,
            (rootMultiplicity ζ : ℂ) * ζ := by
      rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
        Finset.sum_biUnion hdisjoint]
    _ = ∑ d ∈ N.divisors,
          (orbitMultiplicity d : ℂ) *
            (∑ ζ ∈ primitiveRoots d ℂ, ζ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ζ hζ
      rw [hconstant d hd ζ hζ]
    _ = _ :=
      sum_mul_sum_primitiveRoots_eq_cyclotomic_nextCoeff
        N.divisors
        (fun d hd ↦ (Nat.pos_of_mem_divisors hd).ne')
        orbitMultiplicity

/-- In particular, a root-weighted sum with multiplicities constant
on primitive-root orbits has an integral value. -/
theorem exists_int_eq_sum_nthRoots_of_constant_on_primitiveRoots
    (N : ℕ) [NeZero N]
    (rootMultiplicity : ℂ → ℤ)
    (orbitMultiplicity : ℕ → ℤ)
    (hconstant :
      ∀ d ∈ N.divisors, ∀ ζ ∈ primitiveRoots d ℂ,
        rootMultiplicity ζ = orbitMultiplicity d) :
    ∃ z : ℤ,
      ∑ ζ ∈ nthRootsFinset N (1 : ℂ),
          (rootMultiplicity ζ : ℂ) * ζ = (z : ℂ) :=
  ⟨∑ d ∈ N.divisors,
      orbitMultiplicity d * (-(cyclotomic d ℤ).nextCoeff),
    sum_nthRoots_of_constant_on_primitiveRoots
      N rootMultiplicity orbitMultiplicity hconstant⟩

end Polynomial
