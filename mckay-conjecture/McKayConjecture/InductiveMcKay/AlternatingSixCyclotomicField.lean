/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# A computational cyclotomic coefficient field for the `6.A₆` tables

The ordinary character and matrix entries needed for the sixfold cover of
`A₆` lie in `ℚ(ζ₁₂₀)`: the degree-six rows use 24th roots and the sparse
degree-twelve rows use 15th roots.  We use the quotient obtained by
adjoining a root of the 120th cyclotomic polynomial.  This keeps exact matrix verification
over a small algebraic field; a canonical embedding into `ℂ` is applied
only when an ordinary complex representation is required.

The explicit degree-thirty-two relation is derived from primitive-root
identities of orders six and five applied to `ζ₁₂₀²`.  In particular, it
is proved inside Lean and is not imported as a computer-algebra
assertion.
-/

noncomputable section

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

/-- The exact coefficient field `ℚ(ζ₁₂₀)` used by the `6.A₆` matrix
certificates. -/
abbrev AlternatingSixCyclotomicField :=
  AdjoinRoot (Polynomial.cyclotomic 120 ℚ)

instance alternatingSixCyclotomicOneTwentyIrreducible :
    Fact (Irreducible (Polynomial.cyclotomic 120 ℚ)) :=
  ⟨Polynomial.cyclotomic.irreducible_rat (by norm_num)⟩

/-- The distinguished primitive 120th root in the quotient model. -/
def alternatingSixCyclotomicRoot :
    AlternatingSixCyclotomicField :=
  AdjoinRoot.root (Polynomial.cyclotomic 120 ℚ)

/-- The distinguished quotient root is primitive of exact order 120. -/
theorem alternatingSixCyclotomicRoot_isPrimitive :
    IsPrimitiveRoot alternatingSixCyclotomicRoot 120 := by
  apply
    (Polynomial.isRoot_cyclotomic_iff
      (R := AlternatingSixCyclotomicField)).mp
  rw [Polynomial.IsRoot,
    ← Polynomial.map_cyclotomic 120
      (algebraMap ℚ AlternatingSixCyclotomicField),
    Polynomial.eval_map]
  exact AdjoinRoot.eval₂_root _

/-- The order-six identity satisfied by the twentieth power of
`ζ₁₂₀`. -/
theorem alternatingSixCyclotomicRoot_orderSixRelation :
    alternatingSixCyclotomicRoot ^ 40 -
          alternatingSixCyclotomicRoot ^ 20 +
        1 = 0 := by
  have hprimitive :
      IsPrimitiveRoot
        (alternatingSixCyclotomicRoot ^ 20) 6 := by
    simpa using
      alternatingSixCyclotomicRoot_isPrimitive.pow_of_dvd
        (by norm_num : 20 ≠ 0)
        (by norm_num : 20 ∣ 120)
  have hroot :=
    hprimitive.isRoot_cyclotomic
      (by norm_num : 0 < 6)
  rw [Polynomial.cyclotomic_six] at hroot
  rw [Polynomial.IsRoot] at hroot
  simp only [Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at hroot
  simpa only [← pow_mul] using hroot

local instance alternatingSixCyclotomicFivePrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

private theorem alternatingSixCyclotomic_five :
    Polynomial.cyclotomic 5 AlternatingSixCyclotomicField =
      Polynomial.X ^ 4 + Polynomial.X ^ 3 +
        Polynomial.X ^ 2 + Polynomial.X + 1 := by
  rw [Polynomial.cyclotomic_prime
    AlternatingSixCyclotomicField 5]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_zero, pow_one]
  ac_rfl

/-- The order-five identity satisfied by the twenty-fourth power of
`ζ₁₂₀`. -/
theorem alternatingSixCyclotomicRoot_orderFiveRelation :
    alternatingSixCyclotomicRoot ^ 96 +
          alternatingSixCyclotomicRoot ^ 72 +
          alternatingSixCyclotomicRoot ^ 48 +
          alternatingSixCyclotomicRoot ^ 24 +
        1 = 0 := by
  have hprimitive :
      IsPrimitiveRoot
        (alternatingSixCyclotomicRoot ^ 24) 5 := by
    simpa using
      alternatingSixCyclotomicRoot_isPrimitive.pow_of_dvd
        (by norm_num : 24 ≠ 0)
        (by norm_num : 24 ∣ 120)
  have hroot :=
    hprimitive.isRoot_cyclotomic
      (by norm_num : 0 < 5)
  rw [alternatingSixCyclotomic_five] at hroot
  rw [Polynomial.IsRoot] at hroot
  simp only [Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one] at hroot
  simpa only [← pow_mul] using hroot

private theorem cyclotomicSixtyRelation_of_orderSixAndFive
    {R : Type*} [CommRing R] (x : R)
    (hsix : x ^ 20 - x ^ 10 + 1 = 0)
    (hfive :
      x ^ 48 + x ^ 36 + x ^ 24 + x ^ 12 + 1 = 0) :
    x ^ 16 + x ^ 14 - x ^ 10 - x ^ 8 -
          x ^ 6 + x ^ 2 + 1 =
        0 := by
  linear_combination
    (-x ^ 30 - x ^ 20 - x ^ 18 -
          x ^ 8 - x ^ 6 + 1) * hsix +
      x ^ 2 * hfive

private theorem cyclotomicOneTwentyRelation_of_relations
    {R : Type*} [CommRing R] (x : R)
    (hsix : x ^ 40 - x ^ 20 + 1 = 0)
    (hfive :
      x ^ 96 + x ^ 72 + x ^ 48 + x ^ 24 + 1 = 0) :
    x ^ 32 + x ^ 28 - x ^ 20 - x ^ 16 -
          x ^ 12 + x ^ 4 + 1 =
        0 := by
  have hsix' :
      (x ^ 2) ^ 20 - (x ^ 2) ^ 10 + 1 = 0 := by
    simpa only [← pow_mul] using hsix
  have hfive' :
      (x ^ 2) ^ 48 + (x ^ 2) ^ 36 +
            (x ^ 2) ^ 24 + (x ^ 2) ^ 12 + 1 =
          0 := by
    simpa only [← pow_mul] using hfive
  have hsixty :=
    cyclotomicSixtyRelation_of_orderSixAndFive
      (x ^ 2) hsix' hfive'
  simpa only [← pow_mul] using hsixty

/-- The explicit 120th cyclotomic relation
`Φ₁₂₀(X) = X³² + X²⁸ - X²⁰ - X¹⁶ - X¹² + X⁴ + 1`. -/
theorem alternatingSixCyclotomicRoot_relation :
    alternatingSixCyclotomicRoot ^ 32 +
          alternatingSixCyclotomicRoot ^ 28 -
          alternatingSixCyclotomicRoot ^ 20 -
          alternatingSixCyclotomicRoot ^ 16 -
          alternatingSixCyclotomicRoot ^ 12 +
          alternatingSixCyclotomicRoot ^ 4 +
        1 = 0 :=
  cyclotomicOneTwentyRelation_of_relations
    alternatingSixCyclotomicRoot
    alternatingSixCyclotomicRoot_orderSixRelation
    alternatingSixCyclotomicRoot_orderFiveRelation

/-- The analytic primitive 120th root used for the canonical complex
embedding. -/
def alternatingSixComplexCyclotomicRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 120)

theorem alternatingSixComplexCyclotomicRoot_isPrimitive :
    IsPrimitiveRoot alternatingSixComplexCyclotomicRoot 120 := by
  exact Complex.isPrimitiveRoot_exp 120 (by norm_num)

/-- The canonical embedding of the exact coefficient field into `ℂ`. -/
def alternatingSixCyclotomicEmbedding :
    AlternatingSixCyclotomicField →+* ℂ :=
  AdjoinRoot.lift
    (algebraMap ℚ ℂ)
    alternatingSixComplexCyclotomicRoot
    (by
      have hroot :=
        alternatingSixComplexCyclotomicRoot_isPrimitive
          |>.isRoot_cyclotomic (by norm_num : 0 < 120)
      rw [Polynomial.IsRoot,
        ← Polynomial.map_cyclotomic 120
          (algebraMap ℚ ℂ),
        Polynomial.eval_map] at hroot
      exact hroot)

@[simp]
theorem alternatingSixCyclotomicEmbedding_root :
    alternatingSixCyclotomicEmbedding
        alternatingSixCyclotomicRoot =
      alternatingSixComplexCyclotomicRoot := by
  exact AdjoinRoot.lift_root _

/-- The explicit 120th cyclotomic relation at the analytic root used in
the complex matrix models. -/
theorem alternatingSixComplexCyclotomicRoot_relation :
    alternatingSixComplexCyclotomicRoot ^ 32 +
          alternatingSixComplexCyclotomicRoot ^ 28 -
          alternatingSixComplexCyclotomicRoot ^ 20 -
          alternatingSixComplexCyclotomicRoot ^ 16 -
          alternatingSixComplexCyclotomicRoot ^ 12 +
          alternatingSixComplexCyclotomicRoot ^ 4 +
        1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_relation
  simpa only [map_add, map_sub, map_pow, map_one,
    map_zero, alternatingSixCyclotomicEmbedding_root] using h

/-- Evaluate a sparse rational coefficient list at the chosen complex
120th root.  Generated matrix data uses this wrapper to keep elaboration
of large tables below the default heartbeat limit. -/
def alternatingSixCyclotomicValue
    (terms : List (ℚ × ℕ)) : ℂ :=
  (terms.map fun term ↦
    (term.1 : ℂ) *
      alternatingSixComplexCyclotomicRoot ^ term.2).sum

@[simp]
theorem alternatingSixCyclotomicValue_nil :
    alternatingSixCyclotomicValue [] = 0 :=
  rfl

@[simp]
theorem alternatingSixCyclotomicValue_cons
    (coefficient : ℚ) (exponent : ℕ)
    (terms : List (ℚ × ℕ)) :
    alternatingSixCyclotomicValue
        ((coefficient, exponent) :: terms) =
      (coefficient : ℂ) *
          alternatingSixComplexCyclotomicRoot ^ exponent +
        alternatingSixCyclotomicValue terms := by
  simp [alternatingSixCyclotomicValue]

theorem alternatingSixCyclotomicEmbedding_injective :
    Function.Injective alternatingSixCyclotomicEmbedding :=
  RingHom.injective alternatingSixCyclotomicEmbedding

end InductiveMcKay
end McKayConjecture
