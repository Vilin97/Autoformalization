/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import McKayConjecture.Character.BrauerInductionCyclotomicDescent

/-!
# Lifting bounded complex roots of unity to a cyclotomic coefficient ring

The regular-fibre Fourier coefficients are complex roots of unity.  This
file realizes all `n`-th roots simultaneously in the integral coefficient
ring `AdjoinRoot (cyclotomic n ℤ)`.

Evaluation at the standard complex primitive `n`-th root is injective.
Every complex `n`-th root is a power of that primitive root, hence has a
chosen preimage in the integral cyclotomic ring.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

/-- The standard complex primitive `n`-th root used to evaluate the
integral cyclotomic coefficient ring. -/
def standardComplexPrimitiveRoot (n : ℕ) : ℂ :=
  Complex.exp
    (2 * Real.pi * Complex.I / n)

/-- The standard complex root is primitive when `n` is positive. -/
theorem standardComplexPrimitiveRoot_isPrimitive
    (n : ℕ) (hn : 0 < n) :
    IsPrimitiveRoot
      (standardComplexPrimitiveRoot n) n := by
  exact Complex.isPrimitiveRoot_exp n hn.ne'

/-- Evaluation of the integral cyclotomic coefficient ring at the standard
complex primitive root. -/
def cyclotomicCoefficientEvaluation
    (n : ℕ) (hn : 0 < n) :
    CyclotomicCoefficientRing n →+* ℂ :=
  AdjoinRoot.lift
    (Int.castRingHom ℂ)
    (standardComplexPrimitiveRoot n)
    (by
      have hroot :
          (Polynomial.cyclotomic n ℂ).IsRoot
            (standardComplexPrimitiveRoot n) :=
        (standardComplexPrimitiveRoot_isPrimitive n hn).isRoot_cyclotomic
          hn
      change
        Polynomial.eval₂
            (Int.castRingHom ℂ)
            (standardComplexPrimitiveRoot n)
            (Polynomial.cyclotomic n ℤ) =
          0
      rw [← Polynomial.eval_map,
        Polynomial.map_cyclotomic_int]
      exact hroot)

@[simp]
theorem cyclotomicCoefficientEvaluation_root
    (n : ℕ) (hn : 0 < n) :
    cyclotomicCoefficientEvaluation n hn
        (AdjoinRoot.root
          (Polynomial.cyclotomic n ℤ)) =
      standardComplexPrimitiveRoot n := by
  apply AdjoinRoot.lift_root

/-- Evaluation at a primitive complex root embeds the integral cyclotomic
coefficient ring into `ℂ`. -/
theorem cyclotomicCoefficientEvaluation_injective
    (n : ℕ) (hn : 0 < n) :
    Function.Injective
      (cyclotomicCoefficientEvaluation n hn) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hzero :
      cyclotomicCoefficientEvaluation n hn
          (x - y) =
        0 := by
    rw [map_sub, hxy, sub_self]
  have hker :
      ∀ z : CyclotomicCoefficientRing n,
        cyclotomicCoefficientEvaluation n hn z = 0 →
          z = 0 := by
    intro z
    induction z using AdjoinRoot.induction_on with
    | ih g =>
        intro hg
        change
          Polynomial.eval₂
              (Int.castRingHom ℂ)
              (standardComplexPrimitiveRoot n) g =
            0 at hg
        apply AdjoinRoot.mk_eq_zero.mpr
        rw [Polynomial.cyclotomic_eq_minpoly
          (standardComplexPrimitiveRoot_isPrimitive n hn)
          hn]
        apply minpoly.isIntegrallyClosed_dvd
          ((standardComplexPrimitiveRoot_isPrimitive
            n hn).isIntegral hn)
        change
          Polynomial.eval₂
              (Int.castRingHom ℂ)
              (standardComplexPrimitiveRoot n) g =
            0
        exact hg
  exact hker (x - y) hzero

/-- Every complex `n`-th root of unity has a preimage in the integral
cyclotomic coefficient ring. -/
theorem exists_cyclotomicCoefficient_preimage
    (n : ℕ) (hn : 0 < n)
    (z : ℂ) (hz : z ^ n = 1) :
    ∃ r : CyclotomicCoefficientRing n,
      cyclotomicCoefficientEvaluation n hn r = z := by
  letI : NeZero n :=
    ⟨hn.ne'⟩
  obtain ⟨i, _hi, hpow⟩ :=
    IsPrimitiveRoot.eq_pow_of_pow_eq_one
      (standardComplexPrimitiveRoot_isPrimitive n hn)
      hz
  refine
    ⟨(AdjoinRoot.root
        (Polynomial.cyclotomic n ℤ)) ^ i,
      ?_⟩
  rw [map_pow,
    cyclotomicCoefficientEvaluation_root,
    hpow]

/-- A chosen integral cyclotomic lift of a bounded complex root of unity. -/
def cyclotomicCoefficientLift
    (n : ℕ) (hn : 0 < n)
    (z : ℂ) (hz : z ^ n = 1) :
    CyclotomicCoefficientRing n :=
  Classical.choose
    (exists_cyclotomicCoefficient_preimage
      n hn z hz)

@[simp]
theorem cyclotomicCoefficientEvaluation_lift
    (n : ℕ) (hn : 0 < n)
    (z : ℂ) (hz : z ^ n = 1) :
    cyclotomicCoefficientEvaluation n hn
        (cyclotomicCoefficientLift n hn z hz) =
      z :=
  Classical.choose_spec
    (exists_cyclotomicCoefficient_preimage
      n hn z hz)

end ClassFunction
end McKayConjecture
