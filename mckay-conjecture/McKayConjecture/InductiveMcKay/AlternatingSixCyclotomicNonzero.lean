/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.ComputeDegree
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicField

/-!
# Nonvanishing below the 120th cyclotomic degree

A nonzero rational polynomial of degree below `φ(120) = 32` cannot vanish at
the chosen primitive 120th root.  This small exact lemma avoids analytic
nonvanishing arguments for explicit connecting entries.
-/

noncomputable section

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

/-- A nonzero rational polynomial of degree below `32` evaluates nontrivially
at the chosen complex primitive 120th root. -/
theorem alternatingSixComplexPolynomial_eval₂_ne_zero
    (p : ℚ[X])
    (p_ne_zero : p ≠ 0)
    (degree_lt : p.natDegree < 32) :
    Polynomial.eval₂ (algebraMap ℚ ℂ)
        alternatingSixComplexCyclotomicRoot p ≠ 0 := by
  have hmk :
      AdjoinRoot.mk (Polynomial.cyclotomic 120 ℚ) p ≠ 0 := by
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
      (Polynomial.cyclotomic.monic 120 ℚ)
    · exact p_ne_zero
    · rw [Polynomial.natDegree_cyclotomic]
      have htotient : Nat.totient 120 = 32 := by decide
      simpa [htotient] using degree_lt
  rw [← AdjoinRoot.aeval_eq] at hmk
  have hembedded :=
    alternatingSixCyclotomicEmbedding_injective.ne hmk
  have heval :
      alternatingSixCyclotomicEmbedding
          (aeval alternatingSixCyclotomicRoot p) =
        Polynomial.eval₂ (algebraMap ℚ ℂ)
          alternatingSixComplexCyclotomicRoot p := by
    rw [aeval_def]
    calc
      alternatingSixCyclotomicEmbedding
          (Polynomial.eval₂
            (algebraMap ℚ AlternatingSixCyclotomicField)
            alternatingSixCyclotomicRoot p) =
          Polynomial.eval₂
            (alternatingSixCyclotomicEmbedding.comp
              (algebraMap ℚ AlternatingSixCyclotomicField))
            (alternatingSixCyclotomicEmbedding
              alternatingSixCyclotomicRoot) p :=
        p.hom_eval₂
          (algebraMap ℚ AlternatingSixCyclotomicField)
          alternatingSixCyclotomicEmbedding
          alternatingSixCyclotomicRoot
      _ = Polynomial.eval₂ (algebraMap ℚ ℂ)
          alternatingSixComplexCyclotomicRoot p := by
        congr 2
        · ext q
          simp
        · exact alternatingSixCyclotomicEmbedding_root
  change
    alternatingSixCyclotomicEmbedding
        (aeval alternatingSixCyclotomicRoot p) ≠
      alternatingSixCyclotomicEmbedding 0 at hembedded
  rw [heval, map_zero] at hembedded
  exact hembedded

end InductiveMcKay
end McKayConjecture
