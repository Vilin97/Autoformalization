/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import McKayConjecture.Character.FiniteOrderTrace

/-!
# A congruence for traces of operators of prime-power order

If a complex operator has `p`-power order and has integral trace, then its
trace is congruent modulo `p` to the dimension of the underlying vector
space.  This is the elementary cyclotomic congruence used in the cyclic
step of Glauberman correspondence.
-/

noncomputable section

open Matrix Module Polynomial

namespace McKayConjecture

private theorem multiset_card_sub_sum_dvd_of_pow_eq_one
    {p k : ℕ} [Fact p.Prime]
    (s : Multiset ℂ)
    (hpow : ∀ z ∈ s, z ^ (p ^ (k + 1)) = 1)
    (a : ℤ) (hsum : s.sum = (a : ℂ)) :
    (p : ℤ) ∣ (s.card : ℤ) - a := by
  let q := p ^ (k + 1)
  have hq : q ≠ 0 :=
    pow_ne_zero _ ((Fact.out : p.Prime).ne_zero)
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q :=
    Complex.isPrimitiveRoot_exp q hq
  let exponent : {z // z ∈ s} → ℕ := fun z =>
    Classical.choose
      (hζ.eq_pow_of_pow_eq_one (hpow z.1 z.2))
  have exponent_lt (z : {z // z ∈ s}) :
      exponent z < q :=
    (Classical.choose_spec
      (hζ.eq_pow_of_pow_eq_one (hpow z.1 z.2))).1
  have exponent_spec (z : {z // z ∈ s}) :
      ζ ^ exponent z = z.1 :=
    (Classical.choose_spec
      (hζ.eq_pow_of_pow_eq_one (hpow z.1 z.2))).2
  let P : ℤ[X] :=
    (s.attach.map fun z => X ^ exponent z).sum - C a
  have hPzero : Polynomial.aeval ζ P = 0 := by
    dsimp only [P]
    simp only [map_sub, map_multiset_sum, Multiset.map_map,
      Function.comp_apply, aeval_X_pow, aeval_C]
    have hmap :
        s.attach.map (fun z => ζ ^ exponent z) =
          s.attach.map (fun z => (z.1 : ℂ)) := by
      apply Multiset.map_congr rfl
      intro z hz
      exact exponent_spec z
    rw [hmap, Multiset.attach_map_val, hsum]
    simp
  have hdiv : cyclotomic q ℤ ∣ P := by
    rw [Polynomial.cyclotomic_eq_minpoly hζ
      (Nat.pos_of_ne_zero hq)]
    exact minpoly.isIntegrallyClosed_dvd
      (hζ.isIntegral (Nat.pos_of_ne_zero hq)) hPzero
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨Polynomial.eval 1 Q, ?_⟩
  have heval := congrArg (Polynomial.eval (1 : ℤ)) hQ
  have heval_monomials :
      (s.attach.map
          (fun z => Polynomial.eval (1 : ℤ)
            ((X : ℤ[X]) ^ exponent z))).sum =
        (s.card : ℤ) := by
    simp [eval_pow, eval_X]
  have heval_monomials_comp :
      (s.attach.map
          (Polynomial.eval (1 : ℤ) ∘
            fun z => (X : ℤ[X]) ^ exponent z)).sum =
        (s.card : ℤ) := by
    simpa only [Function.comp_apply] using heval_monomials
  dsimp only [P, q] at heval
  rw [eval_sub, eval_multisetSum, Multiset.map_map,
    heval_monomials_comp,
    eval_C, eval_mul, eval_one_cyclotomic_prime_pow] at heval
  exact heval

/-- A root-of-unity sum of `p`-power roots cannot contain a number of
summands divisible by `p`.  Evaluating a cyclotomic divisibility relation
at one reduces the assertion to `p ∤ 1`. -/
private theorem multiset_card_not_dvd_of_sum_isOfFinOrder
    {p k : ℕ} [Fact p.Prime]
    (s : Multiset ℂ)
    (hpow : ∀ z ∈ s, z ^ (p ^ (k + 1)) = 1)
    (a : ℂ) (hsum : s.sum = a)
    (ha : IsOfFinOrder a) :
    ¬p ∣ s.card := by
  let q := p ^ (k + 1)
  have hq : q ≠ 0 :=
    pow_ne_zero _ ((Fact.out : p.Prime).ne_zero)
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q :=
    Complex.isPrimitiveRoot_exp q hq
  let exponent : {z // z ∈ s} → ℕ := fun z =>
    Classical.choose
      (hζ.eq_pow_of_pow_eq_one (hpow z.1 z.2))
  have exponent_spec (z : {z // z ∈ s}) :
      ζ ^ exponent z = z.1 :=
    (Classical.choose_spec
      (hζ.eq_pow_of_pow_eq_one (hpow z.1 z.2))).2
  let P : ℤ[X] :=
    (s.attach.map fun z => X ^ exponent z).sum
  have hPeval : Polynomial.aeval ζ P = a := by
    dsimp only [P]
    simp only [map_multiset_sum, Multiset.map_map,
      Function.comp_apply, aeval_X_pow]
    have hmap :
        s.attach.map (fun z => ζ ^ exponent z) =
          s.attach.map (fun z => (z.1 : ℂ)) := by
      apply Multiset.map_congr rfl
      intro z hz
      exact exponent_spec z
    rw [hmap, Multiset.attach_map_val, hsum]
  obtain ⟨m, hmpos, hm⟩ := ha.exists_pow_eq_one
  have hPzero :
      Polynomial.aeval ζ (P ^ m - 1) = 0 := by
    rw [map_sub, map_pow, hPeval, hm, map_one, sub_self]
  have hdiv : cyclotomic q ℤ ∣ P ^ m - 1 := by
    rw [Polynomial.cyclotomic_eq_minpoly hζ
      (Nat.pos_of_ne_zero hq)]
    exact minpoly.isIntegrallyClosed_dvd
      (hζ.isIntegral (Nat.pos_of_ne_zero hq)) hPzero
  obtain ⟨Q, hQ⟩ := hdiv
  have hPeval_one :
      Polynomial.eval (1 : ℤ) P = (s.card : ℤ) := by
    dsimp only [P]
    rw [eval_multisetSum, Multiset.map_map]
    simp [Function.comp_apply, eval_pow, eval_X]
  have heval := congrArg (Polynomial.eval (1 : ℤ)) hQ
  dsimp only [q] at heval
  rw [eval_sub, eval_pow, hPeval_one, eval_one, eval_mul,
    eval_one_cyclotomic_prime_pow] at heval
  intro hp
  have hpcast : (p : ℤ) ∣ (s.card : ℤ) := by
    exact_mod_cast hp
  have hppow : (p : ℤ) ∣ (s.card : ℤ) ^ m :=
    hpcast.pow hmpos.ne'
  have hpdiff :
      (p : ℤ) ∣ (s.card : ℤ) ^ m - 1 :=
    ⟨Polynomial.eval 1 Q, heval⟩
  have hpone : (p : ℤ) ∣ 1 := by
    have h := dvd_sub hppow hpdiff
    simpa only [sub_sub_cancel] using h
  have hpone_nat : p ∣ 1 := by
    exact_mod_cast hpone
  exact (Fact.out : p.Prime).not_dvd_one hpone_nat

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every characteristic root of a matrix whose `q`-th power is one is a
`q`-th root of unity. -/
private theorem pow_eq_one_of_mem_roots_charpoly_of_pow_eq_one
    (A : Matrix n n ℂ) {q : ℕ} (hA : A ^ q = 1)
    {z : ℂ} (hz : z ∈ A.charpoly.roots) :
    z ^ q = 1 := by
  have hroot : A.charpoly.IsRoot z :=
    (mem_roots A.charpoly_monic.ne_zero).mp hz
  have heigen :
      Module.End.HasEigenvalue (Matrix.toLin' A) z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      Matrix.charpoly_toLin']
    exact hroot
  obtain ⟨v, hv⟩ := heigen.exists_hasEigenvector
  obtain ⟨i, hvi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv.2 (funext hall)
  apply smul_left_injective ℂ hvi
  have hlinpow :
      (Matrix.toLinAlgEquiv' A) ^ q = 1 := by
    rw [← map_pow, hA, map_one]
  have htoLin :
      Matrix.toLinAlgEquiv' A = Matrix.toLin' A := rfl
  have hvector :
      z ^ q • v = (1 : ℂ) • v := by
    calc
      z ^ q • v = ((Matrix.toLin' A) ^ q) v :=
        (hv.pow_apply q).symm
      _ = v := by rw [← htoLin, hlinpow]; rfl
      _ = 1 • v := (one_smul ℂ v).symm
  simpa only [Pi.smul_apply] using congrFun hvector i

/-- If a complex matrix has prime-power order and integral trace, its trace
is congruent modulo the prime to the matrix size. -/
theorem prime_dvd_card_sub_of_pow_primePower_eq_one
    {p k : ℕ} [Fact p.Prime]
    (A : Matrix n n ℂ)
    (hpow : A ^ (p ^ (k + 1)) = 1)
    (a : ℤ) (htrace : A.trace = (a : ℂ)) :
    (p : ℤ) ∣ (Fintype.card n : ℤ) - a := by
  have hroots_pow :
      ∀ z ∈ A.charpoly.roots,
        z ^ (p ^ (k + 1)) = 1 := by
    intro z hz
    exact
      pow_eq_one_of_mem_roots_charpoly_of_pow_eq_one
        A hpow hz
  have hsum :
      A.charpoly.roots.sum = (a : ℂ) :=
    (Matrix.trace_eq_sum_roots_charpoly A).symm.trans htrace
  have hdiv :=
    multiset_card_sub_sum_dvd_of_pow_eq_one
      A.charpoly.roots hroots_pow a hsum
  have hcard :
      A.charpoly.roots.card = Fintype.card n := by
    calc
      A.charpoly.roots.card = A.charpoly.natDegree :=
        (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots.symm
      _ = Fintype.card n :=
        A.charpoly_natDegree_eq_dim
  simpa only [hcard] using hdiv

/-- A root-of-unity trace of a complex matrix of `p`-power order forces
the matrix size to be prime to `p`. -/
theorem not_dvd_card_of_pow_primePower_eq_one_of_trace_isOfFinOrder
    {p k : ℕ} [Fact p.Prime]
    (A : Matrix n n ℂ)
    (hpow : A ^ (p ^ (k + 1)) = 1)
    (a : ℂ) (htrace : A.trace = a)
    (ha : IsOfFinOrder a) :
    ¬p ∣ Fintype.card n := by
  have hroots_pow :
      ∀ z ∈ A.charpoly.roots,
        z ^ (p ^ (k + 1)) = 1 := by
    intro z hz
    exact
      pow_eq_one_of_mem_roots_charpoly_of_pow_eq_one
        A hpow hz
  have hsum :
      A.charpoly.roots.sum = a :=
    (Matrix.trace_eq_sum_roots_charpoly A).symm.trans htrace
  have hnot :=
    multiset_card_not_dvd_of_sum_isOfFinOrder
      A.charpoly.roots hroots_pow a hsum ha
  have hcard :
      A.charpoly.roots.card = Fintype.card n := by
    calc
      A.charpoly.roots.card = A.charpoly.natDegree :=
        (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots.symm
      _ = Fintype.card n :=
        A.charpoly_natDegree_eq_dim
  simpa only [hcard] using hnot

end Matrix

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- An integer trace of a complex endomorphism of `p`-power order is
congruent modulo `p` to the dimension. -/
theorem prime_dvd_finrank_sub_of_pow_primePower_eq_one
    {p k : ℕ} [Fact p.Prime]
    (f : Module.End ℂ V)
    (hpow : f ^ (p ^ k) = 1)
    (a : ℤ)
    (htrace : LinearMap.trace ℂ V f = (a : ℂ)) :
    (p : ℤ) ∣ (Module.finrank ℂ V : ℤ) - a := by
  cases k with
  | zero =>
      have hf : f = 1 := by
        simpa only [pow_zero, pow_one] using hpow
      subst f
      have ha :
          (Module.finrank ℂ V : ℤ) = a := by
        rw [LinearMap.trace_one] at htrace
        exact_mod_cast htrace
      rw [ha, sub_self]
      exact dvd_zero _
  | succ k =>
      let b := Module.Free.chooseBasis ℂ V
      let A := LinearMap.toMatrix b b f
      have hA : A ^ (p ^ (k + 1)) = 1 := by
        change
          (LinearMap.toMatrixAlgEquiv b f) ^ (p ^ (k + 1)) =
            1
        rw [← map_pow, hpow, map_one]
      have hAtrace : A.trace = (a : ℂ) := by
        rw [← LinearMap.trace_eq_matrix_trace ℂ b]
        exact htrace
      have hdiv :=
        Matrix.prime_dvd_card_sub_of_pow_primePower_eq_one
          A hA a hAtrace
      simpa only [Module.finrank_eq_card_chooseBasisIndex] using hdiv

/-- A root-of-unity trace of a complex endomorphism of `p`-power order
forces the dimension to be prime to `p`. -/
theorem not_dvd_finrank_of_pow_primePower_eq_one_of_trace_isOfFinOrder
    {p k : ℕ} [Fact p.Prime]
    (f : Module.End ℂ V)
    (hpow : f ^ (p ^ k) = 1)
    (a : ℂ)
    (htrace : LinearMap.trace ℂ V f = a)
    (ha : IsOfFinOrder a) :
    ¬p ∣ Module.finrank ℂ V := by
  cases k with
  | zero =>
      have hf : f = 1 := by
        simpa only [pow_zero, pow_one] using hpow
      subst f
      rw [LinearMap.trace_one] at htrace
      obtain ⟨m, hmpos, hm⟩ := ha.exists_pow_eq_one
      have hdim_pow_complex :
          (Module.finrank ℂ V : ℂ) ^ m = 1 := by
        rw [htrace, hm]
      have hdim_pow_nat :
          (Module.finrank ℂ V) ^ m = 1 := by
        exact_mod_cast hdim_pow_complex
      have hdim :
          Module.finrank ℂ V = 1 := by
        simpa [Nat.pow_eq_one, hmpos.ne'] using hdim_pow_nat
      rw [hdim]
      exact (Fact.out : p.Prime).not_dvd_one
  | succ k =>
      let b := Module.Free.chooseBasis ℂ V
      let A := LinearMap.toMatrix b b f
      have hA : A ^ (p ^ (k + 1)) = 1 := by
        change
          (LinearMap.toMatrixAlgEquiv b f) ^ (p ^ (k + 1)) =
            1
        rw [← map_pow, hpow, map_one]
      have hAtrace : A.trace = a := by
        rw [← LinearMap.trace_eq_matrix_trace ℂ b]
        exact htrace
      have hnot :=
        Matrix.not_dvd_card_of_pow_primePower_eq_one_of_trace_isOfFinOrder
          A hA a hAtrace ha
      simpa only [Module.finrank_eq_card_chooseBasisIndex] using hnot

end LinearMap

end McKayConjecture
