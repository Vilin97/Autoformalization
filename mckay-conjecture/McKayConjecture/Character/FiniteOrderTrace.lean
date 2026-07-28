/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RepresentationTheory.Character

/-!
# Traces of inverses of finite-order complex operators

This file develops the linear-algebra input for the familiar identity
`χ(g⁻¹) = conj (χ(g))`.  The key point is that every characteristic root of
a finite-order complex operator is a root of unity.
-/

noncomputable section

open Complex Matrix Module Polynomial
open scoped ComplexConjugate

namespace Polynomial

/-- Reversing a linear polynomial with a nonzero root inverts that root. -/
lemma roots_reverse_X_sub_C (z : ℂ) (hz : z ≠ 0) :
    (X - C z).reverse.roots = {z⁻¹} := by
  have hreverseX : (X : ℂ[X]).reverse = 1 := by
    calc
      X.reverse = (1 * X : ℂ[X]).reverse := by rw [one_mul]
      _ = (1 : ℂ[X]).reverse := reverse_mul_X 1
      _ = 1 := by rw [← C_1, reverse_C, C_1]
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C]
  simp only [hreverseX, natDegree_X, pow_one, C_neg]
  have hrewrite :
      C (-z) * X + 1 = C (-z) * X - C (-1 : ℂ) := by
    simp
  have hform :
      (1 + -C z * X : ℂ[X]) = C (-z) * X + 1 := by
    simp [add_comm]
  rw [hform, hrewrite]
  simpa [neg_mul, hz] using
    (roots_C_mul_X_sub_C (R := ℂ) (a := -z) (-1) (neg_ne_zero.mpr hz))

private lemma reverse_multiset_prod (s : Multiset ℂ[X]) :
    s.prod.reverse = (s.map reverse).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      change (1 : ℂ[X]).reverse = 1
      rw [← C_1, reverse_C, C_1]
  | @cons p s ih =>
      simp only [Multiset.prod_cons, Multiset.map_cons]
      rw [reverse_mul_of_domain, ih]

private lemma bind_roots_reverse_linear_eq_map_inv
    (s : Multiset ℂ) (hs : ∀ z ∈ s, z ≠ 0) :
    (s.bind fun z ↦ (X - C z).reverse.roots) = s.map (·⁻¹) := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons z s ih =>
      have hz : z ≠ 0 := hs z (by simp)
      have hs' : ∀ w ∈ s, w ≠ 0 := by
        intro w hw
        exact hs w (by simp [hw])
      rw [Multiset.cons_bind, roots_reverse_X_sub_C z hz, ih hs',
        Multiset.map_cons]
      simp

/--
For a split complex polynomial with nonzero constant coefficient, reversal
inverts its roots, preserving their algebraic multiplicities.
-/
theorem roots_reverse_eq_map_inv
    (p : ℂ[X]) (hp : p.Splits) (hconstant : p.eval 0 ≠ 0) :
    p.reverse.roots = p.roots.map (·⁻¹) := by
  have hp0 : p ≠ 0 := by
    intro hpzero
    exact hconstant (by simp [hpzero])
  have hleading : p.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr hp0
  have hroot_ne_zero : ∀ z ∈ p.roots, z ≠ 0 := by
    intro z hz hz0
    subst z
    exact hconstant ((mem_roots hp0).mp hz)
  conv_lhs => rw [hp.eq_prod_roots]
  rw [reverse_mul_of_domain, reverse_C]
  rw [roots_C_mul _ hleading]
  rw [reverse_multiset_prod]
  rw [roots_multiset_prod]
  · simp only [Multiset.bind_map]
    exact bind_roots_reverse_linear_eq_map_inv p.roots hroot_ne_zero
  · intro hzero
    obtain ⟨q, hq, hqzero⟩ := Multiset.mem_map.mp hzero
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hq
    exact (monic_X_sub_C z).ne_zero (reverse_eq_zero.mp hqzero)

end Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Every characteristic root of a finite-order complex matrix has absolute
value one.
-/
theorem norm_eq_one_of_mem_roots_charpoly_of_isOfFinOrder
    (A : Matrix n n ℂ) (hA : IsOfFinOrder A) {z : ℂ}
    (hz : z ∈ A.charpoly.roots) :
    ‖z‖ = 1 := by
  have hroot : A.charpoly.IsRoot z :=
    (mem_roots A.charpoly_monic.ne_zero).mp hz
  have heigen :
      Module.End.HasEigenvalue (Matrix.toLin' A) z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      Matrix.charpoly_toLin']
    exact hroot
  have hfinite : IsOfFinOrder (Matrix.toLinAlgEquiv' A) :=
    MonoidHom.isOfFinOrder
      ((Matrix.toLinAlgEquiv' :
        Matrix n n ℂ ≃ₐ[ℂ] ((n → ℂ) →ₗ[ℂ] (n → ℂ))).toMonoidHom) hA
  obtain ⟨m, hmpos, hm⟩ := hfinite.exists_pow_eq_one
  obtain ⟨v, hv⟩ := heigen.exists_hasEigenvector
  have hzpow : z ^ m = 1 := by
    obtain ⟨i, hvi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv.2 (funext hall)
    apply smul_left_injective ℂ hvi
    have htoLin :
        Matrix.toLinAlgEquiv' A = Matrix.toLin' A := rfl
    have hvector :
        z ^ m • v = (1 : ℂ) • v := by
      calc
      z ^ m • v = ((Matrix.toLin' A) ^ m) v :=
        (hv.pow_apply m).symm
      _ = v := by rw [← htoLin, hm]; rfl
      _ = 1 • v := (one_smul ℂ v).symm
    simpa only [Pi.smul_apply] using congrFun hvector i
  exact
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hmpos, hzpow⟩).norm_eq_one

/--
The characteristic roots of the nonsingular inverse of an invertible
complex matrix are the inverses of the original roots, with multiplicity.
-/
theorem roots_charpoly_nonsing_inv_eq_map_inv
    (A : Matrix n n ℂ) (hA : IsUnit A) :
    A⁻¹.charpoly.roots = A.charpoly.roots.map (·⁻¹) := by
  have hdetUnit : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det (A := A)).mp hA
  have hdet : A.det ≠ 0 := hdetUnit.ne_zero
  have hinverseDet : Ring.inverse A.det ≠ 0 :=
    Ring.isUnit_iff_inverse_ne_zero.mp hdetUnit
  have hconstant : A.charpoly.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero]
    intro hzero
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, hzero, mul_zero]
  have hscalar :
      ((-1 : ℂ[X]) ^ Fintype.card n *
          C (Ring.inverse A.det)) =
        C (((-1 : ℂ) ^ Fintype.card n) *
          Ring.inverse A.det) := by
    simp
  rw [Matrix.charpoly_inv A hA]
  rw [hscalar]
  rw [roots_C_mul _ (mul_ne_zero
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hinverseDet)]
  rw [← Matrix.reverse_charpoly]
  exact Polynomial.roots_reverse_eq_map_inv
    A.charpoly (IsAlgClosed.splits A.charpoly) hconstant

private lemma conj_multiset_sum (s : Multiset ℂ) :
    conj s.sum = (s.map conj).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih => simp [ih]

/--
The trace of the inverse of a finite-order complex matrix is the complex
conjugate of its trace.
-/
theorem trace_nonsing_inv_eq_conj_trace_of_isOfFinOrder
    (A : Matrix n n ℂ) (hA : IsOfFinOrder A) :
    A⁻¹.trace = conj A.trace := by
  rw [Matrix.trace_eq_sum_roots_charpoly,
    Matrix.trace_eq_sum_roots_charpoly,
    roots_charpoly_nonsing_inv_eq_map_inv A hA.isUnit]
  have hmap :
      A.charpoly.roots.map (·⁻¹) =
        A.charpoly.roots.map conj := by
    apply Multiset.map_congr rfl
    intro z hz
    exact Complex.inv_eq_conj
      (norm_eq_one_of_mem_roots_charpoly_of_isOfFinOrder A hA hz)
  rw [hmap]
  exact (conj_multiset_sum A.charpoly.roots).symm

end Matrix

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/--
If `fInv` is the inverse of a finite-order complex endomorphism `f`, then
its trace is the complex conjugate of the trace of `f`.
-/
theorem trace_inverse_eq_conj_trace_of_isOfFinOrder
    (f fInv : Module.End ℂ V) (hinv : f * fInv = 1)
    (hfinite : IsOfFinOrder f) :
    LinearMap.trace ℂ V fInv = conj (LinearMap.trace ℂ V f) := by
  let b := Module.Free.chooseBasis ℂ V
  let A := LinearMap.toMatrix b b f
  let AInv := LinearMap.toMatrix b b fInv
  have hmatrixInv : A * AInv = 1 := by
    dsimp only [A, AInv]
    rw [← LinearMap.toMatrix_mul, hinv, LinearMap.toMatrix_one]
  have hAInv : A⁻¹ = AInv :=
    Matrix.inv_eq_right_inv hmatrixInv
  have hAfin : IsOfFinOrder A :=
    MonoidHom.isOfFinOrder
      ((LinearMap.toMatrixAlgEquiv b).toMonoidHom) hfinite
  rw [LinearMap.trace_eq_matrix_trace ℂ b,
    LinearMap.trace_eq_matrix_trace ℂ b]
  change AInv.trace = conj A.trace
  rw [← hAInv]
  exact Matrix.trace_nonsing_inv_eq_conj_trace_of_isOfFinOrder A hAfin

end LinearMap
