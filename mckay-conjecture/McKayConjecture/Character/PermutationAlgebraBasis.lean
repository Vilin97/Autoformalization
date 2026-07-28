/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerTraceIdeal
import Mathlib.Algebra.CharP.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Pointed permutation bases for modular group actions

A permutation `P`-algebra has a basis permuted by `P`.  For the Dade
condition one may choose such a basis containing the algebra unit.  The
coefficient of that distinguished basis vector detects the unit after
passing to the Brauer quotient.

This file packages the basis and proves the elementary nonvanishing
argument.  The proof uses only that `P` is a finite `p`-group and that
the coefficient field has characteristic `p`.
-/

noncomputable section

open scoped BigOperators

namespace Representation

variable {k P A : Type}
variable [Field k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- A `P`-stable basis of `A` containing the algebra unit as a
distinguished basis vector. -/
structure PointedPermutationAlgebraBasis where
  /-- Index type of the permutation basis. -/
  index : Type
  /-- Permutation action on basis indices. -/
  indexAction : P →* Equiv.Perm index
  /-- The underlying vector-space basis. -/
  basis : Module.Basis index k A
  /-- Compatibility of the two actions. -/
  smul_basis :
    ∀ (g : P) (i : index),
      g • basis i = basis (indexAction g i)
  /-- Index of the multiplicative identity. -/
  oneIndex : index
  /-- The distinguished basis vector is `1`. -/
  basis_oneIndex : basis oneIndex = 1

namespace PointedPermutationAlgebraBasis

variable
  (B : PointedPermutationAlgebraBasis
    (k := k) (P := P) (A := A))

/-- Coefficient of the distinguished vector `1` in the permutation
basis. -/
def oneCoefficient : A →ₗ[k] k :=
  B.basis.coord B.oneIndex

omit [Fintype P] [SMulCommClass P k A] in
@[simp]
theorem oneCoefficient_basis_oneIndex :
    B.oneCoefficient (B.basis B.oneIndex) = 1 := by
  simp [oneCoefficient]

omit [Fintype P] [SMulCommClass P k A] in
@[simp]
theorem oneCoefficient_one :
    B.oneCoefficient 1 = 1 := by
  rw [← B.basis_oneIndex]
  exact B.oneCoefficient_basis_oneIndex

omit [Fintype P] [SMulCommClass P k A] in
/-- The permutation action fixes the index of the algebra unit. -/
theorem indexAction_oneIndex
    (g : P) :
    B.indexAction g B.oneIndex = B.oneIndex := by
  apply B.basis.injective
  rw [← B.smul_basis, B.basis_oneIndex, smul_one]

omit [Fintype P] in
/-- The coefficient of `1` is invariant under the `P`-action. -/
theorem oneCoefficient_smul
    (g : P) (a : A) :
    B.oneCoefficient (g • a) = B.oneCoefficient a := by
  let f : A →ₗ[k] k :=
    B.oneCoefficient.comp
      (DistribSMul.toLinearMap k A g)
  have hf : f = B.oneCoefficient := by
    apply B.basis.ext
    intro i
    change
      B.oneCoefficient (g • B.basis i) =
        B.oneCoefficient (B.basis i)
    rw [B.smul_basis]
    by_cases hi : i = B.oneIndex
    · subst i
      rw [B.indexAction_oneIndex]
    · have hgi :
          B.indexAction g i ≠ B.oneIndex := by
        intro h
        apply hi
        apply (B.indexAction g).injective
        rw [h, B.indexAction_oneIndex]
      simp [oneCoefficient, hi, hgi]
  exact LinearMap.congr_fun hf a

noncomputable local instance permutationBasisLeftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

omit [Fintype P] in
/-- A proper subgroup of a finite `p`-group has index divisible by
`p`. -/
theorem prime_dvd_index_of_lt_top
    {p : ℕ} [Fact p.Prime] [Finite P]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q < ⊤) :
    p ∣ Q.index := by
  obtain ⟨n, hn⟩ :=
    hP.index Q
  cases n with
  | zero =>
      simp only [pow_zero] at hn
      exact
        (hQ.ne (Subgroup.index_eq_one.mp hn)).elim
  | succ n =>
      rw [hn, pow_succ']
      exact dvd_mul_right p (p ^ n)

/-- In characteristic `p`, the coefficient of `1` vanishes on every
relative trace from a proper subgroup of a finite `p`-group. -/
theorem oneCoefficient_fixedRelativeTrace_eq_zero
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    B.oneCoefficient
        (fixedRelativeTrace (k := k) (P := P) (A := A) Q x : A) =
      0 := by
  change
    B.oneCoefficient
        (∑ c : P ⧸ Q, c.out • (x : A)) =
      0
  rw [map_sum]
  simp_rw [B.oneCoefficient_smul]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul k]
  have hp :
      p ∣ Fintype.card (P ⧸ Q) := by
    rw [← Nat.card_eq_fintype_card, ← Q.index_eq_card]
    exact prime_dvd_index_of_lt_top hP Q hQ
  rw [(CharP.cast_eq_zero_iff k p _).2 hp, zero_smul]

/-- The distinguished coefficient vanishes on the total Brauer trace
ideal. -/
theorem oneCoefficient_eq_zero_of_mem_brauerTraceIdeal
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p P)
    (y : fixedSubalgebra (k := k) (P := P) (A := A))
    (hy :
      y ∈ brauerTraceIdeal (k := k) (P := P) (A := A)) :
    B.oneCoefficient (y : A) = 0 := by
  change
    y ∈
      ⨆ (Q : Subgroup P) (_hQ : Q < ⊤),
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q at hy
  refine Submodule.iSup_induction
    (fun Q : Subgroup P ↦
      ⨆ _hQ : Q < ⊤,
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q)
    (motive := fun z ↦ B.oneCoefficient (z : A) = 0)
    hy ?_ ?_ ?_
  · intro Q z hz
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ ↦
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q)
      (motive := fun w ↦ B.oneCoefficient (w : A) = 0)
      hz ?_ ?_ ?_
    · intro hQ w hw
      rcases hw with ⟨x, rfl⟩
      exact
        B.oneCoefficient_fixedRelativeTrace_eq_zero
          hP Q hQ x
    · exact map_zero B.oneCoefficient
    · intro u v hu hv
      change
        B.oneCoefficient ((u : A) + (v : A)) = 0
      rw [map_add, hu, hv, add_zero]
  · exact map_zero B.oneCoefficient
  · intro u v hu hv
    change
      B.oneCoefficient ((u : A) + (v : A)) = 0
    rw [map_add, hu, hv, add_zero]

include B in
/-- A pointed permutation basis forces the multiplicative Brauer
quotient to be nonzero. -/
theorem brauerTraceIdeal_ne_top
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p P) :
    brauerTraceIdeal (k := k) (P := P) (A := A) ≠ ⊤ := by
  intro htop
  have hone :
      (1 :
        fixedSubalgebra (k := k) (P := P) (A := A)) ∈
        brauerTraceIdeal (k := k) (P := P) (A := A) := by
    rw [htop]
    trivial
  have hzero :=
    oneCoefficient_eq_zero_of_mem_brauerTraceIdeal
      (B := B) hP 1 hone
  change B.oneCoefficient (1 : A) = 0 at hzero
  rw [B.oneCoefficient_one] at hzero
  exact one_ne_zero hzero

include B in
/-- Nontriviality of the multiplicative Brauer quotient, in the
typeclass form used by later unit arguments. -/
theorem brauerQuotientAlgebra_nontrivial
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p P) :
    Nontrivial
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (brauerTraceIdeal_ne_top (B := B) hP)

end PointedPermutationAlgebraBasis
end Representation
