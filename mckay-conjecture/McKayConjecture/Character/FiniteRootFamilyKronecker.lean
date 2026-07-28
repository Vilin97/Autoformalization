/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Kronecker's theorem for finite families of root sums

This file packages the Galois argument used for cyclic Glauberman
coefficients.  If a finite family of complex numbers consists of sums
of roots of unity of one common order and its squared Hermitian norm is
one, then every nonzero member of the family is itself a root of unity.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace McKayConjecture

private theorem isIntegral_multiset_sum
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (s : Multiset A) (hs : ∀ x ∈ s, IsIntegral R x) :
    IsIntegral R s.sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simpa using (isIntegral_zero : IsIntegral R (0 : A))
  | @cons x s ih =>
      rw [Multiset.sum_cons]
      exact
        (hs x (by simp)).add
          (ih (fun y hy ↦ hs y (by simp [hy])))

/-- Every characteristic root of an endomorphism whose `N`-th power
is the identity is an `N`-th root of unity. -/
theorem endomorphismRoot_pow_eq_one_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (N : ℕ) (hpow : f ^ N = 1)
    {z : ℂ} (hz : z ∈ f.charpoly.roots) :
    z ^ N = 1 := by
  have hroot : f.charpoly.IsRoot z :=
    (Polynomial.mem_roots f.charpoly_monic.ne_zero).mp hz
  have heigen : f.HasEigenvalue z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hroot
  obtain ⟨v, hv⟩ :=
    heigen.exists_hasEigenvector
  apply smul_left_injective ℂ hv.2
  calc
    z ^ N • v = (f ^ N) v :=
      (hv.pow_apply N).symm
    _ = v := by rw [hpow]; rfl
    _ = 1 • v := (one_smul ℂ v).symm

/-- A finite family of sums of roots of unity with total squared
Hermitian norm one has root-of-unity nonzero entries.

The common order is important: it places all summands in one
cyclotomic field, so every embedding of that field preserves complex
conjugation.  Parseval's identity can then be transported through an
arbitrary embedding and Kronecker's theorem applies. -/
theorem eq_zero_or_isOfFinOrder_of_eq_multiset_sum_of_hermitian_sum_eq_one
    {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N]
    (a : ι → ℂ) (roots : ι → Multiset ℂ)
    (hroots : ∀ i z, z ∈ roots i → z ^ N = 1)
    (ha : ∀ i, a i = (roots i).sum)
    (hsum : ∑ i, a i * conj (a i) = 1) :
    ∀ i, a i = 0 ∨ IsOfFinOrder (a i) := by
  classical
  let ζ : ℂ :=
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N)
  have hζ : IsPrimitiveRoot ζ N :=
    Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  let L : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ {ζ}
  have hζmem : ζ ∈ L :=
    IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ)
  have hroot_mem :
      ∀ {z : ℂ}, z ^ N = 1 → z ∈ L := by
    intro z hz
    obtain ⟨k, _hkN, hk⟩ :=
      hζ.eq_pow_of_pow_eq_one hz
    rw [← hk]
    exact L.pow_mem hζmem k
  have hamem : ∀ i, a i ∈ L := by
    intro i
    rw [ha i]
    exact
      L.multiset_sum_mem
        (roots i)
        (fun z hz ↦ hroot_mem (hroots i z hz))
  have haIntegral : ∀ i, IsIntegral ℤ (a i) := by
    intro i
    rw [ha i]
    apply isIntegral_multiset_sum
    intro z hz
    apply IsIntegral.of_pow (NeZero.pos N)
    rw [hroots i z hz]
    exact isIntegral_one
  have hζfinite : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨N, NeZero.pos N, hζ.pow_eq_one⟩
  have hζnorm : ‖ζ‖ = 1 :=
    hζfinite.norm_eq_one
  have hconjζ : conj ζ ∈ L := by
    rw [← Complex.inv_eq_conj hζnorm]
    exact L.inv_mem hζmem
  have hconjmem :
      ∀ (x : ℂ), x ∈ L → conj x ∈ L := by
    intro x hx
    refine
      IntermediateField.adjoin_induction ℚ
        (p := fun y _hy ↦ conj y ∈ L) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hconjζ
    · intro q
      simpa using L.algebraMap_mem q
    · intro y z hy hz hy' hz'
      simpa only [map_add] using L.add_mem hy' hz'
    · intro y hy hy'
      simpa only [map_inv₀] using L.inv_mem hy'
    · intro y z hy hz hy' hz'
      simpa only [map_mul] using L.mul_mem hy' hz'
  let conjQ : ℂ →ₐ[ℚ] ℂ :=
    Complex.conjAe.restrictScalars ℚ
  let conjL : L →ₐ[ℚ] L :=
    AlgHom.codRestrict (conjQ.comp L.val) L.toSubalgebra
      (fun x ↦ hconjmem x x.property)
  have hcomm :
      ∀ τ : L →ₐ[ℚ] ℂ,
        τ.comp conjL = conjQ.comp τ := by
    intro τ
    apply
      IntermediateField.algHom_ext_of_eq_adjoin
        (hS := show
          L = IntermediateField.adjoin ℚ {ζ} from rfl)
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hζpowL :
        (⟨ζ, hζmem⟩ : L) ^ N = 1 := by
      apply Subtype.ext
      exact hζ.pow_eq_one
    have hτζpow :
        (τ (⟨ζ, hζmem⟩ : L)) ^ N = 1 := by
      rw [← map_pow, hζpowL, map_one]
    have hτζfinite :
        IsOfFinOrder (τ (⟨ζ, hζmem⟩ : L)) :=
      isOfFinOrder_iff_pow_eq_one.mpr
        ⟨N, NeZero.pos N, hτζpow⟩
    have hτζnorm :
        ‖τ (⟨ζ, hζmem⟩ : L)‖ = 1 :=
      hτζfinite.norm_eq_one
    dsimp only [conjL, conjQ, AlgHom.comp_apply]
    change
      τ (⟨conj ζ, hconjζ⟩ : L) =
        conj (τ (⟨ζ, hζmem⟩ : L))
    have hconjζL :
        (⟨conj ζ, hconjζ⟩ : L) =
          (⟨ζ, hζmem⟩ : L)⁻¹ := by
      apply Subtype.ext
      exact (Complex.inv_eq_conj hζnorm).symm
    rw [hconjζL, map_inv₀,
      Complex.inv_eq_conj hτζnorm]
  let A : ι → L :=
    fun i ↦ ⟨a i, hamem i⟩
  have hsumL :
      ∑ i, A i * conjL (A i) = 1 := by
    apply L.val.injective
    rw [map_sum, map_one]
    simp only [map_mul]
    dsimp only [A, conjL, conjQ, AlgHom.comp_apply]
    exact hsum
  letI : FiniteDimensional ℚ L :=
    IntermediateField.adjoin.finiteDimensional
      (IsIntegral.of_pow (NeZero.pos N)
        (hζ.pow_eq_one ▸ isIntegral_one))
  letI : NumberField L :=
    NumberField.of_module_finite ℚ L
  intro i
  by_cases hai : a i = 0
  · exact Or.inl hai
  right
  have hAi_ne : A i ≠ 0 := by
    intro hzero
    apply hai
    exact congrArg Subtype.val hzero
  have hAiIntegral : IsIntegral ℤ (A i) :=
    IntermediateField.coe_isIntegral_iff.mp
      (haIntegral i)
  obtain ⟨n, hn, hpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_le_one
      L ℂ hAi_ne hAiIntegral (by
        intro σ
        let τ : L →ₐ[ℚ] ℂ :=
          σ.toRatAlgHom
        have hmapped :=
          congrArg τ hsumL
        have hcomm_apply :
            ∀ x : L, τ (conjL x) = conj (τ x) := by
          intro x
          have hx :=
            DFunLike.congr_fun (hcomm τ) x
          dsimp only [AlgHom.comp_apply, conjQ] at hx
          exact hx
        have hsumτ :
            ∑ j, τ (A j) * conj (τ (A j)) = 1 := by
          simpa only [map_sum, map_mul, map_one,
            hcomm_apply] using hmapped
        have hnormSqSum :
            ∑ j, Complex.normSq (τ (A j)) = 1 := by
          have hre := congrArg Complex.re hsumτ
          rw [Complex.re_sum] at hre
          simpa only [Complex.mul_conj,
            Complex.ofReal_re, Complex.one_re] using hre
        have hterm :
            Complex.normSq (τ (A i)) ≤ 1 := by
          rw [← hnormSqSum]
          exact
            Finset.single_le_sum
              (fun j _hj ↦ Complex.normSq_nonneg (τ (A j)))
              (Finset.mem_univ i)
        change ‖τ (A i)‖ ≤ 1
        rw [← Complex.sq_norm] at hterm
        have hnonneg : 0 ≤ ‖τ (A i)‖ :=
          norm_nonneg _
        nlinarith)
  have hpowComplex :
      a i ^ n = 1 := by
    exact congrArg Subtype.val hpow
  exact
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hn, hpowComplex⟩

/-- If a finite family has Hermitian norm one and every entry is zero
or a root of unity, then exactly one entry is nonzero.  The conclusion
also records that the surviving entry is a root of unity. -/
theorem exists_isOfFinOrder_and_others_eq_zero_of_hermitian_sum_eq_one
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ)
    (hfinite : ∀ i, a i = 0 ∨ IsOfFinOrder (a i))
    (hsum : ∑ i, a i * conj (a i) = 1) :
    ∃ i, IsOfFinOrder (a i) ∧
      ∀ j, j ≠ i → a j = 0 := by
  classical
  have hnormSqSum :
      ∑ i, Complex.normSq (a i) = 1 := by
    have hre := congrArg Complex.re hsum
    rw [Complex.re_sum] at hre
    simpa only [Complex.mul_conj,
      Complex.ofReal_re, Complex.one_re] using hre
  have hnonzero : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    have hzero :
        ∑ i, a i * conj (a i) = 0 := by
      simp [h]
    rw [hzero] at hsum
    exact zero_ne_one hsum
  obtain ⟨i, hi⟩ := hnonzero
  have hifinite : IsOfFinOrder (a i) :=
    (hfinite i).resolve_left hi
  refine ⟨i, hifinite, ?_⟩
  intro j hji
  by_contra hj
  have hjfinite : IsOfFinOrder (a j) :=
    (hfinite j).resolve_left hj
  have hiNormSq :
      Complex.normSq (a i) = 1 := by
    rw [← Complex.sq_norm, hifinite.norm_eq_one]
    norm_num
  have hjNormSq :
      Complex.normSq (a j) = 1 := by
    rw [← Complex.sq_norm, hjfinite.norm_eq_one]
    norm_num
  have hjmem :
      j ∈ (Finset.univ.erase i) := by
    simp [hji]
  have hrest :
      Complex.normSq (a j) ≤
        ∑ k ∈ Finset.univ.erase i,
          Complex.normSq (a k) :=
    Finset.single_le_sum
      (fun k _hk ↦ Complex.normSq_nonneg (a k))
      hjmem
  rw [hjNormSq] at hrest
  have hdecomp :=
    Finset.sum_erase_add
      (Finset.univ : Finset ι)
      (fun k ↦ Complex.normSq (a k))
      (Finset.mem_univ i)
  rw [hnormSqSum, hiNormSq] at hdecomp
  linarith

/-- Root-sum form of the unique-survivor conclusion.  This is the
interface used by the cyclic Glauberman coefficient family. -/
theorem
    exists_isOfFinOrder_and_others_eq_zero_of_eq_multiset_sum_of_hermitian_sum_eq_one
    {ι : Type*} [Fintype ι]
    (N : ℕ) [NeZero N]
    (a : ι → ℂ) (roots : ι → Multiset ℂ)
    (hroots : ∀ i z, z ∈ roots i → z ^ N = 1)
    (ha : ∀ i, a i = (roots i).sum)
    (hsum : ∑ i, a i * conj (a i) = 1) :
    ∃ i, IsOfFinOrder (a i) ∧
      ∀ j, j ≠ i → a j = 0 :=
  exists_isOfFinOrder_and_others_eq_zero_of_hermitian_sum_eq_one
    a
    (eq_zero_or_isOfFinOrder_of_eq_multiset_sum_of_hermitian_sum_eq_one
      N a roots hroots ha hsum)
    hsum

end McKayConjecture
