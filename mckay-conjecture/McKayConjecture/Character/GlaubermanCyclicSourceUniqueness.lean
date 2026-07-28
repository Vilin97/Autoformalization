/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCyclicCrossOrthogonality
import McKayConjecture.Character.GlaubermanCyclicKronecker
import McKayConjecture.Character.GlaubermanCyclicMultiplicityCongruence
import McKayConjecture.Character.IrreducibleCharacterBasis

/-!
# Source uniqueness and injectivity from the cyclic trace

If the determinant-normalized cyclic trace has exactly one nonzero
irreducible Fourier coefficient, and that coefficient is a root of
unity, then:

* the corresponding irreducible character is the unique one occurring
  with prime-to-`p` restriction multiplicity; and
* distinct invariant source characters have distinct correspondents.

The second assertion uses generator-coset cross orthogonality.  If two
distinct sources selected the same irreducible character, their cyclic
traces would be nonzero scalar multiples of that character, contradicting
their vanishing Hermitian cross-pairing.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace McKayConjecture

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- The coefficient shape needed from the cyclic signed-character
theorem: exactly one Fourier coefficient is nonzero, and it is a root
of unity. -/
def CyclicTraceSingleCoefficientShape
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤) : Prop :=
  ∀ θ : PInvariantPPrimeIrreducibleCharacter K P p,
    ∃ ψ :
        IrreducibleCharacter
          (cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G)),
      IsOfFinOrder
        (ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction) ∧
      ∀ φ :
          IrreducibleCharacter
            (cyclicFixedPoints K
              ((cyclicSubgroupGenerator P : P) : G)),
        φ ≠ ψ →
          ClassFunction.normalizedPairing
              (determinantNormalizedCyclicTrace
                K P hK hP hgenerate θ)
              φ.toClassFunction =
            0

/-- Kronecker's theorem and the unconditional cyclic Parseval identity
establish the required single-coefficient shape. -/
theorem cyclicTraceSingleCoefficientShape
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤) :
    CyclicTraceSingleCoefficientShape
      K P hK hP hgenerate := by
  intro θ
  exact
    exists_isOfFinOrder_normalizedPairing_determinantNormalizedCyclicTrace_and_others_eq_zero
      K P hK hP hgenerate θ

/-- The irreducible character singled out by the cyclic trace shape. -/
def cyclicTraceCorrespondent
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (hshape :
      CyclicTraceSingleCoefficientShape
        K P hK hP hgenerate)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
  Classical.choose (hshape θ)

/-- The cyclic trace is exactly its unique nonzero Fourier coefficient
times the selected irreducible character. -/
theorem determinantNormalizedCyclicTrace_eq_smul_cyclicTraceCorrespondent
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (hshape :
      CyclicTraceSingleCoefficientShape
        K P hK hP hgenerate)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ =
      ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          (cyclicTraceCorrespondent
            K P hK hP hgenerate hshape θ).toClassFunction •
        (cyclicTraceCorrespondent
          K P hK hP hgenerate hshape θ).toClassFunction := by
  classical
  letI : Fintype
      (IrreducibleCharacter
        (cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G))) :=
    Fintype.ofFinite _
  let ψ :=
    cyclicTraceCorrespondent
      K P hK hP hgenerate hshape θ
  calc
    determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ =
        ∑ φ :
            IrreducibleCharacter
              (cyclicFixedPoints K
                ((cyclicSubgroupGenerator P : P) : G)),
          ClassFunction.normalizedPairing
              (determinantNormalizedCyclicTrace
                K P hK hP hgenerate θ)
              φ.toClassFunction •
            φ.toClassFunction :=
      ClassFunction.irreducibleCharacter_fourierExpansion _
    _ =
        ClassFunction.normalizedPairing
            (determinantNormalizedCyclicTrace
              K P hK hP hgenerate θ)
            ψ.toClassFunction •
          ψ.toClassFunction := by
      apply Finset.sum_eq_single ψ
      · intro φ _hφ hφψ
        rw [(Classical.choose_spec (hshape θ)).2 φ hφψ]
        exact zero_smul ℂ φ.toClassFunction
      · intro hψ
        exact (hψ (Finset.mem_univ ψ)).elim
    _ = _ := rfl

/-- A root of unity in `ℂ` is nonzero. -/
private theorem isOfFinOrder_ne_zero
    {a : ℂ} (ha : IsOfFinOrder a) :
    a ≠ 0 := by
  obtain ⟨n, hn, hpow⟩ := ha.exists_pow_eq_one
  intro hazero
  rw [hazero, zero_pow hn.ne'] at hpow
  exact zero_ne_one hpow

/-- The target selected by the cyclic trace is injective as a function
of the invariant source character. -/
theorem cyclicTraceCorrespondent_injective
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (hshape :
      CyclicTraceSingleCoefficientShape
        K P hK hP hgenerate) :
    Function.Injective
      (cyclicTraceCorrespondent
        K P hK hP hgenerate hshape) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  intro θ η heq
  by_contra hne
  let C :=
    cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)
  letI : Fintype C := Fintype.ofFinite C
  let ψ : IrreducibleCharacter C :=
    cyclicTraceCorrespondent
      K P hK hP hgenerate hshape θ
  let a : ℂ :=
    ClassFunction.normalizedPairing
      (determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ)
      ψ.toClassFunction
  let b : ℂ :=
    ClassFunction.normalizedPairing
      (determinantNormalizedCyclicTrace
        K P hK hP hgenerate η)
      ψ.toClassFunction
  have ha : IsOfFinOrder a := by
    exact (Classical.choose_spec (hshape θ)).1
  have hb : IsOfFinOrder b := by
    have hb' := (Classical.choose_spec (hshape η)).1
    change
      IsOfFinOrder
        (ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate η)
          (cyclicTraceCorrespondent
            K P hK hP hgenerate hshape η).toClassFunction)
        at hb'
    rw [← heq] at hb'
    exact hb'
  have htraceθ :
      determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ =
        a • ψ.toClassFunction := by
    simpa [a, ψ] using
      determinantNormalizedCyclicTrace_eq_smul_cyclicTraceCorrespondent
        K P hK hP hgenerate hshape θ
  have htraceη :
      determinantNormalizedCyclicTrace
          K P hK hP hgenerate η =
        b • ψ.toClassFunction := by
    have h :=
      determinantNormalizedCyclicTrace_eq_smul_cyclicTraceCorrespondent
        K P hK hP hgenerate hshape η
    simpa [b, ψ, heq] using h
  have hcross :=
    determinantNormalizedCyclicTrace_hermitianSum_eq_zero_of_ne
      K P hK hP hgenerate θ η hne
  rw [htraceθ, htraceη] at hcross
  have hnorm :
      ∑ c : C,
          ψ.values c * conj (ψ.values c) =
        (Nat.card C : ℂ) := by
    have hself :=
      ClassFunction.normalizedPairing_irreducible_self ψ
    change
      (Nat.card C : ℂ)⁻¹ *
          ∑ c : C,
            ψ.values c * ψ.values c⁻¹ =
        1 at hself
    simp_rw [IrreducibleCharacter.value_inv_eq_conj] at hself
    have hcardne : (Nat.card C : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card C).ne'
    field_simp [hcardne] at hself
    exact hself
  have hcross' :
      a * conj b *
          (∑ c : C,
            ψ.values c * conj (ψ.values c)) =
        0 := by
    calc
      a * conj b *
            (∑ c : C,
              ψ.values c * conj (ψ.values c)) =
          ∑ c : C,
            (a • ψ.toClassFunction) c *
              conj ((b • ψ.toClassFunction) c) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _hc
        change
          a * conj b *
              (ψ.values c * conj (ψ.values c)) =
            (a * ψ.values c) *
              conj (b * ψ.values c)
        rw [map_mul]
        ring
      _ = 0 := hcross
  rw [hnorm] at hcross'
  have hconjb : conj b ≠ 0 := by
    intro hzero
    have hback := congrArg conj hzero
    rw [map_zero, Complex.conj_conj] at hback
    exact isOfFinOrder_ne_zero hb hback
  exact
    (mul_ne_zero
      (mul_ne_zero
        (isOfFinOrder_ne_zero ha)
        hconjb)
      (by
        exact_mod_cast
          (Nat.card_pos : 0 < Nat.card C).ne')) hcross'

/-- The cyclic trace shape gives full source-side uniqueness of
prime-to-`p` restriction multiplicity. -/
theorem cyclicTrace_existsUnique_restrictionMultiplicity_isPPrime
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (hshape :
      CyclicTraceSingleCoefficientShape
        K P hK hP hgenerate)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ∃! ψ :
        IrreducibleCharacter
          (cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G)),
      ¬p ∣
        restrictionMultiplicity
          (cyclicFixedPointsInclusion K
            ((cyclicSubgroupGenerator P : P) : G))
          ψ θ.1.1 :=
  existsUnique_restrictionMultiplicity_isPPrime_of_unique_rootCoefficient
    K P hK hP hgenerate θ (hshape θ)

end McKayConjecture
