/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteRootFamilyKronecker
import McKayConjecture.Character.GlaubermanCyclicCoefficientTrace
import McKayConjecture.Character.GlaubermanCyclicHermitianNorm

/-!
# The unique cyclic Glauberman Fourier coefficient

The characteristic roots of every cyclic coefficient endomorphism are
roots of unity of order dividing the acting cyclic group.  Parseval's
identity and Kronecker's theorem then show that exactly one Fourier
coefficient is nonzero, and that coefficient is itself a root of
unity.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- The characteristic-root multiset of the coefficient endomorphism
indexed by `ψ`. -/
def determinantNormalizedCyclicCoefficientRoots
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    Multiset ℂ :=
  (determinantNormalizedCyclicCoefficientEndomorphism
    K P hK hP θ ψ).charpoly.roots

/-- Every characteristic root of a cyclic coefficient endomorphism has
order dividing the order of the acting cyclic group. -/
theorem determinantNormalizedCyclicCoefficientRoot_pow_card_eq_one
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)))
    {z : ℂ}
    (hz : z ∈ determinantNormalizedCyclicCoefficientRoots
      K P hK hP θ ψ) :
    z ^ Nat.card P = 1 := by
  letI : Fintype
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
    Fintype.ofFinite _
  apply
    endomorphismRoot_pow_eq_one_of_pow_eq_one
      (determinantNormalizedCyclicCoefficientEndomorphism
        K P hK hP θ ψ)
      (Nat.card P)
      (determinantNormalizedCyclicCoefficientEndomorphism_pow_card_eq_one
        K P hK hP θ ψ)
  exact hz

/-- A cyclic Fourier coefficient is the sum, with algebraic
multiplicity, of the roots of its coefficient endomorphism. -/
theorem
    normalizedPairing_determinantNormalizedCyclicTrace_eq_sum_coefficientRoots
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    ClassFunction.normalizedPairing
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ)
        ψ.toClassFunction =
      (determinantNormalizedCyclicCoefficientRoots
        K P hK hP θ ψ).sum := by
  letI : Fintype
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
    Fintype.ofFinite _
  rw [
    normalizedPairing_determinantNormalizedCyclicTrace_eq_trace_coefficientEndomorphism]
  exact
    Module.End.trace_eq_sum_roots_charpoly_of_splits
      (IsAlgClosed.splits
        (determinantNormalizedCyclicCoefficientEndomorphism
          K P hK hP θ ψ).charpoly)

/-- Exactly one irreducible Fourier coefficient of the
determinant-normalized cyclic trace survives, and it is a root of
unity. -/
theorem
    exists_isOfFinOrder_normalizedPairing_determinantNormalizedCyclicTrace_and_others_eq_zero
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ∃ ψ : IrreducibleCharacter
        (cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G)),
      IsOfFinOrder
        (ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction) ∧
      ∀ φ : IrreducibleCharacter
          (cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G)),
        φ ≠ ψ →
          ClassFunction.normalizedPairing
              (determinantNormalizedCyclicTrace
                K P hK hP hgenerate θ)
              φ.toClassFunction =
            0 := by
  letI : Fintype
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
    Fintype.ofFinite _
  letI : Fintype
      (IrreducibleCharacter
        (cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G))) :=
    ClassFunction.irreducibleCharacterBasisFintype
  letI : NeZero (Nat.card P) :=
    ⟨Nat.card_pos.ne'⟩
  apply
    exists_isOfFinOrder_and_others_eq_zero_of_eq_multiset_sum_of_hermitian_sum_eq_one
      (Nat.card P)
      (fun ψ ↦
        ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction)
      (fun ψ ↦
        determinantNormalizedCyclicCoefficientRoots
          K P hK hP θ ψ)
  · intro ψ z hz
    exact
      determinantNormalizedCyclicCoefficientRoot_pow_card_eq_one
        K P hK hP θ ψ hz
  · intro ψ
    exact
      normalizedPairing_determinantNormalizedCyclicTrace_eq_sum_coefficientRoots
        K P hK hP hgenerate θ ψ
  · simpa only [ClassFunction.fourierCoefficientNormSqSum] using
      determinantNormalizedCyclicTrace_fourierCoefficientNormSqSum_eq_one
        K P hK hP hgenerate θ

end McKayConjecture
