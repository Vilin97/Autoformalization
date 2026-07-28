/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionRegularFiberCyclotomic

/-!
# Regular-fibre coefficients in a common cyclotomic ring

The local regular-fibre construction naturally uses the cyclotomic ring
whose index is the order of its cyclic factor.  A global Brauer-induction
sum ranges over several such factors, so its coefficients must instead
live in one common ring.

This file lifts the Fourier coefficients directly into any cyclotomic
ring of index `n` divisible by the cyclic-factor order.  Taking `n` to be
the order of the ambient finite group gives a single coefficient ring for
all local summands.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {p n : ℕ}
variable {E : Type} [Group E] [Finite E]

/-- A regular-fibre Fourier weight is an `n`-th root whenever the order of
the cyclic factor divides `n`. -/
theorem regularFiberWeight_pow_eq_one_of_card_dvd
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart)
    (lam : D.cyclicPart →* ℂˣ)
    (hdiv : Nat.card D.cyclicPart ∣ n) :
    (lam a⁻¹ : ℂ) ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hdiv
  rw [pow_mul,
    regularFiberWeight_pow_card_eq_one,
    one_pow]

/-- Lift a regular-fibre Fourier weight directly into a common cyclotomic
coefficient ring. -/
def liftedRegularFiberWeightAt
    (n : ℕ) (hn : 0 < n)
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart)
    (lam : D.cyclicPart →* ℂˣ)
    (hdiv : Nat.card D.cyclicPart ∣ n) :
    CyclotomicCoefficientRing n :=
  cyclotomicCoefficientLift n hn
    (lam a⁻¹ : ℂ)
    (regularFiberWeight_pow_eq_one_of_card_dvd
      D a lam hdiv)

@[simp]
theorem evaluate_liftedRegularFiberWeightAt
    (n : ℕ) (hn : 0 < n)
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart)
    (lam : D.cyclicPart →* ℂˣ)
    (hdiv : Nat.card D.cyclicPart ∣ n) :
    cyclotomicCoefficientEvaluation n hn
        (liftedRegularFiberWeightAt
          n hn D a lam hdiv) =
      (lam a⁻¹ : ℂ) :=
  cyclotomicCoefficientEvaluation_lift
    n hn (lam a⁻¹ : ℂ)
      (regularFiberWeight_pow_eq_one_of_card_dvd
        D a lam hdiv)

variable {C : Type} [Group C] [Finite C]
variable [Fact p.Prime]

/-- The central regular-fibre Fourier coefficients, all lifted into the
same cyclotomic ring of index `n`. -/
def centralPRegularCyclotomicCoefficientsAt
    (n : ℕ) (hn : 0 < n)
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C)
    (hdiv :
      Nat.card
          (centralPRegularElementaryDecomposition
            a haCentral haRegular P).cyclicPart ∣
        n) :
    ElementaryInductionTerm C →₀
      CyclotomicCoefficientRing n := by
  let D :=
    centralPRegularElementaryDecomposition
      a haCentral haRegular P
  let aD :=
    centralPRegularCyclicCoordinate
      a haCentral haRegular P
  exact
    ∑ lam ∈ cyclicFactorDual D,
      Finsupp.single
        (centralPRegularLinearInductionTerm
          a haCentral haRegular P lam)
        (liftedRegularFiberWeightAt
          n hn D aD lam hdiv)

/-- Unfolding the common-ring coefficient family gives its finite weighted
sum of elementary coefficient vectors. -/
theorem centralPRegularCyclotomicCombinationAt_apply
    (n : ℕ) (hn : 0 < n)
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C)
    (hdiv :
      Nat.card
          (centralPRegularElementaryDecomposition
            a haCentral haRegular P).cyclicPart ∣
        n)
    (χ : IrreducibleCharacter C) :
    let D :=
      centralPRegularElementaryDecomposition
        a haCentral haRegular P
    let aD :=
      centralPRegularCyclicCoordinate
        a haCentral haRegular P
    elementaryCoefficientCombinationOver
        (centralPRegularCyclotomicCoefficientsAt
          n hn a haCentral haRegular P hdiv) χ =
      ∑ lam ∈ cyclicFactorDual D,
        elementaryInductionCoefficient
            (centralPRegularLinearInductionTerm
              a haCentral haRegular P lam) χ •
          liftedRegularFiberWeightAt
            n hn D aD lam hdiv := by
  classical
  dsimp only
  rw [centralPRegularCyclotomicCoefficientsAt,
    elementaryCoefficientCombinationOver_finsetSum]
  simp

/-- Evaluation of the common-ring coefficient combination recovers the
normalized pairing with the induced regular-fibre class function. -/
theorem evaluate_centralPRegularCyclotomicCombinationAt
    (n : ℕ) (hn : 0 < n)
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C)
    (hdiv :
      Nat.card
          (centralPRegularElementaryDecomposition
            a haCentral haRegular P).cyclicPart ∣
        n)
    (χ : IrreducibleCharacter C) :
    let S :=
      centralPRegularElementarySubgroup a P
    cyclotomicCoefficientEvaluation n hn
        (elementaryCoefficientCombinationOver
          (centralPRegularCyclotomicCoefficientsAt
            n hn a haCentral haRegular P hdiv) χ) =
      normalizedPairing
        (induceLinearMap S
          (centralPRegularFiber
            a haCentral haRegular P))
        χ.toClassFunction := by
  classical
  dsimp only
  rw [centralPRegularCyclotomicCombinationAt_apply]
  simp only [map_sum, map_zsmul,
    evaluate_liftedRegularFiberWeightAt]
  have hfourier :=
    congrArg
      (fun f : ClassFunction C =>
        normalizedPairing f χ.toClassFunction)
      (induce_centralPRegularFiber_eq_sum_inducedLinearCharacters
        a haCentral haRegular P)
  simpa only [map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply,
    normalizedPairing_inducedClassFunction_irreducible,
    Int.cast_sum, Int.cast_mul, smul_eq_mul,
    zsmul_eq_mul, mul_comm] using hfourier.symm

/-- The cyclic factor in the canonical central regular-element
construction has order dividing the order of the ambient finite group. -/
theorem centralPRegularCyclicPart_card_dvd
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C) :
    Nat.card
        (centralPRegularElementaryDecomposition
          a haCentral haRegular P).cyclicPart ∣
      Nat.card C := by
  let S :=
    centralPRegularElementarySubgroup a P
  let D :=
    centralPRegularElementaryDecomposition
      a haCentral haRegular P
  exact
    (Subgroup.card_subgroup_dvd_card D.cyclicPart).trans
      (Subgroup.card_subgroup_dvd_card S)

end ClassFunction
end McKayConjecture
