/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionCyclotomicLift
import McKayConjecture.Character.BrauerInductionRegularFiberFourier
import McKayConjecture.Character.BrauerInductionCoefficientLattice

/-!
# Cyclotomic coefficients of the regular-fibre construction

The cyclic Fourier weights in Bernstein's regular-fibre function have
order dividing the size of the cyclic factor.  This file lifts every such
weight to the corresponding integral cyclotomic coefficient ring and
packages the resulting finite family as coefficients on genuine elementary
induction terms.

Evaluating the lifted coefficient vector in `ℂ` recovers the normalized
irreducible-character coefficients of the induced regular-fibre function.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {p : ℕ}
variable {E : Type} [Group E]

/-- A cyclic Fourier weight has order dividing the cardinality of the
cyclic factor. -/
theorem regularFiberWeight_pow_card_eq_one
    [Finite E]
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart)
    (lam : D.cyclicPart →* ℂˣ) :
    (lam a⁻¹ : ℂ) ^ Nat.card D.cyclicPart =
      1 := by
  rw [← Units.val_pow_eq_pow_val,
    ← map_pow, pow_card_eq_one', map_one,
    Units.val_one]

/-- The integral cyclotomic lift of one cyclic Fourier weight. -/
def liftedRegularFiberWeight
    [Finite E]
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart)
    (lam : D.cyclicPart →* ℂˣ) :
    CyclotomicCoefficientRing
      (Nat.card D.cyclicPart) :=
  cyclotomicCoefficientLift
    (Nat.card D.cyclicPart)
    Nat.card_pos
    (lam a⁻¹ : ℂ)
    (regularFiberWeight_pow_card_eq_one
      D a lam)

@[simp]
theorem evaluate_liftedRegularFiberWeight
    [Finite E]
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart)
    (lam : D.cyclicPart →* ℂˣ) :
    cyclotomicCoefficientEvaluation
        (Nat.card D.cyclicPart)
        Nat.card_pos
        (liftedRegularFiberWeight D a lam) =
      (lam a⁻¹ : ℂ) := by
  apply cyclotomicCoefficientEvaluation_lift

variable {C : Type} [Group C] [Finite C]

/-- Pairing one elementary induced character with an irreducible character
recovers its integral restriction-multiplicity coefficient. -/
theorem normalizedPairing_inducedClassFunction_irreducible
    (t : ElementaryInductionTerm C)
    (χ : IrreducibleCharacter C) :
    normalizedPairing t.inducedClassFunction
        χ.toClassFunction =
      (elementaryInductionCoefficient t χ : ℂ) := by
  rw [
    inducedClassFunction_eq_integerCharacterCombination_coefficient,
    IrreducibleCharacter.normalizedPairing_integerCharacterCombination_irreducible]

variable [Fact p.Prime]

/-- The finitely supported cyclotomic coefficient family obtained by
lifting every Fourier weight of the canonical regular-fibre function. -/
def centralPRegularCyclotomicCoefficients
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C) :
    ElementaryInductionTerm C →₀
      CyclotomicCoefficientRing
        (Nat.card
          (centralPRegularElementaryDecomposition
            a haCentral haRegular P).cyclicPart) := by
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
        (liftedRegularFiberWeight D aD lam)

/-- Unfolding the lifted coefficient family gives the expected finite sum
of elementary coefficient vectors. -/
theorem centralPRegularCyclotomicCombination_apply
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C)
    (χ : IrreducibleCharacter C) :
    let D :=
      centralPRegularElementaryDecomposition
        a haCentral haRegular P
    let aD :=
      centralPRegularCyclicCoordinate
        a haCentral haRegular P
    elementaryCoefficientCombinationOver
        (centralPRegularCyclotomicCoefficients
          a haCentral haRegular P) χ =
      ∑ lam ∈ cyclicFactorDual D,
        elementaryInductionCoefficient
            (centralPRegularLinearInductionTerm
              a haCentral haRegular P lam) χ •
          liftedRegularFiberWeight D aD lam := by
  classical
  dsimp only
  rw [centralPRegularCyclotomicCoefficients,
    elementaryCoefficientCombinationOver_finsetSum]
  simp

/-- Evaluating the lifted elementary coefficient combination in `ℂ`
recovers the normalized irreducible coefficient of the induced canonical
regular-fibre function. -/
theorem evaluate_centralPRegularCyclotomicCombination
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C)
    (χ : IrreducibleCharacter C) :
    let S :=
      centralPRegularElementarySubgroup a P
    let D :=
      centralPRegularElementaryDecomposition
        a haCentral haRegular P
    cyclotomicCoefficientEvaluation
        (Nat.card D.cyclicPart)
        Nat.card_pos
        (elementaryCoefficientCombinationOver
          (centralPRegularCyclotomicCoefficients
            a haCentral haRegular P) χ) =
      normalizedPairing
        (induceLinearMap S
          (centralPRegularFiber
            a haCentral haRegular P))
        χ.toClassFunction := by
  classical
  dsimp only
  rw [centralPRegularCyclotomicCombination_apply]
  simp only [map_sum, map_zsmul,
    evaluate_liftedRegularFiberWeight]
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
    zsmul_eq_mul,
    mul_comm] using hfourier.symm

end ClassFunction
end McKayConjecture
