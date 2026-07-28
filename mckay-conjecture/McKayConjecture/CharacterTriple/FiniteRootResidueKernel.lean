/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import McKayConjecture.Character.CrossCharacteristicCoefficientReduction
import McKayConjecture.CharacterTriple.FiniteRootResidueField

/-!
# The kernel of reduction of finite complex roots

Reduction modulo a maximal ideal above `q` kills exactly the `q`-primary
part of the finite group of complex roots of unity.  The prime-to-`q`
part retains its order because a primitive root remains a root of its
cyclotomic polynomial after reduction, and cyclotomic roots in
characteristic prime to their order are primitive.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FiniteRootCoefficientRing

open Polynomial Representation

variable (q n : ℕ) [Fact q.Prime] [NeZero n]

/-- A primitive complex `n`th root whose order is prime to `q` remains
primitive after reduction at the chosen maximal ideal above `q`. -/
theorem rootToResidueField_isPrimitiveRoot
    (z : rootsOfUnity n ℂ)
    (d : ℕ)
    (hz : IsPrimitiveRoot z d)
    (hqd : ¬q ∣ d) :
    IsPrimitiveRoot (rootToResidueField q n z) d := by
  have hzComplexUnit :
      IsPrimitiveRoot (z : ℂˣ) d :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mpr hz
  have hzComplex :
      IsPrimitiveRoot ((z : ℂˣ) : ℂ) d :=
    IsPrimitiveRoot.coe_units_iff.mpr hzComplexUnit
  have hzCoefficient :
      IsPrimitiveRoot (root n z) d := by
    apply
      IsPrimitiveRoot.of_map_of_injective
        (f := (FiniteRootCoefficientRing n).val)
        (by simpa using hzComplex)
        Subtype.coe_injective
  have hdpos : 0 < d := by
    by_contra hd
    have : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    exact hqd (dvd_zero q)
  have hrootCoefficient :
      IsRoot
        (cyclotomic d (FiniteRootCoefficientRing n))
        (root n z) :=
    hzCoefficient.isRoot_cyclotomic hdpos
  have hrootResidue :
      IsRoot
        (cyclotomic d (ResidueFieldAbovePrime q n))
        (Ideal.Quotient.mk (maximalIdealAbovePrime q n)
          (root n z)) := by
    simpa only [map_cyclotomic] using
      hrootCoefficient.map
        (f := Ideal.Quotient.mk (maximalIdealAbovePrime q n))
  letI : NeZero (d : ResidueFieldAbovePrime q n) :=
    NeZero.of_not_dvd (ResidueFieldAbovePrime q n) hqd
  rw [← IsPrimitiveRoot.coe_units_iff]
  change
    IsPrimitiveRoot
      (Ideal.Quotient.mk (maximalIdealAbovePrime q n)
        (root n z))
      d
  exact isRoot_cyclotomic_iff.mp hrootResidue

/-- Reduction sends every root in the `q`-primary kernel of the CRT
projection to one. -/
theorem rootToResidueField_eq_one_of_primeToRootsProjection_eq_one
    (z : rootsOfUnity n ℂ)
    (hz : primeToRootsProjection q n z = 1) :
    rootToResidueField q n z = 1 := by
  let zq :
      (primeToRootsProjection q n).ker :=
    ⟨z, hz⟩
  obtain ⟨k, hk⟩ :=
    (primeToRootsProjection_ker_isPGroup q n).exists_orderOf_eq_pow zq
  have hzpow : z ^ q ^ k = 1 := by
    have hzqpow : zq ^ q ^ k = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one zq
    exact congrArg Subtype.val hzqpow
  have hreducePow :
      (rootToResidueField q n z) ^ q ^ k = 1 := by
    rw [← map_pow, hzpow, map_one]
  apply Units.ext
  have hreduceValPow :
      ((rootToResidueField q n z :
          (ResidueFieldAbovePrime q n)ˣ) :
        ResidueFieldAbovePrime q n) ^ (q ^ k * 1) =
          1 := by
    simpa using congrArg Units.val hreducePow
  have hreduceVal :
      ((rootToResidueField q n z :
          (ResidueFieldAbovePrime q n)ˣ) :
        ResidueFieldAbovePrime q n) ^ 1 =
          1 :=
    (ExpChar.pow_prime_pow_mul_eq_one_iff
      q k 1
      ((rootToResidueField q n z :
          (ResidueFieldAbovePrime q n)ˣ) :
        ResidueFieldAbovePrime q n)).mp hreduceValPow
  simpa using hreduceVal

/-- If reduction of an `n`th root is one, then its prime-to-`q`
projection is already one. -/
theorem primeToRootsProjection_eq_one_of_rootToResidueField_eq_one
    (z : rootsOfUnity n ℂ)
    (hz : rootToResidueField q n z = 1) :
    primeToRootsProjection q n z = 1 := by
  let w := primeToRootsProjection q n z
  have hwpow :
      w ^ primeToPart q n = 1 :=
    primeToRootsProjection_pow_primeToPart q n z
  have horderDvd :
      orderOf w ∣ primeToPart q n :=
    orderOf_dvd_of_pow_eq_one hwpow
  have horderCoprime :
      Nat.Coprime q (orderOf w) :=
    (prime_coprime_primeToPart q n).coprime_dvd_right horderDvd
  have hqNotDvdOrder :
      ¬q ∣ orderOf w :=
    (Fact.out : q.Prime).coprime_iff_not_dvd.mp horderCoprime
  have hreduceW :
      rootToResidueField q n w = 1 := by
    change
      rootToResidueField q n
          (z ^ primeToProjectionExponent q n) =
        1
    rw [map_pow, hz, one_pow]
  have hprimitiveReduce :
      IsPrimitiveRoot
        (rootToResidueField q n w)
        (orderOf w) :=
    rootToResidueField_isPrimitiveRoot q n w
      (orderOf w) (IsPrimitiveRoot.orderOf w)
      hqNotDvdOrder
  rw [hreduceW, IsPrimitiveRoot.one_left_iff] at hprimitiveReduce
  exact orderOf_eq_one_iff.mp hprimitiveReduce

/-- Reduction at the chosen maximal ideal above `q` kills exactly the
`q`-primary roots, independently of the choice of maximal ideal. -/
theorem rootToResidueField_ker :
    (rootToResidueField q n).ker =
      (primeToRootsProjection q n).ker := by
  ext z
  constructor
  · exact primeToRootsProjection_eq_one_of_rootToResidueField_eq_one
      q n z
  · exact rootToResidueField_eq_one_of_primeToRootsProjection_eq_one
      q n z

end FiniteRootCoefficientRing
end CharacterTriple
end McKayConjecture
