/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.RootsOfUnity.Complex
import McKayConjecture.Character.FiniteFieldUnitsComplexEmbedding
import McKayConjecture.GroupTheory.PPrimaryKernelCardinality

/-!
# Cross-characteristic reduction of finite roots of unity

Let `q` be prime and let `n` be positive.  Write

`n = ordProj[q] n * ordCompl[q] n`

for the `q`-part times the prime-to-`q` part.  The Chinese remainder
theorem supplies an exponent which is zero modulo the first factor and
one modulo the second.  Raising an `n`th root of unity to this exponent
is therefore the idempotent projection onto its prime-to-`q` part.

The prime-to-`q` part embeds in the units of the concrete finite field

`GaloisField q (Nat.totient (ordCompl[q] n))`.

This file constructs the resulting multiplicative coefficient-reduction
map.  Its Teichmuller-style complex lift is exactly the CRT projection,
its kernel is a finite `q`-group, and every root splits exactly as its
kernel component times its lifted finite-field component.
-/

noncomputable section

namespace Representation

variable (q n : ℕ) [Fact q.Prime] [NeZero n]

/-- The `q`-power part of `n`. -/
abbrev primePart : ℕ :=
  ordProj[q] n

/-- The prime-to-`q` part of `n`. -/
abbrev primeToPart : ℕ :=
  ordCompl[q] n

omit [Fact q.Prime] [NeZero n] in
theorem primePart_mul_primeToPart :
    primePart q n * primeToPart q n = n :=
  Nat.ordProj_mul_ordCompl_eq_self n q

omit [Fact q.Prime] in
theorem primeToPart_pos :
    0 < primeToPart q n :=
  Nat.ordCompl_pos q (NeZero.ne n)

theorem prime_coprime_primeToPart :
    Nat.Coprime q (primeToPart q n) :=
  Nat.coprime_ordCompl Fact.out (NeZero.ne n)

theorem primePart_coprime_primeToPart :
    Nat.Coprime (primePart q n) (primeToPart q n) :=
  (prime_coprime_primeToPart q n).pow_left
    (Nat.factorization n q)

/-- The CRT idempotent exponent which is zero on the `q`-part and one
on the prime-to-`q` part. -/
def primeToProjectionExponent : ℕ :=
  Nat.chineseRemainder
    (primePart_coprime_primeToPart q n) 0 1

theorem primeToProjectionExponent_modEq_primePart :
    primeToProjectionExponent q n ≡ 0 [MOD primePart q n] :=
  (Nat.chineseRemainder
    (primePart_coprime_primeToPart q n) 0 1).property.1

theorem primeToProjectionExponent_modEq_primeToPart :
    primeToProjectionExponent q n ≡ 1 [MOD primeToPart q n] :=
  (Nat.chineseRemainder
    (primePart_coprime_primeToPart q n) 0 1).property.2

theorem primePart_dvd_primeToProjectionExponent :
    primePart q n ∣ primeToProjectionExponent q n :=
  Nat.modEq_zero_iff_dvd.mp
    (primeToProjectionExponent_modEq_primePart q n)

theorem primeToProjectionExponent_coprime_primeToPart :
    Nat.Coprime
      (primeToProjectionExponent q n)
      (primeToPart q n) := by
  apply Nat.coprime_of_mul_modEq_one 1
  simpa using
    primeToProjectionExponent_modEq_primeToPart q n

theorem gcd_n_primeToProjectionExponent :
    Nat.gcd n (primeToProjectionExponent q n) =
      primePart q n := by
  obtain ⟨t, ht⟩ :=
    primePart_dvd_primeToProjectionExponent q n
  have hprojectionCoprime :=
    primeToProjectionExponent_coprime_primeToPart q n
  have ht_coprime :
      Nat.Coprime t (primeToPart q n) := by
    rw [ht] at hprojectionCoprime
    exact
      (Nat.coprime_mul_iff_left.mp
        hprojectionCoprime).2
  calc
    Nat.gcd n (primeToProjectionExponent q n) =
        Nat.gcd
          (primePart q n * primeToPart q n)
          (primeToProjectionExponent q n) :=
      congrArg
        (fun a ↦ Nat.gcd a
          (primeToProjectionExponent q n))
        (primePart_mul_primeToPart q n).symm
    _ =
        Nat.gcd
          (primePart q n * primeToPart q n)
          (primePart q n * t) :=
      congrArg
        (Nat.gcd (primePart q n * primeToPart q n)) ht
    _ =
        primePart q n *
          Nat.gcd (primeToPart q n) t :=
      Nat.gcd_mul_left _ _ _
    _ = primePart q n := by
      rw [ht_coprime.symm.gcd_eq_one, mul_one]

theorem primeToProjectionExponent_idempotent_mod :
    primeToProjectionExponent q n *
        primeToProjectionExponent q n ≡
      primeToProjectionExponent q n [MOD n] := by
  have hmod :
      primeToProjectionExponent q n *
          primeToProjectionExponent q n ≡
        primeToProjectionExponent q n
          [MOD primePart q n * primeToPart q n] := by
    apply
      (Nat.modEq_and_modEq_iff_modEq_mul
        (primePart_coprime_primeToPart q n)).mp
    constructor
    · exact
        (primeToProjectionExponent_modEq_primePart q n).mul
            (primeToProjectionExponent_modEq_primePart q n) |>.trans
          (primeToProjectionExponent_modEq_primePart q n).symm
    · exact
        (primeToProjectionExponent_modEq_primeToPart q n).mul
            (primeToProjectionExponent_modEq_primeToPart q n) |>.trans
          (primeToProjectionExponent_modEq_primeToPart q n).symm
  simpa only [primePart_mul_primeToPart q n] using hmod

/-- The idempotent projection of complex `n`th roots onto their
prime-to-`q` part. -/
def primeToRootsProjection :
    rootsOfUnity n ℂ →* rootsOfUnity n ℂ :=
  powMonoidHom (primeToProjectionExponent q n)

theorem primeToRootsProjection_idempotent
    (z : rootsOfUnity n ℂ) :
    primeToRootsProjection q n
        (primeToRootsProjection q n z) =
      primeToRootsProjection q n z := by
  change
    (z ^ primeToProjectionExponent q n) ^
        primeToProjectionExponent q n =
      z ^ primeToProjectionExponent q n
  have hz : z ^ n = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity n (z : ℂˣ)).mp z.property
  rw [← pow_mul]
  exact
    pow_eq_pow_iff_modEq.mpr
      ((primeToProjectionExponent_idempotent_mod q n).of_dvd
        (orderOf_dvd_of_pow_eq_one hz))

theorem primeToRootsProjection_pow_primeToPart
    (z : rootsOfUnity n ℂ) :
    primeToRootsProjection q n z ^ primeToPart q n = 1 := by
  obtain ⟨t, ht⟩ :=
    primePart_dvd_primeToProjectionExponent q n
  have hz : z ^ n = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity n (z : ℂˣ)).mp z.property
  have hexponent :
      primePart q n * t * primeToPart q n =
        n * t := by
    calc
      primePart q n * t * primeToPart q n =
          (primePart q n * primeToPart q n) * t := by
        ac_rfl
      _ = n * t :=
        congrArg (fun a ↦ a * t)
          (primePart_mul_primeToPart q n)
  change
    (z ^ primeToProjectionExponent q n) ^
        primeToPart q n =
      1
  rw [ht, ← pow_mul]
  rw [hexponent, pow_mul, hz, one_pow]

/-- The kernel of the CRT projection has exactly the `q`-part of `n`
elements. -/
theorem natCard_primeToRootsProjection_ker :
    Nat.card (primeToRootsProjection q n).ker =
      primePart q n := by
  rw [primeToRootsProjection,
    IsCyclic.card_powMonoidHom_ker,
    Complex.card_rootsOfUnity,
    gcd_n_primeToProjectionExponent q n]

/-- The CRT projection has exactly the prime-to-`q` part of `n`
elements in its range. -/
theorem natCard_primeToRootsProjection_range :
    Nat.card (primeToRootsProjection q n).range =
      primeToPart q n := by
  rw [primeToRootsProjection,
    IsCyclic.card_powMonoidHom_range,
    Complex.card_rootsOfUnity,
    gcd_n_primeToProjectionExponent q n]

/-- The concrete finite coefficient field containing the prime-to-`q`
part of the `n`th roots of unity. -/
abbrev PrimeToCoefficientField :=
  GaloisField q (Nat.totient (primeToPart q n))

theorem natCard_primeToCoefficientField :
    Nat.card (PrimeToCoefficientField q n) =
      q ^ Nat.totient (primeToPart q n) := by
  exact
    GaloisField.card q (Nat.totient (primeToPart q n))
      (Nat.totient_pos.mpr (primeToPart_pos q n)).ne'

theorem natCard_primeToCoefficientField_units :
    Nat.card (PrimeToCoefficientField q n)ˣ =
      q ^ Nat.totient (primeToPart q n) - 1 := by
  rw [Nat.card_units, natCard_primeToCoefficientField q n]

/-- Euler's theorem ensures that the unit group of the chosen Galois
field contains a cyclic subgroup of the required prime-to-`q` order. -/
theorem primeToPart_dvd_natCard_primeToCoefficientField_units :
    primeToPart q n ∣
      Nat.card (PrimeToCoefficientField q n)ˣ := by
  rw [natCard_primeToCoefficientField_units q n]
  apply
    (Nat.modEq_iff_dvd'
      (Nat.one_le_pow
        (Nat.totient (primeToPart q n)) q
        (Fact.out : Nat.Prime q).pos)).mp
  exact (Nat.ModEq.pow_totient
    (prime_coprime_primeToPart q n)).symm

/-- Regard the CRT projection as a root of unity of the full order of
the chosen finite-field unit group. -/
def primeToRootsProjectionIntoFiniteFieldRoots :
    rootsOfUnity n ℂ →*
      rootsOfUnity
        (Nat.card (PrimeToCoefficientField q n)ˣ) ℂ where
  toFun z :=
    ⟨((primeToRootsProjection q n z :
        rootsOfUnity n ℂ) : ℂˣ), by
      obtain ⟨t, ht⟩ :=
        primeToPart_dvd_natCard_primeToCoefficientField_units q n
      have hprime :
          ((primeToRootsProjection q n z :
            rootsOfUnity n ℂ) : ℂˣ) ^
              primeToPart q n =
            1 :=
        congrArg
          (fun w : rootsOfUnity n ℂ ↦ (w : ℂˣ))
          (primeToRootsProjection_pow_primeToPart q n z)
      rw [mem_rootsOfUnity]
      rw [ht, pow_mul,
        hprime,
        one_pow]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

/-- Multiplicative reduction of complex `n`th roots to the units of a
finite field of characteristic `q`. -/
def crossCharacteristicCoefficientReduction :
    rootsOfUnity n ℂ →*
      (PrimeToCoefficientField q n)ˣ :=
  (finiteFieldUnitsEquivComplexRoots
      (PrimeToCoefficientField q n)).symm.toMonoidHom.comp
    (primeToRootsProjectionIntoFiniteFieldRoots q n)

/-- Lifting the reduced coefficient back to complex units recovers
exactly the CRT prime-to-`q` projection. -/
@[simp]
theorem finiteFieldUnitsToComplexUnits_crossCharacteristicCoefficientReduction
    (z : rootsOfUnity n ℂ) :
    finiteFieldUnitsToComplexUnits
        (PrimeToCoefficientField q n)
        (crossCharacteristicCoefficientReduction q n z) =
      ((primeToRootsProjection q n z :
        rootsOfUnity n ℂ) : ℂˣ) := by
  change
    (((finiteFieldUnitsEquivComplexRoots
        (PrimeToCoefficientField q n))
      ((finiteFieldUnitsEquivComplexRoots
        (PrimeToCoefficientField q n)).symm
        (primeToRootsProjectionIntoFiniteFieldRoots q n z)) :
      rootsOfUnity
        (Nat.card (PrimeToCoefficientField q n)ˣ) ℂ) : ℂˣ) =
      ((primeToRootsProjection q n z :
        rootsOfUnity n ℂ) : ℂˣ)
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The finite-field coefficient reduction has the same kernel as the
CRT projection. -/
theorem crossCharacteristicCoefficientReduction_ker :
    (crossCharacteristicCoefficientReduction q n).ker =
      (primeToRootsProjection q n).ker := by
  ext z
  change
    crossCharacteristicCoefficientReduction q n z = 1 ↔
      primeToRootsProjection q n z = 1
  constructor
  · intro hz
    have h :=
      congrArg
        (finiteFieldUnitsToComplexUnits
          (PrimeToCoefficientField q n)) hz
    simpa using h
  · intro hz
    apply
      finiteFieldUnitsToComplexUnits_injective
        (PrimeToCoefficientField q n)
    rw [
      finiteFieldUnitsToComplexUnits_crossCharacteristicCoefficientReduction,
      map_one, hz]
    rfl

theorem natCard_crossCharacteristicCoefficientReduction_ker :
    Nat.card
        (crossCharacteristicCoefficientReduction q n).ker =
      primePart q n := by
  rw [crossCharacteristicCoefficientReduction_ker,
    natCard_primeToRootsProjection_ker]

theorem natCard_crossCharacteristicCoefficientReduction_range :
    Nat.card
        (crossCharacteristicCoefficientReduction q n).range =
      primeToPart q n := by
  have hcard :
      Nat.card
          (crossCharacteristicCoefficientReduction q n).ker *
          Nat.card
            (crossCharacteristicCoefficientReduction q n).range =
        Nat.card (rootsOfUnity n ℂ) := by
    calc
      _ =
          Nat.card
              (crossCharacteristicCoefficientReduction q n).ker *
            (crossCharacteristicCoefficientReduction q n).ker.index := by
              rw [Subgroup.index_ker]
      _ = Nat.card (rootsOfUnity n ℂ) :=
        (crossCharacteristicCoefficientReduction q n).ker.card_mul_index
  rw [natCard_crossCharacteristicCoefficientReduction_ker,
    Complex.card_rootsOfUnity] at hcard
  exact
    Nat.eq_of_mul_eq_mul_left
      (Nat.ordProj_pos n q)
      (hcard.trans (primePart_mul_primeToPart q n).symm)

/-- The information discarded by coefficient reduction is exactly
`q`-primary. -/
theorem crossCharacteristicCoefficientReduction_ker_isPGroup :
    IsPGroup q
      (crossCharacteristicCoefficientReduction q n).ker := by
  apply
    (crossCharacteristicCoefficientReduction q n
      ).ker_isPGroup_of_card_eq_pow_mul_card_range
      (n := Nat.factorization n q)
  rw [Complex.card_rootsOfUnity,
    natCard_crossCharacteristicCoefficientReduction_range,
    primePart_mul_primeToPart q n]

/-- The `q`-primary remainder of a complex root after retaining its
prime-to-`q` projection. -/
def primePrimaryRootsRemainder :
    rootsOfUnity n ℂ →* rootsOfUnity n ℂ :=
  MonoidHom.id _ *
    (primeToRootsProjection q n)⁻¹

@[simp]
theorem primePrimaryRootsRemainder_apply
    (z : rootsOfUnity n ℂ) :
    primePrimaryRootsRemainder q n z =
      z * (primeToRootsProjection q n z)⁻¹ :=
  rfl

theorem primePrimaryRootsRemainder_mem_ker
    (z : rootsOfUnity n ℂ) :
    primePrimaryRootsRemainder q n z ∈
      (primeToRootsProjection q n).ker := by
  change
    primeToRootsProjection q n
        (z * (primeToRootsProjection q n z)⁻¹) =
      1
  rw [map_mul, map_inv,
    primeToRootsProjection_idempotent, mul_inv_cancel]

/-- The remainder as a homomorphism into the finite `q`-group kernel. -/
def primePrimaryRootsRemainderToKernel :
    rootsOfUnity n ℂ →*
      (primeToRootsProjection q n).ker :=
  (primePrimaryRootsRemainder q n).codRestrict
    (primeToRootsProjection q n).ker
    (primePrimaryRootsRemainder_mem_ker q n)

theorem primeToRootsProjection_ker_isPGroup :
    IsPGroup q (primeToRootsProjection q n).ker := by
  rw [← crossCharacteristicCoefficientReduction_ker q n]
  exact
    crossCharacteristicCoefficientReduction_ker_isPGroup q n

/-- Exact multiplicative decomposition into the discarded `q`-primary
part and the retained finite-field coefficient. -/
theorem primePrimaryRemainder_mul_lifted_reduction
    (z : rootsOfUnity n ℂ) :
    (((primePrimaryRootsRemainderToKernel q n z :
          (primeToRootsProjection q n).ker) :
        rootsOfUnity n ℂ) : ℂˣ) *
      finiteFieldUnitsToComplexUnits
        (PrimeToCoefficientField q n)
        (crossCharacteristicCoefficientReduction q n z) =
      (z : ℂˣ) := by
  rw [
    finiteFieldUnitsToComplexUnits_crossCharacteristicCoefficientReduction]
  change
    ((z * (primeToRootsProjection q n z)⁻¹ :
      rootsOfUnity n ℂ) : ℂˣ) *
        (primeToRootsProjection q n z : ℂˣ) =
      (z : ℂˣ)
  simp

end Representation
