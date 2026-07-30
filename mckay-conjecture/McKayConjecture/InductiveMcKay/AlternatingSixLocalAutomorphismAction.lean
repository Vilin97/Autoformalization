/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveConcreteFiniteTable
import McKayConjecture.InductiveMcKay.AlternatingSixThreeConcreteFiniteTable
import McKayConjecture.InductiveMcKay.AlternatingSixTwoConcreteFiniteTable
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer

/-!
# Genuine Sylow-stabilizer actions on enumerated normalizer rows

For a fixed Sylow subgroup `P`, its automorphism stabilizer acts genuinely
on the prime-to-`p` irreducible characters of `N_G(P)` through restriction.
Any finite enumeration of those characters therefore transports this action
to an honest permutation of its row type.

The generic construction and its transport formulas are followed by thin
specializations to the proved actual-normalizer enumerations for the
canonical sixfold cover of `A₆` at `p = 2`, `3`, and `5`.  No ambient/local
matching, CTblLib row identification, or McKay equivariance is asserted.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay

/-- The genuine Sylow-stabilizer action on local prime-to-`p` characters,
transported through an arbitrary finite row enumeration. -/
def normalizerPPrimeRowPermutation
    {G : Type u} [Group G]
    {p : ℕ}
    (P : Sylow p G)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (a : SylowAutStabilizer P) :
    Equiv.Perm Row where
  toFun r :=
    e.symm (a • e r)
  invFun r :=
    e.symm (a⁻¹ • e r)
  left_inv r := by
    simp
  right_inv r := by
    simp

@[simp]
theorem normalizerPPrimeRowPermutation_apply
    {G : Type u} [Group G]
    {p : ℕ}
    (P : Sylow p G)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (a : SylowAutStabilizer P)
    (r : Row) :
    normalizerPPrimeRowPermutation P e a r =
      e.symm (a • e r) :=
  rfl

/-- The supplied local enumeration intertwines the transported row
permutation with the genuine restricted stabilizer action. -/
@[simp]
theorem normalizerPPrimeRowPermutation_character
    {G : Type u} [Group G]
    {p : ℕ}
    (P : Sylow p G)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (a : SylowAutStabilizer P)
    (r : Row) :
    e (normalizerPPrimeRowPermutation P e a r) =
      a • e r :=
  e.apply_symm_apply _

@[simp]
theorem normalizerPPrimeRowPermutation_symm_apply
    {G : Type u} [Group G]
    {p : ℕ}
    (P : Sylow p G)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (a : SylowAutStabilizer P)
    (r : Row) :
    (normalizerPPrimeRowPermutation P e a).symm r =
      e.symm (a⁻¹ • e r) :=
  rfl

/-- The inverse row permutation is intertwined with the inverse
stabilizer action on local characters. -/
@[simp]
theorem normalizerPPrimeRowPermutation_symm_character
    {G : Type u} [Group G]
    {p : ℕ}
    (P : Sylow p G)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (a : SylowAutStabilizer P)
    (r : Row) :
    e ((normalizerPPrimeRowPermutation P e a).symm r) =
      a⁻¹ • e r :=
  e.apply_symm_apply _

@[simp]
theorem normalizerPPrimeRowPermutation_one
    {G : Type u} [Group G]
    {p : ℕ}
    (P : Sylow p G)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p) :
    normalizerPPrimeRowPermutation P e 1 = 1 := by
  apply Equiv.ext
  intro r
  apply e.injective
  simp

/-- Multiplication in the Sylow stabilizer becomes multiplication of the
transported local row permutations. -/
theorem normalizerPPrimeRowPermutation_mul
    {G : Type u} [Group G]
    {p : ℕ}
    (P : Sylow p G)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (a b : SylowAutStabilizer P) :
    normalizerPPrimeRowPermutation P e (a * b) =
      normalizerPPrimeRowPermutation P e a *
        normalizerPPrimeRowPermutation P e b := by
  apply Equiv.ext
  intro r
  apply e.injective
  simp [mul_smul]

/-- Inversion in the Sylow stabilizer becomes inversion of the transported
local row permutation. -/
theorem normalizerPPrimeRowPermutation_inv
    {G : Type u} [Group G]
    {p : ℕ}
    (P : Sylow p G)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (a : SylowAutStabilizer P) :
    normalizerPPrimeRowPermutation P e a⁻¹ =
      (normalizerPPrimeRowPermutation P e a).symm := by
  apply Equiv.ext
  intro r
  rfl

/-! ### The three actual-normalizer row enumerations for `6.A₆` -/

open GroupTheory

local instance alternatingSixLocalActionFactPrimeTwo :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

local instance alternatingSixLocalActionFactPrimeThree :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance alternatingSixLocalActionFactPrimeFive :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The genuine stabilizer action on the twelve proved rows of the actual
Sylow-two normalizer. -/
def alternatingSixTwoActualNormalizerRowPermutation
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2)) :
    Equiv.Perm AlternatingSixTwoConcreteNormalizerRow :=
  normalizerPPrimeRowPermutation
    (alternatingSixUniversalCoverSylow 2)
    alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
    a

/-- The genuine stabilizer action on the twelve proved rows of the actual
Sylow-three normalizer. -/
def alternatingSixThreeActualNormalizerRowPermutation
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3)) :
    Equiv.Perm AlternatingSixThreeConcreteNormalizerRow :=
  normalizerPPrimeRowPermutation
    (alternatingSixUniversalCoverSylow 3)
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
    a

/-- The genuine stabilizer action on the twenty-four proved rows of the
actual Sylow-five normalizer. -/
def alternatingSixFiveActualNormalizerRowPermutation
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5)) :
    Equiv.Perm AlternatingSixFiveConcreteNormalizerRow :=
  normalizerPPrimeRowPermutation
    (alternatingSixUniversalCoverSylow 5)
    alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
    a

@[simp]
theorem alternatingSixTwoActualNormalizerRowPermutation_apply
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    alternatingSixTwoActualNormalizerRowPermutation a r =
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv.symm
        (a • alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r) :=
  rfl

@[simp]
theorem alternatingSixThreeActualNormalizerRowPermutation_apply
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixThreeConcreteNormalizerRow) :
    alternatingSixThreeActualNormalizerRowPermutation a r =
      AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv.symm
        (a •
          AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
            r) :=
  rfl

@[simp]
theorem alternatingSixFiveActualNormalizerRowPermutation_apply
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    alternatingSixFiveActualNormalizerRowPermutation a r =
      alternatingSixFiveActualNormalizerPPrimeCharacterEquiv.symm
        (a • alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r) :=
  rfl

@[simp]
theorem alternatingSixTwoActualNormalizerRowPermutation_character
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
        (alternatingSixTwoActualNormalizerRowPermutation a r) =
      a • alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r :=
  normalizerPPrimeRowPermutation_character _ _ a r

@[simp]
theorem alternatingSixThreeActualNormalizerRowPermutation_character
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixThreeConcreteNormalizerRow) :
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
        (alternatingSixThreeActualNormalizerRowPermutation a r) =
      a •
        AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
          r :=
  normalizerPPrimeRowPermutation_character _ _ a r

@[simp]
theorem alternatingSixFiveActualNormalizerRowPermutation_character
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
        (alternatingSixFiveActualNormalizerRowPermutation a r) =
      a • alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r :=
  normalizerPPrimeRowPermutation_character _ _ a r

end InductiveMcKay
end McKayConjecture
