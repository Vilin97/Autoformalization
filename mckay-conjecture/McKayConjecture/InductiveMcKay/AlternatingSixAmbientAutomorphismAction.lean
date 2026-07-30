/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeCharacterEnumeration
import McKayConjecture.InductiveMcKay.AlternatingSixOuterAutomorphismStabilizerCorrection

/-!
# Genuine automorphism actions on the ambient `p'` rows of `6.A₆`

A completed ambient ordinary character table identifies the arithmetic
prime-to-`p` row subtype with the actual prime-to-`p` irreducible characters
of the canonical universal cover.  Conjugating the genuine `MulAut` action
through this equivalence gives an honest permutation of the arithmetic row
type.

This file records that semantic permutation and its basic transport formulas.
It also specializes it to the two audited outer automorphisms, before and
after the inner correction needed to stabilize a chosen Sylow subgroup.  No
identification with the independently audited CTblLib permutations is made.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The genuine action of an automorphism of the canonical `A₆` cover,
transported to the arithmetic prime-to-`p` ambient row type through a
completed ordinary character table. -/
def alternatingSixAmbientPPrimeRowPermutation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (a : MulAut AlternatingSixUniversalCover) :
    Equiv.Perm (AlternatingSixAmbientPPrimeRowIndex p) where
  toFun r :=
    (alternatingSixAmbientPPrimeCharacterEquiv T p).symm
      (a • alternatingSixAmbientPPrimeCharacterEquiv T p r)
  invFun r :=
    (alternatingSixAmbientPPrimeCharacterEquiv T p).symm
      (a⁻¹ • alternatingSixAmbientPPrimeCharacterEquiv T p r)
  left_inv r := by
    simp
  right_inv r := by
    simp

@[simp]
theorem alternatingSixAmbientPPrimeRowPermutation_apply
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (a : MulAut AlternatingSixUniversalCover)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    alternatingSixAmbientPPrimeRowPermutation T p a r =
      (alternatingSixAmbientPPrimeCharacterEquiv T p).symm
        (a • alternatingSixAmbientPPrimeCharacterEquiv T p r) :=
  rfl

/-- The ambient enumeration intertwines the transported row permutation
with the genuine action on prime-to-`p` irreducible characters. -/
@[simp]
theorem alternatingSixAmbientPPrimeRowPermutation_character
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (a : MulAut AlternatingSixUniversalCover)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    alternatingSixAmbientPPrimeCharacterEquiv T p
        (alternatingSixAmbientPPrimeRowPermutation T p a r) =
      a • alternatingSixAmbientPPrimeCharacterEquiv T p r :=
  (alternatingSixAmbientPPrimeCharacterEquiv T p).apply_symm_apply _

/-- Every genuine ambient automorphism preserves the matrix dimension
attached to the transported arithmetic row. -/
theorem alternatingSixAmbientPPrimeRowPermutation_dimension
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (a : MulAut AlternatingSixUniversalCover)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeRowPermutation T p a r).1.dimension =
      r.1.dimension := by
  calc
    (alternatingSixAmbientPPrimeRowPermutation T p a r).1.dimension =
        (alternatingSixAmbientPPrimeCharacterEquiv T p
          (alternatingSixAmbientPPrimeRowPermutation T p a r)).1.degree := by
      rw [alternatingSixAmbientPPrimeCharacterEquiv_degree]
    _ = (a • alternatingSixAmbientPPrimeCharacterEquiv T p r).1.degree := by
      rw [alternatingSixAmbientPPrimeRowPermutation_character]
    _ = (alternatingSixAmbientPPrimeCharacterEquiv T p r).1.degree := by
      rfl
    _ = r.1.dimension :=
      alternatingSixAmbientPPrimeCharacterEquiv_degree T p r

@[simp]
theorem alternatingSixAmbientPPrimeRowPermutation_symm_apply
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (a : MulAut AlternatingSixUniversalCover)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    (alternatingSixAmbientPPrimeRowPermutation T p a).symm r =
      (alternatingSixAmbientPPrimeCharacterEquiv T p).symm
        (a⁻¹ • alternatingSixAmbientPPrimeCharacterEquiv T p r) :=
  rfl

/-- The inverse row permutation is intertwined with the inverse
automorphism on characters. -/
@[simp]
theorem alternatingSixAmbientPPrimeRowPermutation_symm_character
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (a : MulAut AlternatingSixUniversalCover)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    alternatingSixAmbientPPrimeCharacterEquiv T p
        ((alternatingSixAmbientPPrimeRowPermutation T p a).symm r) =
      a⁻¹ • alternatingSixAmbientPPrimeCharacterEquiv T p r :=
  (alternatingSixAmbientPPrimeCharacterEquiv T p).apply_symm_apply _

@[simp]
theorem alternatingSixAmbientPPrimeRowPermutation_one
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ) :
    alternatingSixAmbientPPrimeRowPermutation T p 1 = 1 := by
  apply Equiv.ext
  intro r
  apply (alternatingSixAmbientPPrimeCharacterEquiv T p).injective
  simp

/-- Multiplication of automorphisms becomes multiplication of the
transported row permutations. -/
theorem alternatingSixAmbientPPrimeRowPermutation_mul
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (a b : MulAut AlternatingSixUniversalCover) :
    alternatingSixAmbientPPrimeRowPermutation T p (a * b) =
      alternatingSixAmbientPPrimeRowPermutation T p a *
        alternatingSixAmbientPPrimeRowPermutation T p b := by
  apply Equiv.ext
  intro r
  apply (alternatingSixAmbientPPrimeCharacterEquiv T p).injective
  simp [mul_smul]

/-- The inverse automorphism induces the inverse row permutation. -/
theorem alternatingSixAmbientPPrimeRowPermutation_inv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (a : MulAut AlternatingSixUniversalCover) :
    alternatingSixAmbientPPrimeRowPermutation T p a⁻¹ =
      (alternatingSixAmbientPPrimeRowPermutation T p a).symm := by
  apply Equiv.ext
  intro r
  rfl

/-- Left multiplication by an inner automorphism does not change the
semantic ambient row permutation. -/
@[simp]
theorem alternatingSixAmbientPPrimeRowPermutation_conj_mul
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (g : AlternatingSixUniversalCover)
    (a : MulAut AlternatingSixUniversalCover) :
    alternatingSixAmbientPPrimeRowPermutation T p
        (MulAut.conj g * a) =
      alternatingSixAmbientPPrimeRowPermutation T p a := by
  apply Equiv.ext
  intro r
  apply (alternatingSixAmbientPPrimeCharacterEquiv T p).injective
  simp [mul_smul]

/-! ### The two transported audited automorphisms -/

/-- The semantic ambient row permutation induced by the first audited
outer automorphism. -/
def alternatingSixAmbientPPrimeAlphaOneRowPermutation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ) :
    Equiv.Perm (AlternatingSixAmbientPPrimeRowIndex p) :=
  alternatingSixAmbientPPrimeRowPermutation T p
    alternatingSixUniversalCoverTransportedAlphaOne

/-- The semantic ambient row permutation induced by the second audited
outer automorphism. -/
def alternatingSixAmbientPPrimeAlphaTwoRowPermutation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ) :
    Equiv.Perm (AlternatingSixAmbientPPrimeRowIndex p) :=
  alternatingSixAmbientPPrimeRowPermutation T p
    alternatingSixUniversalCoverTransportedAlphaTwo

@[simp]
theorem alternatingSixAmbientPPrimeAlphaOneRowPermutation_character
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    alternatingSixAmbientPPrimeCharacterEquiv T p
        (alternatingSixAmbientPPrimeAlphaOneRowPermutation T p r) =
      alternatingSixUniversalCoverTransportedAlphaOne •
        alternatingSixAmbientPPrimeCharacterEquiv T p r :=
  alternatingSixAmbientPPrimeRowPermutation_character T p _ r

@[simp]
theorem alternatingSixAmbientPPrimeAlphaTwoRowPermutation_character
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (p : ℕ)
    (r : AlternatingSixAmbientPPrimeRowIndex p) :
    alternatingSixAmbientPPrimeCharacterEquiv T p
        (alternatingSixAmbientPPrimeAlphaTwoRowPermutation T p r) =
      alternatingSixUniversalCoverTransportedAlphaTwo •
        alternatingSixAmbientPPrimeCharacterEquiv T p r :=
  alternatingSixAmbientPPrimeRowPermutation_character T p _ r

/-! ### Inner-corrected Sylow-stabilizing specializations -/

/-- The ambient row permutation induced by the first audited automorphism
after correcting it to stabilize the chosen Sylow subgroup. -/
def alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    Equiv.Perm (AlternatingSixAmbientPPrimeRowIndex p) :=
  alternatingSixAmbientPPrimeRowPermutation T p
    (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer P :
      MulAut AlternatingSixUniversalCover)

/-- The ambient row permutation induced by the second audited automorphism
after correcting it to stabilize the chosen Sylow subgroup. -/
def alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    Equiv.Perm (AlternatingSixAmbientPPrimeRowIndex p) :=
  alternatingSixAmbientPPrimeRowPermutation T p
    (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer P :
      MulAut AlternatingSixUniversalCover)

/-- The inner Sylow correction does not change the first audited
automorphism's action on ambient character rows. -/
@[simp]
theorem
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation T P =
      alternatingSixAmbientPPrimeAlphaOneRowPermutation T p := by
  rw [
    alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation,
    alternatingSixUniversalCoverCorrectedAlphaOneStabilizer_coe,
    alternatingSixAmbientPPrimeAlphaOneRowPermutation,
    alternatingSixAmbientPPrimeRowPermutation_conj_mul
  ]

/-- The inner Sylow correction does not change the second audited
automorphism's action on ambient character rows. -/
@[simp]
theorem
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover) :
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation T P =
      alternatingSixAmbientPPrimeAlphaTwoRowPermutation T p := by
  rw [
    alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation,
    alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer_coe,
    alternatingSixAmbientPPrimeAlphaTwoRowPermutation,
    alternatingSixAmbientPPrimeRowPermutation_conj_mul
  ]

end InductiveMcKay
end McKayConjecture
