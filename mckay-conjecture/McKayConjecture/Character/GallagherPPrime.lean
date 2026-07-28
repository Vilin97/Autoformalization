/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherCorrespondence

/-!
# Prime-to-`p` degrees in the Gallagher correspondence

The Gallagher tensor character has degree equal to the product of the
extension degree and the quotient-character degree.  This file records the
resulting prime-to-`p` criterion and the useful specialization in which the
fixed extension already has prime-to-`p` degree.
-/

noncomputable section

namespace McKayConjecture

namespace IrreducibleCharacter

variable {K : Type} [Finite K] [Group K]
variable {H : Subgroup K} [H.Normal]
variable {χ : IrreducibleCharacter H}
variable {ψ : IrreducibleCharacter K}

/-- Gallagher tensoring has prime-to-`p` degree exactly when both tensor
factors do. -/
theorem gallagherTensorCharacter_isPPrimeDegree_iff
    {p : ℕ} (hp : p.Prime)
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    (gallagherTensorCharacter hψ beta).IsPPrimeDegree p ↔
      ψ.IsPPrimeDegree p ∧ beta.IsPPrimeDegree p := by
  rw [IsPPrimeDegree, gallagherTensorCharacter_degree,
    hp.dvd_mul, not_or, IsPPrimeDegree, IsPPrimeDegree]

/-- For a fixed prime-to-`p` extension, Gallagher tensoring preserves and
reflects prime-to-`p` degree of the quotient character. -/
theorem gallagherTensorCharacter_isPPrimeDegree_iff_of_extension
    {p : ℕ} (hp : p.Prime)
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (hψp : ψ.IsPPrimeDegree p)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    (gallagherTensorCharacter hψ beta).IsPPrimeDegree p ↔
      beta.IsPPrimeDegree p := by
  simpa [hψp] using
    (gallagherTensorCharacter_isPPrimeDegree_iff hp hψ beta)

/-- It is equivalent to assume that the extended normal-subgroup character
has prime-to-`p` degree. -/
theorem gallagherTensorCharacter_isPPrimeDegree_iff_of_source
    {p : ℕ} (hp : p.Prime)
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (hχp : χ.IsPPrimeDegree p)
    (beta : IrreducibleCharacter (K ⧸ H)) :
    (gallagherTensorCharacter hψ beta).IsPPrimeDegree p ↔
      beta.IsPPrimeDegree p :=
  gallagherTensorCharacter_isPPrimeDegree_iff_of_extension
    hp hψ ((hψ.isPPrimeDegree_iff p).2 hχp) beta

/-- Gallagher's correspondence restricted to prime-to-`p` characters,
assuming the chosen extension has prime-to-`p` degree. -/
def gallagherPPrimeCorrespondence
    {p : ℕ} (hp : p.Prime)
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (hψp : ψ.IsPPrimeDegree p) :
    PPrimeIrreducibleCharacter (K ⧸ H) p ≃
      CliffordCorrespondence.PPrimeIrreducibleCharactersOverAlong
        H.subtype χ p :=
  (gallagherCorrespondence hψ).subtypeEquiv fun beta ↦
    (gallagherTensorCharacter_isPPrimeDegree_iff_of_extension
      hp hψ hψp beta).symm

/-- The same prime-to-`p` correspondence, with the degree hypothesis stated
on the normal-subgroup character being extended. -/
def gallagherPPrimeCorrespondenceOfSource
    {p : ℕ} (hp : p.Prime)
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (hχp : χ.IsPPrimeDegree p) :
    PPrimeIrreducibleCharacter (K ⧸ H) p ≃
      CliffordCorrespondence.PPrimeIrreducibleCharactersOverAlong
        H.subtype χ p :=
  gallagherPPrimeCorrespondence hp hψ
    ((hψ.isPPrimeDegree_iff p).2 hχp)

end IrreducibleCharacter
end McKayConjecture
