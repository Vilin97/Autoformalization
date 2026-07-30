/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.InductiveMcKay.SylowAutomorphismInnerAdjustment

/-!
# Outer classes and character actions on exact Sylow normalizers

Two automorphisms stabilizing the same Sylow subgroup and representing the
same ambient outer class differ by conjugation by an element of the exact
Sylow normalizer.  Their restrictions therefore induce the same action on
prime-to-`q` irreducible characters of that normalizer.

This observation makes the character action of the noncomputably selected
`sylowAdjustedAutomorphism` independent of its selected inner correction.
It does not construct an explicit stabilizing representative or compute a
finite character-row permutation.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay

variable {G : Type u} [Group G] {p q : ℕ}

/-- Restricting conjugation by an exact-normalizer element to the exact
normalizer is conjugation by that same element. -/
@[simp]
theorem normalizerRestrictionHom_normalizerInnerSylowAutStabilizerHom
    (P : Sylow p G) (g : SylowNormalizer P) :
    SylowAutStabilizer.normalizerRestrictionHom P
        (normalizerInnerSylowAutStabilizerHom P g) =
      MulAut.conj g := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  rfl

/-- Equal ambient outer classes induce the same action on prime-to-`q`
irreducible characters of the exact Sylow normalizer. -/
theorem normalizerPPrime_smul_eq_of_sylowOuter_eq
    (P : Sylow p G)
    (a b : SylowAutStabilizer P)
    (hab :
      sylowAutStabilizerOuterHom P a =
        sylowAutStabilizerOuterHom P b)
    (χ : PPrimeIrreducibleCharacter (SylowNormalizer P) q) :
    a • χ = b • χ := by
  have hker :
      a⁻¹ * b ∈ (sylowAutStabilizerOuterHom P).ker := by
    change
      sylowAutStabilizerOuterHom P (a⁻¹ * b) = 1
    simp [map_mul, hab]
  rw [
    sylowAutStabilizerOuterHom_ker_eq_normalizerInner_range
  ] at hker
  obtain ⟨g, hg⟩ := hker
  have hb :
      b = a * normalizerInnerSylowAutStabilizerHom P g := by
    rw [hg]
    simp
  have hinner :
      normalizerInnerSylowAutStabilizerHom P g • χ = χ := by
    change
      SylowAutStabilizer.normalizerRestrictionHom P
            (normalizerInnerSylowAutStabilizerHom P g) • χ =
        χ
    rw [
      normalizerRestrictionHom_normalizerInnerSylowAutStabilizerHom,
      pPrime_conj_smul
    ]
  rw [hb, mul_smul, hinner]

/-- The permutation of a finite row type obtained by transporting the
prime-to-`q` character action of a Sylow-stabilizing automorphism. -/
def transportedNormalizerPPrimeRowPerm
    {Row : Type v}
    (P : Sylow p G)
    (enumeration :
      Row ≃ PPrimeIrreducibleCharacter (SylowNormalizer P) q)
    (a : SylowAutStabilizer P) :
    Equiv.Perm Row where
  toFun row :=
    enumeration.symm (a • enumeration row)
  invFun row :=
    enumeration.symm (a⁻¹ • enumeration row)
  left_inv row := by
    simp
  right_inv row := by
    simp

/-- Equal ambient outer classes induce the same action after transporting
normalizer characters through any chosen finite row enumeration. -/
theorem transportedNormalizerPPrimeRowAction_eq_of_sylowOuter_eq
    {Row : Type v}
    (P : Sylow p G)
    (enumeration :
      Row ≃ PPrimeIrreducibleCharacter (SylowNormalizer P) q)
    (a b : SylowAutStabilizer P)
    (hab :
      sylowAutStabilizerOuterHom P a =
        sylowAutStabilizerOuterHom P b)
    (row : Row) :
    enumeration.symm (a • enumeration row) =
      enumeration.symm (b • enumeration row) := by
  rw [normalizerPPrime_smul_eq_of_sylowOuter_eq P a b hab]

/-- The transported row permutation depends only on the ambient outer
class of the Sylow-stabilizing automorphism. -/
theorem transportedNormalizerPPrimeRowPerm_eq_of_sylowOuter_eq
    {Row : Type v}
    (P : Sylow p G)
    (enumeration :
      Row ≃ PPrimeIrreducibleCharacter (SylowNormalizer P) q)
    (a b : SylowAutStabilizer P)
    (hab :
      sylowAutStabilizerOuterHom P a =
        sylowAutStabilizerOuterHom P b) :
    transportedNormalizerPPrimeRowPerm P enumeration a =
      transportedNormalizerPPrimeRowPerm P enumeration b := by
  ext row
  exact
    transportedNormalizerPPrimeRowAction_eq_of_sylowOuter_eq
      P enumeration a b hab row

end InductiveMcKay
end McKayConjecture
