/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.InnerCharacterStabilizer
import McKayConjecture.InductiveMcKay.NormalizerInnerAutomorphismStabilizer

/-!
# Detecting inner character inertia

The exact Sylow normalizer maps onto a character inertia group precisely
when every Sylow-stabilizing automorphism fixing that character is inner.
Equivalently, the character stabilizer subgroup is contained in the range
of the normalizer-inner homomorphism.

These elementary reformulations isolate the finite outer-action check
needed in concrete inductive McKay verifications.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {G : Type u} [Group G] {p : ℕ}

namespace SylowAutStabilizer

/-- A Sylow-stabilizing automorphism belongs to the normalizer-inner range
if and only if it is inner as an automorphism of the ambient group. -/
theorem mem_normalizerInnerHom_range_iff_isInner
    (P : Sylow p G)
    (a : SylowAutStabilizer P) :
    a ∈ (normalizerInnerHom P).range ↔
      ∃ g : G, (a : MulAut G) = MulAut.conj g := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, rfl⟩
  · rintro ⟨g, hg⟩
    have hgNormalizer :
        g ∈ Subgroup.normalizer (P : Subgroup G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      have hstabilizes :=
        congrArg
          (fun Q : Sylow p G ↦ (Q : Subgroup G))
          a.2
      rw [hg] at hstabilizes
      exact hstabilizes
    refine ⟨⟨g, hgNormalizer⟩, ?_⟩
    apply Subtype.ext
    exact hg.symm

end SylowAutStabilizer

/-- The normalizer-to-character-inertia homomorphism is onto exactly when
the character stabilizer lies in the normalizer-inner range. -/
theorem normalizerInnerCharacterStabilizerHom_surjective_iff_le_range
    (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p) :
    Function.Surjective
        (normalizerInnerCharacterStabilizerHom P χ) ↔
      PPrimeCharacterStabilizer P χ ≤
        (SylowAutStabilizer.normalizerInnerHom P).range := by
  constructor
  · intro h a ha
    obtain ⟨g, hg⟩ := h ⟨a, ha⟩
    refine ⟨g, ?_⟩
    exact congrArg Subtype.val hg
  · intro h a
    obtain ⟨g, hg⟩ := h a.2
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hg

/-- It is enough to show directly that every Sylow-stabilizing
automorphism fixing the selected character is inner. -/
theorem normalizerInnerCharacterStabilizerHom_surjective_of_isInner
    (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p)
    (hInner :
      ∀ a : SylowAutStabilizer P,
        a • χ = χ →
          ∃ g : G, (a : MulAut G) = MulAut.conj g) :
    Function.Surjective
      (normalizerInnerCharacterStabilizerHom P χ) := by
  rw [
    normalizerInnerCharacterStabilizerHom_surjective_iff_le_range
  ]
  intro a ha
  exact
    (SylowAutStabilizer.mem_normalizerInnerHom_range_iff_isInner
      P a).mpr
      (hInner a ((PPrimeCharacterStabilizer.mem_iff a).mp ha))

/-- Row-index form: if every automorphism fixing the chosen enumerated row
is inner, the normalizer maps onto that row's character inertia group. -/
theorem normalizerInnerCharacterStabilizerHom_surjective_of_row_isInner
    {Row : Type*}
    (P : Sylow p G)
    (enumeration : Row ≃ PPrimeIrreducibleCharacter G p)
    (r : Row)
    (hInner :
      ∀ a : SylowAutStabilizer P,
        enumeration.symm (a • enumeration r) = r →
          ∃ g : G, (a : MulAut G) = MulAut.conj g) :
    Function.Surjective
      (normalizerInnerCharacterStabilizerHom P (enumeration r)) := by
  apply normalizerInnerCharacterStabilizerHom_surjective_of_isInner
  intro a ha
  apply hInner a
  apply enumeration.injective
  simpa using ha

end InductiveMcKay
end McKayConjecture
