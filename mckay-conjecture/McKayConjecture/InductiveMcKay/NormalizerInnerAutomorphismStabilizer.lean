/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer

/-!
# Inner automorphisms in a Sylow automorphism stabilizer

Every element of `N_G(P)` induces an inner automorphism stabilizing `P`.
This gives a canonical homomorphism

`N_G(P) → Aut(G)_P`.

Its action on ambient ordinary characters is trivial.  After restriction
to `N_G(P)`, it is again inner conjugation by the same element, so its
action on normalizer characters is trivial as well.  Consequently every
equivalence between arbitrarily enumerated ambient and local character
rows intertwines the entire range of this homomorphism.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace InductiveMcKay
namespace SylowAutStabilizer

variable {G : Type u} [Group G] {p q : ℕ}

/-- Conjugation by the Sylow normalizer, bundled as an element of the
Sylow automorphism stabilizer. -/
def normalizerInnerHom
    (P : Sylow p G) :
    SylowNormalizer P →* SylowAutStabilizer P where
  toFun g :=
    ⟨MulAut.conj g.1, by
      rw [mem_iff]
      apply Sylow.ext
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp g.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (MulAut.conj : G →* MulAut G)
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (MulAut.conj : G →* MulAut G) g.1 h.1

@[simp]
theorem normalizerInnerHom_coe
    (P : Sylow p G)
    (g : SylowNormalizer P) :
    ((normalizerInnerHom P g : SylowAutStabilizer P) :
        MulAut G) =
      MulAut.conj g.1 :=
  rfl

/-- Restriction of the ambient inner automorphism to `N_G(P)` is inner
conjugation by the same normalizer element. -/
@[simp]
theorem normalizerRestrictionHom_normalizerInnerHom
    (P : Sylow p G)
    (g : SylowNormalizer P) :
    normalizerRestrictionHom P (normalizerInnerHom P g) =
      MulAut.conj g := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  rfl

/-- The inner normalizer range acts trivially on every ambient
prime-to-`q` irreducible character. -/
@[simp]
theorem normalizerInnerHom_smul_ambientPPrime
    (P : Sylow p G)
    (g : SylowNormalizer P)
    (χ : PPrimeIrreducibleCharacter G q) :
    normalizerInnerHom P g • χ = χ := by
  change MulAut.conj g.1 • χ = χ
  exact pPrime_conj_smul q g.1 χ

/-- The inner normalizer range also acts trivially on every prime-to-`q`
irreducible character of the restricted normalizer. -/
@[simp]
theorem normalizerInnerHom_smul_normalizerPPrime
    (P : Sylow p G)
    (g : SylowNormalizer P)
    (χ :
      PPrimeIrreducibleCharacter (SylowNormalizer P) q) :
    normalizerInnerHom P g • χ = χ := by
  change
    normalizerRestrictionHom P (normalizerInnerHom P g) • χ = χ
  rw [
    normalizerRestrictionHom_normalizerInnerHom,
    pPrime_conj_smul
  ]

/-- Any equivalence between arbitrarily enumerated ambient and local
character rows intertwines an element of the inner normalizer range. -/
theorem rowEquiv_intertwines_normalizerInnerHom
    (P : Sylow p G)
    {AmbientRow : Type v}
    {LocalRow : Type w}
    (ambientEnumeration :
      AmbientRow ≃ PPrimeIrreducibleCharacter G q)
    (localEnumeration :
      LocalRow ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) q)
    (e : AmbientRow ≃ LocalRow)
    (g : SylowNormalizer P)
    (r : AmbientRow) :
    e
        (ambientEnumeration.symm
          (normalizerInnerHom P g • ambientEnumeration r)) =
      localEnumeration.symm
        (normalizerInnerHom P g • localEnumeration (e r)) := by
  simp

/-- Range-membership form of
`rowEquiv_intertwines_normalizerInnerHom`. -/
theorem rowEquiv_intertwines_mem_normalizerInnerHom_range
    (P : Sylow p G)
    {AmbientRow : Type v}
    {LocalRow : Type w}
    (ambientEnumeration :
      AmbientRow ≃ PPrimeIrreducibleCharacter G q)
    (localEnumeration :
      LocalRow ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) q)
    (e : AmbientRow ≃ LocalRow)
    (a : SylowAutStabilizer P)
    (ha : a ∈ (normalizerInnerHom P).range)
    (r : AmbientRow) :
    e
        (ambientEnumeration.symm
          (a • ambientEnumeration r)) =
      localEnumeration.symm
        (a • localEnumeration (e r)) := by
  obtain ⟨g, rfl⟩ := ha
  exact
    rowEquiv_intertwines_normalizerInnerHom
      P ambientEnumeration localEnumeration e g r

end SylowAutStabilizer
end InductiveMcKay
end McKayConjecture
