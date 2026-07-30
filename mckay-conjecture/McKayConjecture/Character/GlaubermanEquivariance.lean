/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OverAlongTransport
import McKayConjecture.GroupTheory.CoprimeFixedPointNormalizer

/-!
# Equivariance of the Glauberman correspondence

The classical Glauberman correspondent is characterized as the unique
fixed-point constituent whose restriction multiplicity is prime to `p`.
Restriction multiplicity is invariant under simultaneous conjugation.
Consequently uniqueness makes the Glauberman correspondence equivariant
under `N_G(P)`; this is a theorem, not extra correspondence data.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup G) [K.Normal]

/-- Conjugation by `N_G(P)` preserves the subtype of `P`-invariant
prime-to-`p` characters of `K`. -/
def invariantCharacterConjByNormalizer
    (g : Subgroup.normalizer (P : Set G))
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    PInvariantPPrimeIrreducibleCharacter K P p := by
  refine ⟨g • θ.1, ?_⟩
  intro x hx
  rw [IrreducibleCharacter.mem_inertia_iff]
  change
    (x : G) • ((g : G) • θ.1.1) =
      (g : G) • θ.1.1
  have hxconj :
      (g : G)⁻¹ * (x : G) * (g : G) ∈ P :=
    (Subgroup.mem_normalizer_iff.mp g.property
      ((g : G)⁻¹ * (x : G) * (g : G))).mpr (by
        simpa [mul_assoc] using hx)
  have hfix :
      ((g : G)⁻¹ * (x : G) * (g : G)) • θ.1.1 =
        θ.1.1 :=
    (IrreducibleCharacter.mem_inertia_iff
      K θ.1.1
      ((g : G)⁻¹ * (x : G) * (g : G))).mp
        (θ.2 hxconj)
  have hgroup :
      (x : G) * (g : G) =
        (g : G) *
          ((g : G)⁻¹ * (x : G) * (g : G)) := by
    group
  calc
    (x : G) • ((g : G) • θ.1.1) =
        ((x : G) * (g : G)) • θ.1.1 := by
          rw [mul_smul]
    _ =
        ((g : G) *
          ((g : G)⁻¹ * (x : G) * (g : G))) •
            θ.1.1 := by rw [hgroup]
    _ =
        (g : G) •
          (((g : G)⁻¹ * (x : G) * (g : G)) •
            θ.1.1) := by
          rw [mul_smul]
    _ = (g : G) • θ.1.1 := by
          rw [hfix]

@[simp]
theorem invariantCharacterConjByNormalizer_coe
    (g : Subgroup.normalizer (P : Set G))
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    (invariantCharacterConjByNormalizer K P g θ).1 =
      g • θ.1 :=
  rfl

/-- Conjugation by `N_G(P)` on prime-to-`p` characters of `C_K(P)`. -/
def fixedPointCharacterConjByNormalizer
    (g : Subgroup.normalizer (P : Set G))
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p) :
    PPrimeIrreducibleCharacter
      (coprimeFixedPoints K P) p :=
  (coprimeFixedPointsNormalizerAction K P g) • φ

@[simp]
theorem fixedPointCharacterConjByNormalizer_coe
    (g : Subgroup.normalizer (P : Set G))
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p) :
    (fixedPointCharacterConjByNormalizer K P g φ).1 =
      (coprimeFixedPointsNormalizerAction K P g) • φ.1 :=
  rfl

/-- Simultaneous conjugation of a kernel character and a fixed-point
character preserves their exact restriction multiplicity. -/
theorem restrictionMultiplicity_conjByNormalizer
    (g : Subgroup.normalizer (P : Set G))
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p) :
    restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        (fixedPointCharacterConjByNormalizer
          K P g φ).1
        (invariantCharacterConjByNormalizer
          K P g θ).1.1 =
      restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        φ.1 θ.1.1 := by
  let eK : K ≃* K :=
    (MulAut.conjNormal (H := K) (g : G)).symm
  let eC : coprimeFixedPoints K P ≃*
      coprimeFixedPoints K P :=
    (coprimeFixedPointsNormalizerAction K P g).symm
  have hcomm :
      eK.toMonoidHom.comp
          (coprimeFixedPointsInclusion K P) =
        (coprimeFixedPointsInclusion K P).comp
          eC.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rfl
  exact
    restrictionMultiplicity_comap_equiv
      eK eC
      (coprimeFixedPointsInclusion K P)
      (coprimeFixedPointsInclusion K P)
      hcomm φ.1 θ.1.1

namespace GlaubermanCorrespondence

/-- The uniqueness clause in the classical Glauberman theorem forces
normalizer-equivariance of its character equivalence. -/
theorem characterEquiv_conjByNormalizer
    (d : GlaubermanCorrespondence K P p)
    (g : Subgroup.normalizer (P : Set G))
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    d.characterEquiv
        (invariantCharacterConjByNormalizer
          K P g θ) =
      fixedPointCharacterConjByNormalizer
        K P g (d.characterEquiv θ) := by
  symm
  apply d.eq_correspondent_of_multiplicity_isPPrime
  rw [restrictionMultiplicity_conjByNormalizer
    K P g θ (d.characterEquiv θ)]
  exact d.multiplicity_isPPrime θ

/-- Inverse form of normalizer-equivariance.  This is convenient when
the fixed-point character is obtained first, as in the full-fixed
Okuyama--Wajima branch. -/
theorem characterEquiv_symm_conjByNormalizer
    (d : GlaubermanCorrespondence K P p)
    (g : Subgroup.normalizer (P : Set G))
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p) :
    d.characterEquiv.symm
        (fixedPointCharacterConjByNormalizer K P g φ) =
      invariantCharacterConjByNormalizer
        K P g (d.characterEquiv.symm φ) := by
  apply d.characterEquiv.injective
  rw [d.characterEquiv.apply_symm_apply,
    characterEquiv_conjByNormalizer]
  simp

end GlaubermanCorrespondence
end McKayConjecture
