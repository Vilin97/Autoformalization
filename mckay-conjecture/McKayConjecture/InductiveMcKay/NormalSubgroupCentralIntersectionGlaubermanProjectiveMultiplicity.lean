/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanProjectiveMultiplicity
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerCharacterTransport

/-!
# The kernel Glauberman projective multiplicity obstruction

Fix a `P`-invariant character `θ` of the canonical normal `q′`-kernel in
`CP`.  Its stabilizer in `N_X(P)` acts on the kernel and on its fixed-point
subgroup.  Ambient Glauberman equivariance proves that both `θ` and its
Glauberman correspondent are invariant under those restricted actions.

Consequently the canonical Glauberman Hom-space carries a projective action
of this stabilizer.  Its dimension is prime to `q`, so a `q`-primary
mismatch class must vanish.

This is the multiplicity-space part of the Dade--Glauberman--Nagao
obstruction argument.  Identifying this kernel factor mismatch with the
factor mismatch of the final matched `CP` inertia characters is a separate
transport theorem.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CharacterTriple

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The subgroup of the ambient Sylow normalizer fixing a selected
`P`-invariant source-kernel character. -/
abbrev ProductGlaubermanKernelCharacterStabilizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :=
  MulAction.stabilizer (ambientNormalizer S) θ.1

/-- The restricted stabilizer action on the source `q′`-kernel. -/
def productGlaubermanKernelStabilizerAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :
    ProductGlaubermanKernelCharacterStabilizer
        S C hcentral θ →*
      MulAut (productPPrimeKernel S C hcentral) :=
  (productPPrimeKernelConjugationHom S C hcentral).comp
    (MulAction.stabilizer (ambientNormalizer S) θ.1).subtype

/-- The restricted stabilizer action on the kernel fixed points. -/
def productGlaubermanFixedPointsStabilizerAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :
    ProductGlaubermanKernelCharacterStabilizer
        S C hcentral θ →*
      MulAut (productPPrimeKernelFixedPoints S C hcentral) :=
  (productPPrimeKernelFixedPointsConjugationHom
      S C hcentral).comp
    (MulAction.stabilizer (ambientNormalizer S) θ.1).subtype

/-- The fixed-point inclusion is equivariant for the two restricted
stabilizer actions. -/
theorem productGlaubermanStabilizerActions_inclusion_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q)
    (γ :
      ProductGlaubermanKernelCharacterStabilizer
        S C hcentral θ)
    (x : productPPrimeKernelFixedPoints S C hcentral) :
    coprimeFixedPointsInclusion
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (productGlaubermanFixedPointsStabilizerAction
          S C hcentral θ γ x) =
      productGlaubermanKernelStabilizerAction
        S C hcentral θ γ
        (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)) x) := by
  rfl

/-- The selected source-kernel character is invariant under its ambient
normalizer stabilizer action. -/
theorem productGlaubermanKernelCharacter_isInvariant
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :
    IsInvariant
      (productGlaubermanKernelStabilizerAction
        S C hcentral θ)
      θ.1.1 := by
  intro γ x
  have hfix :
      ((γ⁻¹ :
        ProductGlaubermanKernelCharacterStabilizer
          S C hcentral θ) :
        ambientNormalizer S) • θ.1 =
      θ.1 :=
    (γ⁻¹).property
  have hvalues :=
    congrArg
      (fun χ :
        PPrimeIrreducibleCharacter
          (productPPrimeKernel S C hcentral) q ↦
        χ.1.values x)
      hfix
  change
    θ.1.1.values
        ((productPPrimeKernelConjugationHom
          S C hcentral
          (((γ⁻¹ :
            ProductGlaubermanKernelCharacterStabilizer
              S C hcentral θ) :
            ambientNormalizer S))).symm x) =
      θ.1.1.values x at hvalues
  rw [show
    (((γ⁻¹ :
        ProductGlaubermanKernelCharacterStabilizer
          S C hcentral θ) :
      ambientNormalizer S)) =
        (((γ :
          ProductGlaubermanKernelCharacterStabilizer
            S C hcentral θ) :
          ambientNormalizer S))⁻¹ by rfl,
    map_inv] at hvalues
  simpa [productGlaubermanKernelStabilizerAction] using hvalues

/-- Ambient Glauberman equivariance makes the fixed-point correspondent
invariant under the same character stabilizer. -/
theorem productGlaubermanFixedPointCharacter_isInvariant
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :
    IsInvariant
      (productGlaubermanFixedPointsStabilizerAction
        S C hcentral θ)
      (g.characterEquiv θ).1 := by
  intro γ x
  let h : ambientNormalizer S :=
    ((γ⁻¹ :
      ProductGlaubermanKernelCharacterStabilizer
        S C hcentral θ) :
      ambientNormalizer S)
  have hsource :
      productPInvariantCharacterConjugation
          S C hcentral h θ =
        θ := by
    apply Subtype.ext
    rw [productPInvariantCharacterConjugation_coe]
    exact (γ⁻¹).property
  have hcovariance :=
    productGlaubermanCharacterEquiv_conjugation
      S C hcentral g h θ
  rw [hsource] at hcovariance
  have hfixed :
      productPPrimeKernelFixedPointsConjugation
          S C hcentral h • g.characterEquiv θ =
        g.characterEquiv θ :=
    hcovariance.symm
  have hvalues :=
    congrArg
      (fun χ :
        PPrimeIrreducibleCharacter
          (productPPrimeKernelFixedPoints
            S C hcentral) q ↦
        χ.1.values x)
      hfixed
  change
    (g.characterEquiv θ).1.values
        ((productPPrimeKernelFixedPointsConjugation
          S C hcentral h).symm x) =
      (g.characterEquiv θ).1.values x at hvalues
  rw [show
    h =
      (((γ :
        ProductGlaubermanKernelCharacterStabilizer
          S C hcentral θ) :
        ambientNormalizer S))⁻¹ by rfl] at hvalues
  change
    (g.characterEquiv θ).1.values
        ((productPPrimeKernelFixedPointsConjugationHom
          S C hcentral
          (((γ :
            ProductGlaubermanKernelCharacterStabilizer
              S C hcentral θ) :
            ambientNormalizer S))⁻¹).symm x) =
      (g.characterEquiv θ).1.values x at hvalues
  rw [map_inv] at hvalues
  simpa [productGlaubermanFixedPointsStabilizerAction] using hvalues

/-- The canonical kernel-level projective factor mismatch for the selected
Glauberman pair and its full ambient-normalizer stabilizer. -/
abbrev productGlaubermanKernelProjectiveMultiplicityFactorSet
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :=
  g.ProjectiveMultiplicityFactorSet
    (productGlaubermanKernelStabilizerAction
      S C hcentral θ)
    (productGlaubermanFixedPointsStabilizerAction
      S C hcentral θ)
    θ
    (productGlaubermanKernelCharacter_isInvariant
      S C hcentral θ)
    (productGlaubermanFixedPointCharacter_isInvariant
      S C hcentral g θ)

/-- The exact kernel-level `q`-primary assertion left by the projective
multiplicity argument. -/
def ProductGlaubermanKernelProjectiveMultiplicityMismatchIsQPrimary
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) : Prop :=
  g.ProjectiveMultiplicityMismatchIsPPrimary
    (productGlaubermanKernelStabilizerAction
      S C hcentral θ)
    (productGlaubermanFixedPointsStabilizerAction
      S C hcentral θ)
    θ
    (productGlaubermanKernelCharacter_isInvariant
      S C hcentral θ)
    (productGlaubermanFixedPointCharacter_isInvariant
      S C hcentral g θ)

/-- A `q`-primary kernel Glauberman mismatch vanishes: the coprime
annihilator is supplied unconditionally by the classical correspondence. -/
theorem productGlaubermanKernelProjectiveMultiplicityFactorSet_h2Class_eq_zero
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q)
    (hprimary :
      ProductGlaubermanKernelProjectiveMultiplicityMismatchIsQPrimary
        S C hcentral g θ) :
    letI :=
      trivialMulDistribMulAction
        (ProductGlaubermanKernelCharacterStabilizer
          S C hcentral θ) ℂˣ
    (productGlaubermanKernelProjectiveMultiplicityFactorSet
      S C hcentral g θ).h2Class =
      0 := by
  exact
    g.projectiveMultiplicityFactorSet_h2Class_eq_zero_of_pPrimary
      (productGlaubermanKernelStabilizerAction
        S C hcentral θ)
      (productGlaubermanFixedPointsStabilizerAction
        S C hcentral θ)
      (productGlaubermanStabilizerActions_inclusion_commutes
        S C hcentral θ)
      θ
      (productGlaubermanKernelCharacter_isInvariant
        S C hcentral θ)
      (productGlaubermanFixedPointCharacter_isInvariant
        S C hcentral g θ)
      hprimary

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
