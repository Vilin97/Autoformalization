/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionFromDegree
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanKernelCharacterStabilizer

/-!
# Canonical Gallagher and Sylow parameters in the Glauberman fibre

The normalized Okuyama--Wajima construction already chooses all the data
needed to recover the linear Gallagher coordinate of an ambient
prime-to-`q` character:

1. decompose the character into its active Clifford block;
2. extract its normalized source inertia coordinate;
3. use the inertia-top equivalence to regard that coordinate as an
   ambient extension; and
4. invert the source Gallagher equivalence.

This file gives that definitional chain stable names.  It also transports
the resulting quotient character to the local quotient and records its
restriction to the internal Sylow direct factor.  These are the canonical
linear parameters used when the DGN kernel Hom-action is normalized.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordPartition
open CliffordCorrespondence
open CentralIntersectionKernelAssembly
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productCanonicalSylowParameterFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

/-- The active Clifford block coordinate of an ambient source
character. -/
def productAmbientSourceOrbitBlockCoordinate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    PPrimeOrbitBlock
      (productPPrimeKernel S C hcentral) q
      (activeOrbitIndex
        (productPPrimeKernel S C hcentral) theta).1 :=
  (pPrimeActiveOrbitBlockSigmaEquiv
    (productPPrimeKernel S C hcentral) q theta).2

/-- The canonical source inertia coordinate extracted from an ambient
character's active Clifford block. -/
def productAmbientSourceInertiaCoordinate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    PPrimeIrreducibleCharactersOverInertia
      (productPPrimeKernel S C hcentral)
      ((activeOrbitIndex
        (productPPrimeKernel S C hcentral) theta).pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q :=
  productNormalizedSourceInertiaCoordinate
    S C hcentral
    (activeOrbitIndex
      (productPPrimeKernel S C hcentral) theta)
    (productAmbientSourceOrbitBlockCoordinate
      S C hcentral theta)

/-- The source Gallagher coordinate canonically recovered from an
ambient character. -/
def productAmbientSourceGallagherParameter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ((product S C) ⧸
      productPPrimeKernel S C hcentral) →* ℂˣ :=
  let r :=
    activeOrbitIndex
      (productPPrimeKernel S C hcentral) theta
  (productSourceAmbientGallagherEquiv
      S C hcentral r).symm
    (productSourceInertiaAmbientEquiv
      S C hcentral r
      (productAmbientSourceInertiaCoordinate
        S C hcentral theta))

/-- The recovered Gallagher parameter reconstructs exactly the named
source inertia-top coordinate. -/
theorem productAmbientSourceGallagherParameter_spec
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    productSourceAmbientGallagherEquiv
        S C hcentral
        (activeOrbitIndex
          (productPPrimeKernel S C hcentral) theta)
        (productAmbientSourceGallagherParameter
          S C hcentral theta) =
      productSourceInertiaAmbientEquiv
        S C hcentral
        (activeOrbitIndex
          (productPPrimeKernel S C hcentral) theta)
        (productAmbientSourceInertiaCoordinate
          S C hcentral theta) := by
  exact
    (productSourceAmbientGallagherEquiv
      S C hcentral
      (activeOrbitIndex
        (productPPrimeKernel S C hcentral) theta)
      ).apply_symm_apply
        (productSourceInertiaAmbientEquiv
          S C hcentral
          (activeOrbitIndex
            (productPPrimeKernel S C hcentral) theta)
        (productAmbientSourceInertiaCoordinate
            S C hcentral theta))

/-- The actual source extension reconstructed from the canonical
Gallagher coordinate.  Naming the character, rather than only its linear
parameter, makes the subsequent operator comparison independent of how
the ambient character was originally presented. -/
abbrev productAmbientSourceGallagherCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter (product S C) :=
  (productSourceAmbientGallagherEquiv
    S C hcentral
    (activeOrbitIndex
      (productPPrimeKernel S C hcentral) theta)
    (productAmbientSourceGallagherParameter
      S C hcentral theta)).1.1

/-- Recovering the Gallagher parameter from an ambient character and then
reconstructing the extension returns that ambient character exactly. -/
theorem productAmbientSourceGallagherCharacter_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    productAmbientSourceGallagherCharacter
        S C hcentral theta =
      theta.1 := by
  let K := productPPrimeKernel S C hcentral
  let r := activeOrbitIndex K theta
  let rho :=
    productAmbientSourceInertiaCoordinate
      S C hcentral theta
  let block :=
    productAmbientSourceOrbitBlockCoordinate
      S C hcentral theta
  let e :=
    CliffordEquivalence.cliffordPPrimeCorrespondence
      K (r.pPrimeOut K).1
      (Fact.out : q.Prime)
      (activeOrbit_inertia_index_isPPrime K r)
  let hinertia :
      IrreducibleCharacter.inertia
          K (r.pPrimeOut K).1 = ⊤ :=
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral).activeKernel_inertia_eq_top
        K
        (productSylow S C :
          Subgroup (product S C))
        (r.pPrimeOut K)
        (activePPrimeOut K r).2
  have hspec :=
    congrArg
      (fun z ↦ z.1.1)
      (productAmbientSourceGallagherParameter_spec
        S C hcentral theta)
  have htop :=
    CliffordCorrespondence.cliffordPPrimeCorrespondence_eq_inertiaTopAmbient
      K (r.pPrimeOut K).1 hinertia q
      (Fact.out : q.Prime)
      (activeOrbit_inertia_index_isPPrime K r)
      rho
  have he :
      e rho = block := by
    exact e.apply_symm_apply block
  exact
    hspec.trans
      (htop.symm.trans
        ((congrArg (fun z ↦ z.1.1) he).trans
          (pPrimeActiveOrbitBlockSigmaEquiv_apply_character
            K theta)))

/-- The reconstructed source Gallagher character is an exact extension
of the canonical invariant kernel representative.  This is not an extra
assumption: lying-over is part of the Gallagher fibre, and equality of
degrees follows from linearity of the recovered quotient parameter. -/
theorem productAmbientSourceGallagherCharacter_isExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter.IsExtensionAlong
      (productPPrimeKernel S C hcentral).subtype
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1.1
      (productAmbientSourceGallagherCharacter
        S C hcentral theta) := by
  apply
    IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
  · exact
      (productSourceAmbientGallagherEquiv
        S C hcentral
        (activeOrbitIndex
          (productPPrimeKernel S C hcentral) theta)
        (productAmbientSourceGallagherParameter
          S C hcentral theta)).1.2
  · calc
      (productAmbientSourceGallagherCharacter
          S C hcentral theta).degree =
          (productSourcePPrimeExtension
            S C hcentral
            (activeOrbitIndex
              (productPPrimeKernel S C hcentral) theta)).1.degree :=
        productSourceAmbientGallagherEquiv_degree
          S C hcentral
          (activeOrbitIndex
            (productPPrimeKernel S C hcentral) theta)
          (productAmbientSourceGallagherParameter
            S C hcentral theta)
      _ =
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta).1.1.degree :=
        IrreducibleCharacter.IsExtensionAlong.degree_eq
          (productSourcePPrimeExtension_isExtension
            S C hcentral
            (activeOrbitIndex
              (productPPrimeKernel S C hcentral) theta))

/-- The corresponding canonical linear character of the local
normalizer quotient. -/
def productAmbientLocalGallagherParameter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    (localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) →* ℂˣ :=
  productLinearQuotientEquiv
    S C hcentral
    (productAmbientSourceGallagherParameter
      S C hcentral theta)

/-- The normalized local Gallagher character evaluated at the transported
canonical source parameter. -/
abbrev productAmbientNormalizedLocalGallagherCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :=
  (productNormalizedLocalAmbientGallagherEquiv
    S C hcentral g
    (productGlaubermanActivationData S C hcentral)
    (activeOrbitIndex
      (productPPrimeKernel S C hcentral) theta)
    (productAmbientLocalGallagherParameter
      S C hcentral theta)).1.1

/-- The normalized local Gallagher character is an exact extension of the
matched fixed-point kernel representative. -/
theorem productAmbientNormalizedLocalGallagherCharacter_isExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter.IsExtensionAlong
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))).subtype
      (((productGlaubermanActiveOrbitEquiv
          S C hcentral g
          (productGlaubermanActivationData S C hcentral)
          (activeOrbitIndex
            (productPPrimeKernel S C hcentral) theta)).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))).1)
      (productAmbientNormalizedLocalGallagherCharacter
        S C hcentral g theta) := by
  apply
    IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
  · exact
      (productNormalizedLocalAmbientGallagherEquiv
        S C hcentral g
        (productGlaubermanActivationData S C hcentral)
        (activeOrbitIndex
          (productPPrimeKernel S C hcentral) theta)
        (productAmbientLocalGallagherParameter
          S C hcentral theta)).1.2
  · calc
      (productAmbientNormalizedLocalGallagherCharacter
          S C hcentral g theta).degree =
          (productNormalizedLocalExtension
            S C hcentral g
            (productGlaubermanActivationData S C hcentral)
            (activeOrbitIndex
              (productPPrimeKernel S C hcentral) theta)).1.degree :=
        productNormalizedLocalAmbientGallagherEquiv_degree
          S C hcentral g
          (productGlaubermanActivationData S C hcentral)
          (activeOrbitIndex
            (productPPrimeKernel S C hcentral) theta)
          (productAmbientLocalGallagherParameter
            S C hcentral theta)
      _ =
          (((productGlaubermanActiveOrbitEquiv
              S C hcentral g
              (productGlaubermanActivationData S C hcentral)
              (activeOrbitIndex
                (productPPrimeKernel S C hcentral) theta)).pPrimeOut
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C)))).1).degree :=
        IrreducibleCharacter.IsExtensionAlong.degree_eq
          (productNormalizedLocalExtension_isExtension
            S C hcentral g
            (productGlaubermanActivationData S C hcentral)
            (activeOrbitIndex
              (productPPrimeKernel S C hcentral) theta))

/-- The canonical map from the internal Sylow direct factor to the local
normalizer quotient. -/
def productInternalNormalizerSylowToLocalQuotient
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    internalNormalizerSylow (productSylow S C) →*
      (localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) :=
  (productLocalQuotientSylowEquiv
      S C hcentral).symm.toMonoidHom.comp
    (Subgroup.subgroupOfEquivOfLe
      (show
        (productSylow S C :
            Subgroup (product S C)) ≤
          localNormalizer
            (productSylow S C :
              Subgroup (product S C)) from
        Subgroup.le_normalizer)).toMonoidHom

/-- The canonical scalar character on the local Sylow direct factor.
It is the determinant-normalized base parameter multiplied by the
Gallagher quotient parameter recovered from the ambient source
character. -/
def productAmbientNormalizedLocalSylowLinearParameter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) →* ℂˣ :=
  productLocalSylowLinearParameter
      S C hcentral
      (activeOrbitIndex
        (productPPrimeKernel S C hcentral) theta) *
    (productAmbientLocalGallagherParameter
      S C hcentral theta).comp
        (productInternalNormalizerSylowToLocalQuotient
          S C hcentral)

@[simp]
theorem productAmbientNormalizedLocalSylowLinearParameter_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C)) :
    productAmbientNormalizedLocalSylowLinearParameter
        S C hcentral theta b =
      productLocalSylowLinearParameter
          S C hcentral
          (activeOrbitIndex
            (productPPrimeKernel S C hcentral) theta) b *
        productAmbientLocalGallagherParameter
          S C hcentral theta
          (productInternalNormalizerSylowToLocalQuotient
            S C hcentral b) :=
  rfl

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
