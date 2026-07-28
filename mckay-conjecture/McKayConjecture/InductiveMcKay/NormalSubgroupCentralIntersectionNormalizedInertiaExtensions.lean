/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.InertiaTopExtension
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizedExtension

/-!
# The normalized CP extensions on their full inertia groups

For every active orbit of the normal `q′`-kernel of `CP`, the selected
source extension and determinant-normalized local extension are honest
characters of `CP` and `N_{CP}(P)`.  Activity makes the corresponding
kernel-character inertia groups equal to the whole ambient groups.  This
file pulls both extensions back to those canonical inertia groups and proves
that they afford the canonical inertia triples.

The already-proved normalized central identity is also transported to these
inertia groups.  Its domain is exactly the ambient center.  It should not be
confused with scalar agreement on the entire centralizer of the kernel copy;
that stronger statement is not supplied by the elementary normalized
extension construction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CharacterTriple
open CliffordPartition
open CentralIntersectionKernelAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The selected source extension, pulled back to the full inertia group of
the chosen active kernel representative. -/
def productSourceInertiaExtensionCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter
      (IrreducibleCharacter.inertia
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1) :=
  inertiaTopExtensionCharacter
    (productPPrimeKernel S C hcentral)
    (r.pPrimeOut
      (productPPrimeKernel S C hcentral)).1
    ((productPPrimeKernelCentralIntersectionSetup
      S C hcentral).activeKernel_inertia_eq_top
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral))
        (activePPrimeOut
          (productPPrimeKernel S C hcentral) r).2)
    (productSourcePPrimeExtension
      S C hcentral r).1

/-- The pulled-back source character extends the canonical internal kernel
copy. -/
theorem productSourceInertiaExtensionCharacter_isExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter.IsExtensionAlong
      (CliffordEquivalence.inertiaNormalCopy
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1).subtype
      (CliffordEquivalence.inertiaCopyCharacter
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1)
      (productSourceInertiaExtensionCharacter
        S C hcentral r) :=
  inertiaTopExtensionCharacter_isExtension
    (productPPrimeKernel S C hcentral)
    (r.pPrimeOut
      (productPPrimeKernel S C hcentral)).1
    ((productPPrimeKernelCentralIntersectionSetup
      S C hcentral).activeKernel_inertia_eq_top
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral))
        (activePPrimeOut
          (productPPrimeKernel S C hcentral) r).2)
    (productSourcePPrimeExtension
      S C hcentral r).1
    (productSourcePPrimeExtension_isExtension
      S C hcentral r)

/-- The determinant-normalized local extension, pulled back to the full
inertia group of the matched active local-kernel representative. -/
def productNormalizedLocalInertiaExtensionCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence
      S C hcentral)
    (a : ProductGlaubermanActivationData
      S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter
      (IrreducibleCharacter.inertia
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1)) :=
  inertiaTopExtensionCharacter
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    (((productGlaubermanActiveOrbitEquiv
        S C hcentral g a r).pPrimeOut
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))).1)
    ((productPPrimeKernelCentralIntersectionSetup
      S C hcentral).activeLocalKernel_inertia_eq_top
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        ((productGlaubermanActiveOrbitEquiv
          S C hcentral g a r).pPrimeOut
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C))))
        (activePPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          (productGlaubermanActiveOrbitEquiv
            S C hcentral g a r)).2)
    (productNormalizedLocalExtension
      S C hcentral g a r).1

/-- The pulled-back normalized local character extends the canonical
internal local-kernel copy. -/
theorem productNormalizedLocalInertiaExtensionCharacter_isExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence
      S C hcentral)
    (a : ProductGlaubermanActivationData
      S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter.IsExtensionAlong
      (CliffordEquivalence.inertiaNormalCopy
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1)).subtype
      (CliffordEquivalence.inertiaCopyCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1))
      (productNormalizedLocalInertiaExtensionCharacter
        S C hcentral g a r) :=
  inertiaTopExtensionCharacter_isExtension
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    (((productGlaubermanActiveOrbitEquiv
        S C hcentral g a r).pPrimeOut
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))).1)
    ((productPPrimeKernelCentralIntersectionSetup
      S C hcentral).activeLocalKernel_inertia_eq_top
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        ((productGlaubermanActiveOrbitEquiv
          S C hcentral g a r).pPrimeOut
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C))))
        (activePPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          (productGlaubermanActiveOrbitEquiv
            S C hcentral g a r)).2)
    (productNormalizedLocalExtension
      S C hcentral g a r).1
    (productNormalizedLocalExtension_isExtension
      S C hcentral g a r)

/-- On ambient-central elements, the two full-inertia pullbacks retain the
normalized central identity proved for the selected extensions. -/
theorem productNormalizedInertiaExtensions_central_cross
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence
      S C hcentral)
    (a : ProductGlaubermanActivationData
      S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C)) :
    (productSourceInertiaExtensionCharacter
        S C hcentral r).values
        ((productPPrimeKernelCentralIntersectionSetup
          S C hcentral).kernelInertiaElement
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C))
            r z) *
        ((productNormalizedLocalInertiaExtensionCharacter
          S C hcentral g a r).degree : ℂ) =
      (productNormalizedLocalInertiaExtensionCharacter
          S C hcentral g a r).values
        ((productPPrimeKernelCentralIntersectionSetup
          S C hcentral).localKernelInertiaElement
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C))
            (productGlaubermanActiveOrbitEquiv
              S C hcentral g a r)
            ⟨z,
              Subgroup.center_le_normalizer
                (productSylow S C :
                  Set (product S C)) hz⟩) *
        ((productSourceInertiaExtensionCharacter
          S C hcentral r).degree : ℂ) := by
  change
    (productSourcePPrimeExtension
        S C hcentral r).1.values z *
        ((productNormalizedLocalExtension
          S C hcentral g a r).1.degree : ℂ) =
      (productNormalizedLocalExtension
        S C hcentral g a r).1.values
          ⟨z,
            Subgroup.center_le_normalizer
              (productSylow S C :
                Set (product S C)) hz⟩ *
        ((productSourcePPrimeExtension
          S C hcentral r).1.degree : ℂ)
  exact
    productNormalizedExtensions_central_cross
      S C hcentral g a r z hz

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
