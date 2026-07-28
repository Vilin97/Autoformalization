/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalPPrimeKernelGlauberman
import McKayConjecture.InductiveMcKay.NormalPPrimeKernelExtensionConstruction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionActivation
import McKayConjecture.InductiveMcKay.CentralScalarLocalCorrespondence

/-!
# The Glauberman route for Rossi's central-intersection subgroup

This file specializes the normal `p′`-kernel construction to `CP`.  The
classical Glauberman correspondence and the two elementary activation
facts construct the active-orbit matching.  What remains is precisely the
Okuyama--Wajima comparison of the characters above each matched pair,
including its central-value refinement.

The resulting data is converted to `ActiveKernelCentralFibreData` for the
coprime kernel and hence gives the desired central-scalar McKay
correspondence for `CP`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordCorrespondence
open CliffordPartition
open CentralIntersectionKernelAssembly
open NormalPPrimeKernelGlauberman

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The classical Glauberman correspondence for the canonical normal
`q′`-kernel of `CP`. -/
abbrev ProductGlaubermanCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :=
  GlaubermanCorrespondence
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    q

/-- The canonical-extension and direct-product activation facts for the
Glauberman correspondence in `CP`. -/
abbrev ProductGlaubermanActivationData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :=
  ActivationData
    (p := q)
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral)
    (localKernelAmbientFixedPointsEquiv
      S C hcentral)

/-- The actual remaining source activation input: prime-to-`q` extensions
of invariant characters of the normal `q′`-kernel.  The local activation
half is constructed in
`NormalSubgroupCentralIntersectionActivation` by extending across the
direct product with the trivial Sylow character. -/
abbrev ProductInvariantPPrimeExtensionData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :=
  InvariantPPrimeExtensionData
    (p := q)
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral)

/-- The invariant source extensions are canonical consequences of the
normal Hall `q'` extension theorem. -/
def productInvariantPPrimeExtensionData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    ProductInvariantPPrimeExtensionData
      S C hcentral :=
  invariantPPrimeExtensionDataOfPPrimeKernel
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral)
    (productPPrimeKernel_isPPrimeGroup
      S C hcentral)

/-- Construct all Glauberman activation data from invariant source
extensions.  The target clause is a theorem, not an input. -/
theorem productGlaubermanActivationDataOfExtensions
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d :
      ProductInvariantPPrimeExtensionData
        S C hcentral) :
    ProductGlaubermanActivationData
      S C hcentral :=
  ActivationData.ofInvariantExtensions d
    (productFixedPointCharacter_isActive
      S C hcentral)

/-- All activation facts needed by the Glauberman correspondence in `CP`
are theorems. -/
theorem productGlaubermanActivationData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    ProductGlaubermanActivationData
      S C hcentral :=
  productGlaubermanActivationDataOfExtensions
    S C hcentral
    (productInvariantPPrimeExtensionData
      S C hcentral)

/-- Above an invariant source character, the whole prime-to-`q` fibre is
parametrized by multiplicative linear characters of the quotient. -/
def productSourceLinearGallagherEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d :
      ProductInvariantPPrimeExtensionData
        S C hcentral)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :
    (((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) ≃
      PPrimeIrreducibleCharactersOverAlong
        (productPPrimeKernel S C hcentral).subtype
        θ.1.1 q :=
  d.linearGallagherEquiv θ

/-- The actual active Clifford-orbit equivalence constructed from the
classical Glauberman correspondence. -/
def productGlaubermanActiveOrbitEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral) :
    ActiveOrbit
        (productPPrimeKernel S C hcentral) q ≃
      ActiveOrbit
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q :=
  a.activeOrbitEquiv g

/-- The active Clifford-orbit equivalence with its elementary activation
constructed from invariant source extensions. -/
def productGlaubermanActiveOrbitEquivOfExtensions
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (d :
      ProductInvariantPPrimeExtensionData
        S C hcentral) :
    ActiveOrbit
        (productPPrimeKernel S C hcentral) q ≃
      ActiveOrbit
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q :=
  productGlaubermanActiveOrbitEquiv
    S C hcentral g
      (productGlaubermanActivationDataOfExtensions
        S C hcentral d)

/-- The active Clifford-orbit equivalence with all extension and activation
facts discharged. -/
def productGlaubermanActiveOrbitEquivCanonical
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral) :
    ActiveOrbit
        (productPPrimeKernel S C hcentral) q ≃
      ActiveOrbit
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q :=
  productGlaubermanActiveOrbitEquiv
    S C hcentral g
    (productGlaubermanActivationData
      S C hcentral)

/-- The remaining Okuyama--Wajima theorem after the active orbits have
been matched by the classical Glauberman correspondence.

This is an inertia-fibre statement, not an ambient McKay equivalence.  Its
central clause is the exact numerical refinement required for the
central-scalar reduction. -/
structure ProductOkuyamaWajimaFibreData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral) where
  /-- Prime-to-`q` characters above matched invariant kernel characters
  have the same cardinality; a finite equivalence is selected here. -/
  inertiaFibreEquiv :
    ∀ r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q,
      PPrimeIrreducibleCharactersOverInertia
          (productPPrimeKernel S C hcentral)
          (r.pPrimeOut
            (productPPrimeKernel S C hcentral)).1 q ≃
        PPrimeIrreducibleCharactersOverInertia
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          (((productGlaubermanActiveOrbitEquiv
              S C hcentral g a r).pPrimeOut
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C)))).1) q
  /-- The Okuyama--Wajima comparison preserves normalized values at
  ambient-central elements. -/
  inertia_central_cross :
    ∀ (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
      (ρ :
        PPrimeIrreducibleCharactersOverInertia
          (productPPrimeKernel S C hcentral)
          (r.pPrimeOut
            (productPPrimeKernel S C hcentral)).1 q)
      (z : product S C)
      (hzcentral :
        z ∈ Subgroup.center (product S C)),
      ρ.1.1.values
          ((productPPrimeKernelCentralIntersectionSetup
            S C hcentral).kernelInertiaElement
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C))
              r z) *
          (((inertiaFibreEquiv r ρ).1.1.degree : ℂ)) =
        (inertiaFibreEquiv r ρ).1.1.values
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
                      Set (product S C))
                    hzcentral⟩) *
          (ρ.1.1.degree : ℂ)

/-- The Okuyama--Wajima fibre theorem with elementary activation generated
from invariant source extensions. -/
abbrev ProductOkuyamaWajimaFibreDataOfExtensions
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (d :
      ProductInvariantPPrimeExtensionData
        S C hcentral) :=
  ProductOkuyamaWajimaFibreData
    S C hcentral g
      (productGlaubermanActivationDataOfExtensions
        S C hcentral d)

/-- The remaining Okuyama--Wajima fibre input after all invariant-extension
and activation facts have been constructed. -/
abbrev ProductOkuyamaWajimaFibreDataCanonical
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral) :=
  ProductOkuyamaWajimaFibreData
    S C hcentral g
    (productGlaubermanActivationData
      S C hcentral)

namespace ProductOkuyamaWajimaFibreData

/-- Combine the genuinely lower-level Glauberman and Okuyama--Wajima
pieces into the numerical active-kernel interface. -/
def toActiveKernelCentralFibreData
    {hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X}
    {g :
      ProductGlaubermanCorrespondence
        S C hcentral}
    {a :
      ProductGlaubermanActivationData
        S C hcentral}
    (d :
      ProductOkuyamaWajimaFibreData
        S C hcentral g a) :
    ActiveKernelCentralFibreData
      (p := q)
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))
      (productPPrimeKernelCentralIntersectionSetup
        S C hcentral) where
  activeOrbitEquiv :=
    productGlaubermanActiveOrbitEquiv
      S C hcentral g a
  inertiaFibreEquiv := d.inertiaFibreEquiv
  inertia_central_cross :=
    d.inertia_central_cross

end ProductOkuyamaWajimaFibreData

namespace ProductOkuyamaWajimaFibreDataOfExtensions

/-- Convert the source-extension form of Okuyama--Wajima directly to the
exact numerical active-kernel input used by the Clifford assembly. -/
def toActiveKernelCentralFibreData
    {hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X}
    {g :
      ProductGlaubermanCorrespondence
        S C hcentral}
    {e :
      ProductInvariantPPrimeExtensionData
        S C hcentral}
    (d :
      ProductOkuyamaWajimaFibreDataOfExtensions
        S C hcentral g e) :
    ActiveKernelCentralFibreData
      (p := q)
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))
      (productPPrimeKernelCentralIntersectionSetup
        S C hcentral) :=
  ProductOkuyamaWajimaFibreData.toActiveKernelCentralFibreData
    S C d

end ProductOkuyamaWajimaFibreDataOfExtensions

namespace ProductOkuyamaWajimaFibreDataCanonical

/-- Convert the canonical-activation Okuyama--Wajima data directly to the
active-kernel numerical interface. -/
def toActiveKernelCentralFibreData
    {hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X}
    {g :
      ProductGlaubermanCorrespondence
        S C hcentral}
    (d :
      ProductOkuyamaWajimaFibreDataCanonical
        S C hcentral g) :
    ActiveKernelCentralFibreData
      (p := q)
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))
      (productPPrimeKernelCentralIntersectionSetup
        S C hcentral) :=
  ProductOkuyamaWajimaFibreData.toActiveKernelCentralFibreData
    S C d

end ProductOkuyamaWajimaFibreDataCanonical

/-- The ordinary-character correspondence for `CP` assembled through its
normal `q′`-kernel. -/
def complementCharacterEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d :
      ActiveKernelCentralFibreData
        (p := q)
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (productPPrimeKernelCentralIntersectionSetup
          S C hcentral)) :
    PPrimeIrreducibleCharacter (product S C) q ≃
      PPrimeIrreducibleCharacter
        (Subgroup.normalizer
          (productSylow S C :
            Set (product S C))) q :=
  d.assembledPPrimeEquiv

/-- The central-scalar local correspondence assembled through the normal
`q′`-kernel. -/
def complementCentralScalarLocalCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d :
      ActiveKernelCentralFibreData
        (p := q)
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (productPPrimeKernelCentralIntersectionSetup
          S C hcentral)) :
    CentralScalarLocalCorrespondence
      (productSylow S C) where
  toLocalCorrespondence :=
    { intermediate :=
        Subgroup.normalizer
          (productSylow S C :
            Set (product S C))
      normalizer_le := le_rfl
      proper_of_normalizer_ne_top := fun hne =>
        lt_top_iff_ne_top.mpr hne
      correspondence :=
        complementCharacterEquiv
          S C hcentral d }
  correspondence_central_cross := by
    intro χ z hzcentral hzintermediate
    have h :=
      ActiveKernelCentralFibreData.assembledPPrimeEquiv_central_cross
        (K := productPPrimeKernel S C hcentral)
        (P := (productSylow S C :
          Subgroup (product S C)))
        d χ z hzcentral
    have hzEq :
        (⟨z,
          Subgroup.center_le_normalizer
            (productSylow S C :
              Set (product S C))
            hzcentral⟩ :
          Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) =
        ⟨z, hzintermediate⟩ :=
      Subtype.ext rfl
    rw [hzEq] at h
    convert h using 1 <;>
      rfl

/-- The central-scalar correspondence obtained directly from the classical
Glauberman theorem, invariant source extensions, and the remaining
Okuyama--Wajima inertia-fibre comparison. -/
def complementCentralScalarLocalCorrespondenceOfOkuyamaWajima
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    {g :
      ProductGlaubermanCorrespondence
        S C hcentral}
    {e :
      ProductInvariantPPrimeExtensionData
        S C hcentral}
    (d :
      ProductOkuyamaWajimaFibreDataOfExtensions
        S C hcentral g e) :
    CentralScalarLocalCorrespondence
      (productSylow S C) :=
  complementCentralScalarLocalCorrespondence
    S C hcentral
      (ProductOkuyamaWajimaFibreDataOfExtensions.toActiveKernelCentralFibreData
        S C d)

/-- The central-scalar correspondence from the classical Glauberman theorem
and the remaining Okuyama--Wajima fibre comparison, with invariant
extensions constructed internally. -/
def complementCentralScalarLocalCorrespondenceOfCanonicalOkuyamaWajima
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    {g :
      ProductGlaubermanCorrespondence
        S C hcentral}
    (d :
      ProductOkuyamaWajimaFibreDataCanonical
        S C hcentral g) :
    CentralScalarLocalCorrespondence
      (productSylow S C) :=
  complementCentralScalarLocalCorrespondence
    S C hcentral
    (ProductOkuyamaWajimaFibreDataCanonical.toActiveKernelCentralFibreData
      S C d)

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
