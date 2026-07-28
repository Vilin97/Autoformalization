/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizedFibre

/-!
# Okuyama--Wajima fibres for the central-intersection product

The normal `q′`-kernel, Glauberman correspondence, determinant-normalized
extensions, and Gallagher coordinates constructed in the preceding files
prove the complete numerical Okuyama--Wajima fibre package.  Thus no
additional fibre equivalence or central-value hypothesis is needed once a
Glauberman correspondence has been supplied.
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

/-- The full Okuyama--Wajima fibre package constructed from normalized
Gallagher coordinates. -/
def productOkuyamaWajimaFibreData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral) :
    ProductOkuyamaWajimaFibreData
      S C hcentral g a where
  inertiaFibreEquiv :=
    productNormalizedOkuyamaWajimaInertiaFibreEquiv
      S C hcentral g a
  inertia_central_cross := by
    intro r rho z hz
    exact
      productNormalizedOkuyamaWajimaInertiaFibreEquiv_central_cross
        S C hcentral g a r rho z hz

/-- The canonical Okuyama--Wajima package, with activation and invariant
extensions constructed internally. -/
def productOkuyamaWajimaFibreDataCanonical
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral) :
    ProductOkuyamaWajimaFibreDataCanonical
      S C hcentral g :=
  productOkuyamaWajimaFibreData
    S C hcentral g
    (productGlaubermanActivationData
      S C hcentral)

/-- The central-scalar correspondence for `CP`, constructed solely from
the classical Glauberman correspondence and the proved elementary
normal-kernel machinery. -/
def complementCentralScalarLocalCorrespondenceOfGlauberman
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral) :
    CentralScalarLocalCorrespondence
      (productSylow S C) :=
  complementCentralScalarLocalCorrespondenceOfCanonicalOkuyamaWajima
    S C hcentral
    (productOkuyamaWajimaFibreDataCanonical
      S C hcentral g)

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
