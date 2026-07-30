/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaSourceRouteCanonicalAssembly
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOkuyamaWajimaCharacterInertiaGlaubermanTransport

/-!
# Automatic ordinary count in the exact character inertia

The universal printed Okuyama--Wajima extension statement supplies the
source-route input for the copied kernel action inside the exact character
inertia group.  Navarro's local--global theorem then turns that input into
the uniform semantic comparison consumed by the ordinary fibre count.

The final theorem specializes the universal premise to the proved canonical
assembly, so no residual Okuyama--Wajima hypothesis remains.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordEquivalence
open CliffordCorrespondence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The canonical source-route assembly supplies the semantic uniform input
in the exact form consumed by the base-count API. -/
theorem okuyamaWajimaComplementUniformOrdinaryInput_automatic
    {Γ : Type} [Group Γ] [Finite Γ]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (P : Subgroup Γ) p)
    (phi :
      PInvariantPPrimeIrreducibleCharacter
        K (P : Subgroup Γ) p)
    (hinvariant : ∀ a : Γ, a • phi.1.1 = phi.1.1) :
    OkuyamaWajimaComplementUniformOrdinaryInput
      P K hK hKP d phi := by
  change
    UniformOkuyamaWajimaExtensionComparison
      K (P : Subgroup Γ)
        (okuyamaWajimaAmbientComplement P K hK hKP)
        d phi
  apply
    _root_.McKayConjecture.uniformOkuyamaWajimaExtensionComparison_automatic
  · exact P.isPGroup'
  · exact hK
  · exact hKP
  · exact
      okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP
  · exact hinvariant

/-- The automatic uniform source route, specialized to the copied kernel
action inside the exact character inertia. -/
theorem
    productAmbientGlaubermanLeftOW_uniformOrdinaryInput_automatic
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    UniformOkuyamaWajimaExtensionComparison
      (ProductAmbientGlaubermanLeftOWKernel
        S C hcentral hgenerate theta)
      (ProductAmbientGlaubermanLeftOWSylow
        S C hgenerate theta :
        Subgroup
          (ProductAmbientGlaubermanLeftInertiaGroup
            S C hgenerate theta))
      (okuyamaWajimaAmbientComplement
        (ProductAmbientGlaubermanLeftOWSylow
          S C hgenerate theta)
        (ProductAmbientGlaubermanLeftOWKernel
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftInertiaPPrimeKernel_isPPrimeGroup
          S C hcentral hgenerate theta)
        (productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
          S C hcentral hgenerate theta))
      (productAmbientGlaubermanLeftOWCorrespondence
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
        S C hcentral hgenerate theta) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  let P :=
    ProductAmbientGlaubermanLeftOWSylow
      S C hgenerate theta
  let K :=
    ProductAmbientGlaubermanLeftOWKernel
      S C hcentral hgenerate theta
  let hK :=
    productAmbientGlaubermanLeftInertiaPPrimeKernel_isPPrimeGroup
      S C hcentral hgenerate theta
  let hKP :=
    productAmbientGlaubermanLeftInertiaPPrimeKernel_sup_sylow_normal
      S C hcentral hgenerate theta
  let d :=
    productAmbientGlaubermanLeftOWCorrespondence
      S C hcentral hgenerate g theta
  let phi :=
    productAmbientGlaubermanLeftInertiaInvariantKernelCharacter
      S C hcentral hgenerate theta
  apply
    okuyamaWajimaComplementUniformOrdinaryInput_automatic
      P K hK hKP d phi
  exact
      productAmbientGlaubermanLeftInertiaInvariantKernelCharacter_ambient
        S C hcentral hgenerate theta

/-- Unconditional exact ordinary fibre count in the character inertia,
obtained from the universal printed statement proved by the complete
canonical induction assembly. -/
theorem
    productAmbientGlaubermanLeftOW_natCard_eq_rightInertia_automatic
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
      (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    Nat.card
        (IrreducibleCharactersOverAlong
          (inertiaNormalCopy (product S C) theta.1).subtype
          (productAmbientGlaubermanLeftInertiaTheta
            S C hgenerate theta).1) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (ProductAmbientGlaubermanRightNormalCopy
            S C hcentral hgenerate g theta).subtype
          (inertiaCopyCharacter
            (internalProductNormalizer S C)
            (productAmbientGlaubermanRightKernelTransportCharacter
              S C hcentral g theta))) :=
  productAmbientGlaubermanLeftOW_natCard_eq_rightInertia_transported
    S C hcentral hgenerate g theta
    (productAmbientGlaubermanLeftOW_uniformOrdinaryInput_automatic
      S C hcentral hgenerate g theta)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
