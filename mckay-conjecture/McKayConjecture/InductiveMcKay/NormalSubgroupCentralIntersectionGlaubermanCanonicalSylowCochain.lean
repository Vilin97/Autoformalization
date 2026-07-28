/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSylowScalar

/-!
# Canonical Sylow-normalizing cochain

The canonical Gallagher extensions determine a scalar on the Sylow
factor of the right normal copy.  This file extends its inverse to the
whole right inertia group and proves, from that construction, that the
rescaled selected action is the identity on the Sylow factor.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The inclusion of the Sylow factor of the right normal copy into the
matched right inertia group is injective. -/
theorem productAmbientGlaubermanRightNormalSylowToInertia_injective
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    Function.Injective
      (productAmbientGlaubermanRightNormalSylowToInertia
        S C hcentral hgenerate g theta) := by
  intro b d hbd
  have hnormal :
      productAmbientGlaubermanRightNormalCopySylowHom
          S C hcentral hgenerate g theta b =
        productAmbientGlaubermanRightNormalCopySylowHom
          S C hcentral hgenerate g theta d :=
    Subtype.ext hbd
  have hpair :=
    (productAmbientGlaubermanRightNormalCopyProductEquiv
      S C hcentral hgenerate g theta).injective hnormal
  exact congrArg Prod.snd hpair

/-- The cochain selected by the canonical Gallagher comparison.  Its
restriction to the Sylow factor is definitionally forced to cancel the
canonical scalar; away from that factor it is harmlessly extended by
`1`. -/
def productAmbientGlaubermanCanonicalInertiaCochain
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta → ℂˣ :=
  Function.extend
    (productAmbientGlaubermanRightNormalSylowToInertia
      S C hcentral hgenerate g theta)
    (fun b ↦
      (productAmbientGlaubermanCanonicalSelectedSylowScalar
        S C hcentral hgenerate g theta b)⁻¹)
    1

/-- On the embedded Sylow factor, the canonical inertia cochain is
exactly the inverse selected scalar. -/
@[simp]
theorem productAmbientGlaubermanCanonicalInertiaCochain_apply_sylow
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b : internalNormalizerSylow (productSylow S C)) :
    productAmbientGlaubermanCanonicalInertiaCochain
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanRightNormalSylowToInertia
          S C hcentral hgenerate g theta b) =
      (productAmbientGlaubermanCanonicalSelectedSylowScalar
        S C hcentral hgenerate g theta b)⁻¹ := by
  exact
    (productAmbientGlaubermanRightNormalSylowToInertia_injective
      S C hcentral hgenerate g theta).extend_apply _ _ b

/-- Construction-derived normalization regression: after restricting to
the canonical selected summand and rescaling by the canonical cochain,
every Sylow-factor operator is the identity.  No cochain restriction is
assumed by this theorem. -/
theorem productAmbientGlaubermanCanonical_rescaledKernelSylow_operator_eq_one
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (hstable :
      (productAmbientGlaubermanRestrictedKernelMultiplicityProjective
        S C hcentral hgenerate g theta).IsStable
          (ProductAmbientGlaubermanKernelSylowScalarSubspace
            S C hcentral hgenerate g theta
            (productAmbientGlaubermanCanonicalSelectedSylowScalar
              S C hcentral hgenerate g theta)))
    [Nontrivial
      (ProductAmbientGlaubermanKernelSylowScalarSubspace
        S C hcentral hgenerate g theta
        (productAmbientGlaubermanCanonicalSelectedSylowScalar
          S C hcentral hgenerate g theta))]
    (b : internalNormalizerSylow (productSylow S C)) :
    ((((productAmbientGlaubermanRestrictedKernelMultiplicityProjective
            S C hcentral hgenerate g theta).restrictStable
              (ProductAmbientGlaubermanKernelSylowScalarSubspace
                S C hcentral hgenerate g theta
                (productAmbientGlaubermanCanonicalSelectedSylowScalar
                  S C hcentral hgenerate g theta))
              hstable).rescale
                (productAmbientGlaubermanCanonicalInertiaCochain
                  S C hcentral hgenerate g theta)).operator
          (productAmbientGlaubermanRightNormalSylowToInertia
            S C hcentral hgenerate g theta b) = 1) := by
  rw [
    productAmbientGlauberman_rescaledKernelSylow_operator_eq_one_iff
      S C hcentral hgenerate g theta
      (productAmbientGlaubermanCanonicalSelectedSylowScalar
        S C hcentral hgenerate g theta)
      hstable
      (productAmbientGlaubermanCanonicalInertiaCochain
        S C hcentral hgenerate g theta)
      b]
  exact
    productAmbientGlaubermanCanonicalInertiaCochain_apply_sylow
      S C hcentral hgenerate g theta b

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
