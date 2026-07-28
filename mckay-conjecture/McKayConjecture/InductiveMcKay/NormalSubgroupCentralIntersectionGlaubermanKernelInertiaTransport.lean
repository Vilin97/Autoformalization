/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanKernelCharacterStabilizer
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45FactorExtensionNormalizer
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45OuterQuotients

/-!
# Transport from matched inertia to the Glauberman kernel stabilizer

For a prime-to-`q` character of `CS`, its active Clifford orbit selects a
canonical `P`-invariant character of the normal `q'`-kernel.  Every element
of the matched right inertia group fixes the ambient character, hence fixes
that active orbit and its canonical representative.  This gives the
homomorphism from the right inertia group to the kernel-character
stabilizer needed to compare the Dade--Glauberman factor with the final
inertia-quotient factor.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open CharacterTriple
namespace Proposition45

open ComplementReduction

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productGlaubermanKernelInertiaTransportSourceFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

noncomputable local instance productGlaubermanKernelInertiaTransportTargetFintype :
    Fintype (internalProductNormalizer S C) :=
  Fintype.ofFinite (internalProductNormalizer S C)

/-- The matched target character, named locally for the kernel transport. -/
abbrev productAmbientGlaubermanRightKernelTransportCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    IrreducibleCharacter (internalProductNormalizer S C) :=
  productAmbientGlaubermanRightCharacter
    S C hcentral g theta

/-- A matched right-inertia element fixes the source character under the
ambient-normalizer action. -/
theorem productAmbientGlaubermanRightInertia_fixed_sourceCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    (b : ambientNormalizer S) • theta = theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  have hb :=
    (productAmbientGlaubermanInertiaEmbedding
      S C hcentral hgenerate g theta b).property
  apply Subtype.ext
  exact
    (IrreducibleCharacter.mem_inertia_iff
      (product S C) theta.1
      (((b : ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
          ambientNormalizer S) : X)).mp hb

/-- The canonical homomorphism from the matched right inertia group into
the stabilizer of the selected source-kernel character. -/
def productAmbientGlaubermanRightInertiaToKernelStabilizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta →*
      ProductGlaubermanKernelCharacterStabilizer
        S C hcentral
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta) where
  toFun b :=
    ⟨(b : ambientNormalizer S),
      productAmbientGlaubermanSourceKernelCharacter_fixed_of_fixed
        S C hcentral theta (b : ambientNormalizer S)
        (productAmbientGlaubermanRightInertia_fixed_sourceCharacter
          S C hcentral hgenerate g theta b)⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' b c := by
    apply Subtype.ext
    rfl

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
