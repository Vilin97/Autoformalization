/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCoprimeClassVanishing
import McKayConjecture.CharacterTriple.FactorSetPGroupPullback
import McKayConjecture.CharacterTriple.ProjectiveMultiplicityMismatch
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanKernelNormalCopyDecomposition
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45OuterQuotients

/-!
# Descent of the kernel Glauberman obstruction to the outer quotient

This file isolates the exact cohomological transport needed after the
kernel multiplicity construction.

Suppose the kernel Glauberman mismatch is pulled back from a finite
`q`-group `D`.  Restrict the corresponding homomorphism to the matched
right inertia group.  If this composite kills the canonical normal copy,
it descends to the right outer quotient.  An explicit gauge equality
between the final quotient mismatch and the descended factor then:

* inflates back to the restricted kernel mismatch on the inertia group;
* makes the final mismatch simultaneously `q`-primary and a class on a
  `q'`-group; and therefore
* proves the intrinsic Proposition-4.5 projective obstruction agreement.

Thus the remaining representation-theoretic input is stated as an actual
factorization and gauge transport, not as an opaque cohomology hypothesis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordEquivalence
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The final mismatch of the canonical associated projective
representations, as a factor set on the matched right outer quotient. -/
abbrev productAmbientGlaubermanQuotientMismatchFactorSet
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta).quotientFactorSetAlong
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta) *
    (productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta).quotientFactorSet⁻¹

/-- The quotient projection from the matched right inertia group to its
canonical outer quotient. -/
abbrev productAmbientGlaubermanRightInertiaQuotientHom
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta →*
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta :=
  by
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    exact
      QuotientGroup.mk'
        (inertiaNormalCopy
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightCharacter
            S C hcentral g theta))

/-- If the `D`-valued kernel-obstruction homomorphism kills the normal
copy in the matched right inertia group, it descends canonically to the
right outer quotient. -/
def productAmbientGlaubermanRightOuterToKernelObstructionHom
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D]
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (hkill :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      inertiaNormalCopy
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightCharacter
            S C hcentral g theta) ≤
        (rho.comp
          (productAmbientGlaubermanRightInertiaToKernelStabilizer
            S C hcentral hgenerate g theta)).ker) :
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta →* D :=
  by
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    exact
      QuotientGroup.lift
        (inertiaNormalCopy
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightCharacter
            S C hcentral g theta))
        (rho.comp
          (productAmbientGlaubermanRightInertiaToKernelStabilizer
            S C hcentral hgenerate g theta))
        hkill

@[simp]
theorem productAmbientGlaubermanRightOuterToKernelObstructionHom_mk
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D]
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (hkill :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      inertiaNormalCopy
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightCharacter
            S C hcentral g theta) ≤
        (rho.comp
          (productAmbientGlaubermanRightInertiaToKernelStabilizer
            S C hcentral hgenerate g theta)).ker)
    (b :
      ProductAmbientGlaubermanRightInertiaGroup
        S C hcentral hgenerate g theta) :
    productAmbientGlaubermanRightOuterToKernelObstructionHom
        S C hcentral hgenerate g theta D rho hkill
        (productAmbientGlaubermanRightInertiaQuotientHom
          S C hcentral hgenerate g theta b) =
      rho
        (productAmbientGlaubermanRightInertiaToKernelStabilizer
          S C hcentral hgenerate g theta b) := by
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    QuotientGroup.lift_mk'
      (inertiaNormalCopy
        (internalProductNormalizer S C)
        (productAmbientGlaubermanRightCharacter
          S C hcentral g theta))
      hkill b

/-- Once the kernel-obstruction homomorphism descends to the right outer
quotient, the descended homomorphism is trivial: its source is a finite
`q'`-group and its target is a `q`-group. -/
theorem productAmbientGlaubermanRightOuterToKernelObstructionHom_eq_one
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D]
    (hD : IsPGroup q D)
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (hkill :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      inertiaNormalCopy
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightCharacter
            S C hcentral g theta) ≤
        (rho.comp
          (productAmbientGlaubermanRightInertiaToKernelStabilizer
            S C hcentral hgenerate g theta)).ker) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI : (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    productAmbientGlaubermanRightOuterToKernelObstructionHom
        S C hcentral hgenerate g theta D rho hkill =
      1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    McKayConjecture.GroupTheory.MonoidHom.eq_one_of_isPPrimeGroup_of_isPGroup
      (productAmbientGlaubermanRightOuterToKernelObstructionHom
        S C hcentral hgenerate g theta D rho hkill)
      (productAmbientGlaubermanRightOuterQuotient_isPPrimeGroup
        S C hcentral hgenerate g theta)
      hD

/-- The precise factor-level transport assertion: after inflation from
the right outer quotient, the final mismatch is gauge-equivalent to the
kernel Glauberman mismatch restricted to the matched inertia group. -/
theorem productAmbientGlaubermanQuotientMismatch_inflation_eq_kernelMismatch_gauge
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D]
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (c : FactorSet D ℂˣ)
    (hkernel :
      productGlaubermanKernelProjectiveMultiplicityFactorSet
          S C hcentral g
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) =
        c.comap rho)
    (hkill :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      inertiaNormalCopy
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightCharacter
            S C hcentral g theta) ≤
        (rho.comp
          (productAmbientGlaubermanRightInertiaToKernelStabilizer
            S C hcentral hgenerate g theta)).ker)
    (a :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta → ℂˣ)
    (htransport :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      productAmbientGlaubermanQuotientMismatchFactorSet
          S C hcentral hgenerate g theta =
        (c.comap
          (productAmbientGlaubermanRightOuterToKernelObstructionHom
            S C hcentral hgenerate g theta D rho hkill)).gauge a) :
    (productAmbientGlaubermanQuotientMismatchFactorSet
        S C hcentral hgenerate g theta).comap
          (productAmbientGlaubermanRightInertiaQuotientHom
            S C hcentral hgenerate g theta) =
      ((productGlaubermanKernelProjectiveMultiplicityFactorSet
          S C hcentral g
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta)).comap
        (productAmbientGlaubermanRightInertiaToKernelStabilizer
          S C hcentral hgenerate g theta)).gauge
            (fun b ↦
              a
                (productAmbientGlaubermanRightInertiaQuotientHom
                  S C hcentral hgenerate g theta b)) := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  rw [htransport, hkernel]
  apply FactorSet.ext
  intro b d
  simp only [FactorSet.gauge, FactorSet.comap, map_mul]
  have hb :=
    productAmbientGlaubermanRightOuterToKernelObstructionHom_mk
      S C hcentral hgenerate g theta D rho hkill b
  have hd :=
    productAmbientGlaubermanRightOuterToKernelObstructionHom_mk
      S C hcentral hgenerate g theta D rho hkill d
  exact
    congrArg
      (fun z : ℂˣ ↦
        (a
              (productAmbientGlaubermanRightInertiaQuotientHom
                S C hcentral hgenerate g theta b) *
            a
              (productAmbientGlaubermanRightInertiaQuotientHom
                S C hcentral hgenerate g theta d) /
          a
            (productAmbientGlaubermanRightInertiaQuotientHom
                S C hcentral hgenerate g theta b *
              productAmbientGlaubermanRightInertiaQuotientHom
                S C hcentral hgenerate g theta d)) * z)
      (congrArg₂ c.toFun hb hd)

/-- A finite-`q`-group factorization of the kernel mismatch, compatible
with the inertia quotient and with the final quotient factor up to gauge,
proves the intrinsic projective obstruction-class agreement. -/
theorem productAmbientGlaubermanProjectiveObstructionClassAgreement_of_kernelPGroupTransport
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D] [Finite D]
    (hD : IsPGroup q D)
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (c : FactorSet D ℂˣ)
    (_hkernel :
      productGlaubermanKernelProjectiveMultiplicityFactorSet
          S C hcentral g
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) =
        c.comap rho)
    (hkill :
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      inertiaNormalCopy
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightCharacter
            S C hcentral g theta) ≤
        (rho.comp
          (productAmbientGlaubermanRightInertiaToKernelStabilizer
            S C hcentral hgenerate g theta)).ker)
    (a :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta → ℂˣ)
    (htransport :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      productAmbientGlaubermanQuotientMismatchFactorSet
          S C hcentral hgenerate g theta =
        (c.comap
          (productAmbientGlaubermanRightOuterToKernelObstructionHom
            S C hcentral hgenerate g theta D rho hkill)).gauge a) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let Q :=
    productAmbientGlaubermanRightOuterQuotient
      S C hcentral hgenerate g theta
  let rhoBar :=
    productAmbientGlaubermanRightOuterToKernelObstructionHom
      S C hcentral hgenerate g theta D rho hkill
  obtain ⟨k, hk⟩ :=
    FactorSet.exists_pow_nsmul_comap_h2Class_eq_zero_of_isPGroup
      q hD c rhoBar
  have hcoprime :
      Nat.Coprime (q ^ k) (Nat.card Q) :=
    (productAmbientGlaubermanRightOuterQuotient_isPPrimeGroup
      S C hcentral hgenerate g theta).pow_left k
  have hpullZero :
      letI := trivialMulDistribMulAction Q ℂˣ
      (c.comap rhoBar).h2Class = 0 :=
    (c.comap rhoBar).h2Class_eq_zero_of_coprime
      (q ^ k) hcoprime hk
  have hmismatchZero :
      letI := trivialMulDistribMulAction Q ℂˣ
      (productAmbientGlaubermanQuotientMismatchFactorSet
        S C hcentral hgenerate g theta).h2Class = 0 := by
    rw [htransport]
    exact
      (FactorSet.h2Class_gauge
        (c.comap rhoBar) a).trans hpullZero
  have hfactorAgreement :
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta).QuotientFactorH2ClassAgreement
          (productAmbientGlaubermanRightAssociated
            S C hcentral hgenerate g theta)
          (productAmbientGlaubermanInertiaRestrictionGroupData
            S C hcentral hgenerate g theta) :=
    ProjectiveMultiplicityMismatch.quotientFactorH2ClassAgreement_of_mismatch_eq_zero
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanRightAssociated
        S C hcentral hgenerate g theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)
      hmismatchZero
  exact
    ((productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
      ).quotientFactorH2ClassAgreement_iff_projectiveObstructionClass
        (productAmbientGlaubermanRightAssociated
          S C hcentral hgenerate g theta)
        (productAmbientGlaubermanInertiaRestrictionGroupData
          S C hcentral hgenerate g theta)).mp hfactorAgreement

/-- The same obstruction agreement with the quotient-descent premise reduced
to its unique genuinely `q`-local part: the proposed kernel-obstruction
homomorphism must vanish on the Sylow direct factor of the right normal
copy.  Vanishing on the `q'` fixed-point factor is automatic. -/
theorem productAmbientGlaubermanProjectiveObstructionClassAgreement_of_kernelSylowTransport
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (D : Type) [Group D] [Finite D]
    (hD : IsPGroup q D)
    (rho :
      ProductGlaubermanKernelCharacterStabilizer
          S C hcentral
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) →* D)
    (c : FactorSet D ℂˣ)
    (hkernel :
      productGlaubermanKernelProjectiveMultiplicityFactorSet
          S C hcentral g
          (productAmbientGlaubermanSourceKernelCharacter
            S C hcentral theta) =
        c.comap rho)
    (hsylow :
      productAmbientGlaubermanRightNormalSylowObstructionHom
          S C hcentral hgenerate g theta D rho =
        1)
    (a :
      productAmbientGlaubermanRightOuterQuotient
        S C hcentral hgenerate g theta → ℂˣ)
    (htransport :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI : (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal S C hgenerate
      productAmbientGlaubermanQuotientMismatchFactorSet
          S C hcentral hgenerate g theta =
        (c.comap
          (productAmbientGlaubermanRightOuterToKernelObstructionHom
            S C hcentral hgenerate g theta D rho
            (productAmbientGlaubermanRightNormalCopy_le_kernel_of_sylow
              S C hcentral hgenerate g theta D hD rho hsylow))).gauge a) :
    ProductAmbientGlaubermanProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI : (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    productAmbientGlaubermanProjectiveObstructionClassAgreement_of_kernelPGroupTransport
      S C hcentral hgenerate g theta D hD rho c hkernel
      (productAmbientGlaubermanRightNormalCopy_le_kernel_of_sylow
        S C hcentral hgenerate g theta D hD rho hsylow)
      a htransport

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
