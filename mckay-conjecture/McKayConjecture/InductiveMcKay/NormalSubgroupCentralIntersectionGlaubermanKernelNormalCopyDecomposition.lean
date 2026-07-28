/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PGroupPPrimeHom
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanKernelInertiaTransport

/-!
# The right normal copy in Glauberman kernel coordinates

The normal subgroup in the matched right inertia triple is the local
Sylow normalizer.  Its canonical decomposition is

`C_K(P) × P`.

This file transports that decomposition into the inertia normal copy and
uses it to analyze the kernel condition required for quotient descent.  A
homomorphism from the `q'`-factor `C_K(P)` to a `q`-group is automatically
trivial.  Consequently the full normal copy is killed exactly when the
remaining Sylow-factor restriction is killed.  This identifies the first
genuinely `q`-local compatibility still required by the DGN transport.
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

noncomputable local instance productGlaubermanKernelNormalCopySourceFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

noncomputable local instance productGlaubermanKernelNormalCopyTargetFintype :
    Fintype (internalProductNormalizer S C) :=
  Fintype.ofFinite (internalProductNormalizer S C)

/-- The canonical normal copy in the matched right inertia group. -/
abbrev ProductAmbientGlaubermanRightNormalCopy
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :=
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  inertiaNormalCopy
    (internalProductNormalizer S C)
    (productAmbientGlaubermanRightKernelTransportCharacter
      S C hcentral g theta)

/-- Direct-product coordinates `C_K(P) × P` on the canonical right
inertia normal copy. -/
def productAmbientGlaubermanRightNormalCopyProductEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalPPrimeKernelFixedPoints
          (productSylow S C)
          (productPPrimeKernel S C hcentral) ×
        internalNormalizerSylow (productSylow S C) ≃*
      ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta := by
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    (normalizerProductEquiv S C hcentral).trans
      ((productNormalizerEquivInternal S C).trans
        (inertiaNormalCopyEquiv
          (internalProductNormalizer S C)
          (productAmbientGlaubermanRightKernelTransportCharacter
            S C hcentral g theta)).symm)

/-- Inclusion of the fixed-point direct factor into the right inertia
normal copy. -/
def productAmbientGlaubermanRightNormalCopyFixedPointHom
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral) →*
      ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta :=
  (productAmbientGlaubermanRightNormalCopyProductEquiv
      S C hcentral hgenerate g theta).toMonoidHom.comp
    (MonoidHom.inl
      (internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral))
      (internalNormalizerSylow (productSylow S C)))

/-- Inclusion of the Sylow direct factor into the right inertia normal
copy. -/
def productAmbientGlaubermanRightNormalCopySylowHom
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    internalNormalizerSylow (productSylow S C) →*
      ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta :=
  (productAmbientGlaubermanRightNormalCopyProductEquiv
      S C hcentral hgenerate g theta).toMonoidHom.comp
    (MonoidHom.inr
      (internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral))
      (internalNormalizerSylow (productSylow S C)))

/-- The fixed-point-factor restriction of a proposed `q`-group
obstruction homomorphism. -/
def productAmbientGlaubermanRightNormalFixedPointObstructionHom
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
            S C hcentral theta) →* D) :
    internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral) →* D :=
  (rho.comp
      (productAmbientGlaubermanRightInertiaToKernelStabilizer
        S C hcentral hgenerate g theta)).comp
    ((ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta).subtype.comp
      (productAmbientGlaubermanRightNormalCopyFixedPointHom
        S C hcentral hgenerate g theta))

/-- The Sylow-factor restriction of a proposed `q`-group obstruction
homomorphism. -/
def productAmbientGlaubermanRightNormalSylowObstructionHom
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
            S C hcentral theta) →* D) :
    internalNormalizerSylow (productSylow S C) →* D :=
  (rho.comp
      (productAmbientGlaubermanRightInertiaToKernelStabilizer
        S C hcentral hgenerate g theta)).comp
    ((ProductAmbientGlaubermanRightNormalCopy
        S C hcentral hgenerate g theta).subtype.comp
      (productAmbientGlaubermanRightNormalCopySylowHom
        S C hcentral hgenerate g theta))

/-- The fixed-point direct factor is a `q'`-group. -/
theorem productGlaubermanInternalKernelFixedPoints_isPPrimeGroup
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    IsPPrimeGroup q
      (internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) := by
  let F :=
    productPPrimeKernelFixedPoints S C hcentral
  have hF : IsPPrimeGroup q F :=
    (productPPrimeKernel_isPPrimeGroup
      S C hcentral).coprime_dvd_right
        (Subgroup.card_dvd_of_le inf_le_left)
  let e :
      internalPPrimeKernelFixedPoints
            (productSylow S C)
            (productPPrimeKernel S C hcentral) ≃*
        F :=
    Subgroup.subgroupOfEquivOfLe
      (show
        productPPrimeKernel S C hcentral ⊓
            Subgroup.centralizer
              (productSylow S C :
                Set (product S C)) ≤
          Subgroup.normalizer
            (productSylow S C :
              Set (product S C)) from
        inf_le_right.trans
          (Subgroup.centralizer_le_normalizer
            (productSylow S C :
              Set (product S C))))
  exact hF.of_equiv e.symm

/-- For a `q`-group target, killing the full right normal copy is
equivalent to killing only its Sylow direct factor.  The fixed-point
factor is killed automatically by coprime order. -/
theorem productAmbientGlaubermanRightNormalCopy_le_kernel_iff_sylow
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
            S C hcentral theta) →* D) :
    ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta ≤
        (rho.comp
          (productAmbientGlaubermanRightInertiaToKernelStabilizer
            S C hcentral hgenerate g theta)).ker ↔
      productAmbientGlaubermanRightNormalSylowObstructionHom
          S C hcentral hgenerate g theta D rho =
        1 := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let N :=
    ProductAmbientGlaubermanRightNormalCopy
      S C hcentral hgenerate g theta
  let e :=
    productAmbientGlaubermanRightNormalCopyProductEquiv
      S C hcentral hgenerate g theta
  let fixedHom :=
    productAmbientGlaubermanRightNormalCopyFixedPointHom
      S C hcentral hgenerate g theta
  let sylowHom :=
    productAmbientGlaubermanRightNormalCopySylowHom
      S C hcentral hgenerate g theta
  let f :=
    rho.comp
      (productAmbientGlaubermanRightInertiaToKernelStabilizer
        S C hcentral hgenerate g theta)
  have hfixed :
      productAmbientGlaubermanRightNormalFixedPointObstructionHom
          S C hcentral hgenerate g theta D rho =
        1 :=
    McKayConjecture.GroupTheory.MonoidHom.eq_one_of_isPPrimeGroup_of_isPGroup
      (productAmbientGlaubermanRightNormalFixedPointObstructionHom
        S C hcentral hgenerate g theta D rho)
      (productGlaubermanInternalKernelFixedPoints_isPPrimeGroup
        S C hcentral)
      hD
  constructor
  · intro h
    ext b
    change f (N.subtype (sylowHom b)) = 1
    exact
      MonoidHom.mem_ker.mp
        (h (sylowHom b).property)
  · intro hsylow x hx
    let n : N := ⟨x, hx⟩
    let y := e.symm n
    have hn :
        n = fixedHom y.1 * sylowHom y.2 := by
      calc
        n = e y := (e.apply_symm_apply n).symm
        _ = e ((y.1, 1) * (1, y.2)) := by simp
        _ = e (y.1, 1) * e (1, y.2) := by
          rw [map_mul]
        _ = fixedHom y.1 * sylowHom y.2 := rfl
    have hfixedApply :
        f (N.subtype (fixedHom y.1)) = 1 := by
      have h :=
        congrArg
          (fun z :
            internalPPrimeKernelFixedPoints
                (productSylow S C)
                (productPPrimeKernel S C hcentral) →* D ↦
            z y.1)
          hfixed
      exact h
    have hsylowApply :
        f (N.subtype (sylowHom y.2)) = 1 := by
      have h :=
        congrArg
          (fun z :
            internalNormalizerSylow
                (productSylow S C) →* D ↦
            z y.2)
          hsylow
      exact h
    apply MonoidHom.mem_ker.mpr
    change f (N.subtype n) = 1
    rw [hn, map_mul, map_mul, hfixedApply, hsylowApply, one_mul]

/-- For a `q`-group target, triviality on the Sylow direct factor is the
only premise needed to kill the full right inertia normal copy. -/
theorem productAmbientGlaubermanRightNormalCopy_le_kernel_of_sylow
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
    (hsylow :
      productAmbientGlaubermanRightNormalSylowObstructionHom
          S C hcentral hgenerate g theta D rho =
        1) :
    ProductAmbientGlaubermanRightNormalCopy
          S C hcentral hgenerate g theta ≤
        (rho.comp
          (productAmbientGlaubermanRightInertiaToKernelStabilizer
            S C hcentral hgenerate g theta)).ker :=
  (productAmbientGlaubermanRightNormalCopy_le_kernel_iff_sylow
    S C hcentral hgenerate g theta D hD rho).mpr hsylow

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
