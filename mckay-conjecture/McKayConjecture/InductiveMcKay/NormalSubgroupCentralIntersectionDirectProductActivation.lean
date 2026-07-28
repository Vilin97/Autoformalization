/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveEquivalenceTransport
import McKayConjecture.Character.DirectProductActiveExtension
import McKayConjecture.InductiveMcKay.NormalPPrimeKernelGlauberman
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionComplement

/-!
# Direct-product activation on the local side of the central-intersection reduction

For the canonical normal `p′`-kernel inside `CP`, the Sylow normalizer is
the direct product of the kernel fixed points and the Sylow subgroup.
Consequently every prime-to-`p` fixed-point character extends by the
trivial Sylow character and belongs to an active local Clifford orbit.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open GroupTheory
open CentralIntersectionKernelAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

def localKernelDirectProductFirstFactorEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)) ≃*
      IrreducibleCharacter.directProductFirstFactor
        (G := internalPPrimeKernelFixedPoints
          (productSylow S C)
          (productPPrimeKernel S C hcentral))
        (H := internalNormalizerSylow
          (productSylow S C)) :=
  (localKernelFixedPointsEquiv S C hcentral).trans
    (IrreducibleCharacter.directProductFirstFactorEquiv
      (G := internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral))
      (H := internalNormalizerSylow
        (productSylow S C))).symm

theorem localKernelDirectProductFirstFactorEquiv_comm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    (normalizerProductEquiv S C hcentral).symm.toMonoidHom.comp
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))).subtype =
      (IrreducibleCharacter.directProductFirstFactor
        (G := internalPPrimeKernelFixedPoints
          (productSylow S C)
          (productPPrimeKernel S C hcentral))
        (H := internalNormalizerSylow
          (productSylow S C))).subtype.comp
        (localKernelDirectProductFirstFactorEquiv
          S C hcentral).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply (normalizerProductEquiv S C hcentral).injective
  change
    (normalizerProductEquiv S C hcentral)
        ((normalizerProductEquiv S C hcentral).symm
          (x :
            Subgroup.normalizer
              ((productSylow S C :
                Sylow q (product S C)) :
                Set (product S C)))) =
      (normalizerProductEquiv S C hcentral)
        (((IrreducibleCharacter.directProductFirstFactor).subtype)
          (localKernelDirectProductFirstFactorEquiv
            S C hcentral x))
  rw [(normalizerProductEquiv S C hcentral).apply_symm_apply]
  rw [show
    normalizerProductEquiv S C hcentral =
      pPrimeKernelFixedPointsProductEquiv
        (productSylow S C)
        (productPPrimeKernel S C hcentral)
        (productPPrimeKernel_isPPrimeGroup
          S C hcentral)
        (productPPrimeKernel_sup_productSylow_eq_top
          S C hcentral) from rfl]
  rw [pPrimeKernelFixedPointsProductEquiv_apply]
  change
    (x :
      Subgroup.normalizer
        ((productSylow S C :
          Sylow q (product S C)) :
          Set (product S C))) =
      ((localKernelFixedPointsEquiv S C hcentral x :
          internalPPrimeKernelFixedPoints
            (productSylow S C)
            (productPPrimeKernel S C hcentral)) :
        Subgroup.normalizer
          ((productSylow S C :
            Sylow q (product S C)) :
            Set (product S C))) *
      1
  rw [mul_one]
  rfl

/-- The first direct factor, relabelled as the ambient fixed-point
subgroup used by the Glauberman correspondence. -/
def directProductFirstFactorAmbientFixedPointsEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    IrreducibleCharacter.directProductFirstFactor
          (G := internalPPrimeKernelFixedPoints
            (productSylow S C)
            (productPPrimeKernel S C hcentral))
          (H := internalNormalizerSylow
            (productSylow S C)) ≃*
      coprimeFixedPoints
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) :=
  (localKernelDirectProductFirstFactorEquiv
      S C hcentral).symm.trans
    (localKernelAmbientFixedPointsEquiv
      S C hcentral)

/-- Every prime-to-`q` character of the fixed-point kernel is active in
the local Sylow normalizer. -/
theorem productPPrimeKernel_fixedPointCharacter_active
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q) :
    CliffordPartition.IsActivePPrimeCharacter
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      (IrreducibleCharacter.pPrimeComapEquiv q
        (localKernelAmbientFixedPointsEquiv
          S C hcentral) φ) := by
  let A :=
    internalPPrimeKernelFixedPoints
      (productSylow S C)
      (productPPrimeKernel S C hcentral)
  let B :=
    internalNormalizerSylow (productSylow S C)
  let M :=
    internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))
  let F :
      A × B ≃*
        localNormalizer
          (productSylow S C :
            Subgroup (product S C)) :=
    normalizerProductEquiv S C hcentral
  let eM :
      M ≃*
        IrreducibleCharacter.directProductFirstFactor
          (G := A) (H := B) :=
    localKernelDirectProductFirstFactorEquiv
      S C hcentral
  let eFC :
      IrreducibleCharacter.directProductFirstFactor
            (G := A) (H := B) ≃*
        coprimeFixedPoints
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)) :=
    directProductFirstFactorAmbientFixedPointsEquiv
      S C hcentral
  let θ :
      PPrimeIrreducibleCharacter
        (IrreducibleCharacter.directProductFirstFactor
          (G := A) (H := B)) q :=
    IrreducibleCharacter.pPrimeComapEquiv q eFC φ
  have hθactive :
      @CliffordPartition.IsActivePPrimeCharacter
        (A × B) _
        (IrreducibleCharacter.directProductFirstFactor
          (G := A) (H := B)) _ q θ :=
    IrreducibleCharacter.directProductFirstFactor_isActivePPrimeCharacter
      θ
  have htransport :
      @CliffordPartition.IsActivePPrimeCharacter
          (localNormalizer
            (productSylow S C :
              Subgroup (product S C))) _
          M _ q
          (IrreducibleCharacter.pPrimeComapEquiv
            q eM θ) := by
    apply
      (CliffordPartition.isActivePPrimeCharacter_comap_equiv_iff
        (IrreducibleCharacter.directProductFirstFactor
          (G := A) (H := B))
        M F.symm eM
        (localKernelDirectProductFirstFactorEquiv_comm
          S C hcentral)
        θ).mpr
    exact hθactive
  have heq :
      IrreducibleCharacter.pPrimeComapEquiv q eM θ =
        IrreducibleCharacter.pPrimeComapEquiv q
          (localKernelAmbientFixedPointsEquiv
            S C hcentral) φ := by
    apply Subtype.ext
    change
      (φ.1.comap
          ((localKernelDirectProductFirstFactorEquiv
              S C hcentral).symm.trans
            (localKernelAmbientFixedPointsEquiv
              S C hcentral))).comap
          (localKernelDirectProductFirstFactorEquiv
            S C hcentral) =
        φ.1.comap
          (localKernelAmbientFixedPointsEquiv
            S C hcentral)
    rw [IrreducibleCharacter.comap_trans]
    congr 1
  rw [← heq]
  exact htransport

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
