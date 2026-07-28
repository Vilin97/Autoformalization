/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordActiveEquivalenceTransport
import McKayConjecture.Character.DeterminantEquivalenceTransport
import McKayConjecture.Character.DeterminantRootTwist
import McKayConjecture.Character.GallagherCovariantBaseChange
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerCharacterTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerQuotientTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizedFibre

/-!
# Normalizer transport of determinant-normalized extensions

Ambient-normalizer conjugation preserves the canonical source group `CP`,
its normal `q'`-kernel, its Sylow subgroup, and the local normalizer.  The
chosen source extensions need not themselves be equivariant.  This file
measures their discrepancy by the canonical Gallagher base-change
parameter, then follows that parameter through determinant-root
normalization and the source-to-local quotient equivalence.

All equivalences below point in the pullback direction.  Thus conjugation by
`h` is represented by `productConjugationHom S C h`, and a transported
character is its `comap` along that automorphism.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordCorrespondence
open CliffordPartition
open CentralIntersectionKernelAssembly
open GroupTheory
open NormalPPrimeKernelGlauberman

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance normalizedExtensionTransportProductFintype :
    Fintype (product S C) :=
  Fintype.ofFinite _

noncomputable local instance normalizedExtensionTransportLocalFintype :
    Fintype
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :=
  Fintype.ofFinite _

/-- Pullback along forward conjugation is the character-action convention
for the inverse ambient-normalizer element. -/
@[simp]
theorem productConjugationHom_inv_symm
    (h : ambientNormalizer S) :
    (productConjugationHom S C h⁻¹).symm =
      productConjugationHom S C h := by
  rw [map_inv]
  rfl

/-- Direct inverse form on the source group. -/
@[simp]
theorem productConjugationHom_inv
    (h : ambientNormalizer S) :
    productConjugationHom S C h⁻¹ =
      (productConjugationHom S C h).symm := by
  rw [map_inv]
  rfl

/-- The same inverse-orientation identity on the characteristic source
kernel. -/
@[simp]
theorem productPPrimeKernelConjugationHom_inv_symm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productPPrimeKernelConjugationHom
        S C hcentral h⁻¹).symm =
      productPPrimeKernelConjugationHom
        S C hcentral h := by
  rw [map_inv]
  rfl

/-- Inverse-action bridge on the fixed-point subgroup. -/
@[simp]
theorem productPPrimeKernelFixedPointsConjugation_inv_symm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productPPrimeKernelFixedPointsConjugation
        S C hcentral h⁻¹).symm =
      productPPrimeKernelFixedPointsConjugation
        S C hcentral h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change
    (productConjugationHom S C h⁻¹).symm
        (x : product S C) =
      productConjugationHom S C h
        (x : product S C)
  rw [productConjugationHom_inv_symm]

/-- Inverse-action bridge on the local normalizer. -/
@[simp]
theorem productLocalNormalizerConjugation_inv_symm
    (h : ambientNormalizer S) :
    (productLocalNormalizerConjugation
        S C h⁻¹).symm =
      productLocalNormalizerConjugation
        S C h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change
    (productConjugationHom S C h⁻¹).symm
        (x : product S C) =
      productConjugationHom S C h
        (x : product S C)
  rw [productConjugationHom_inv_symm]

/-- Direct inverse form of the preceding local-normalizer bridge. -/
@[simp]
theorem productLocalNormalizerConjugation_inv
    (h : ambientNormalizer S) :
    productLocalNormalizerConjugation S C h⁻¹ =
      (productLocalNormalizerConjugation S C h).symm := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change
    productConjugationHom S C h⁻¹
        (x : product S C) =
      (productConjugationHom S C h).symm
        (x : product S C)
  rw [map_inv]
  rfl

/-- Inverse-action bridge on the internal local kernel. -/
@[simp]
theorem productLocalKernelConjugation_inv_symm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productLocalKernelConjugation
        S C hcentral h⁻¹).symm =
      productLocalKernelConjugation
        S C hcentral h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change
    (productLocalNormalizerConjugation
        S C h⁻¹).symm
        (x :
          localNormalizer
            (productSylow S C :
              Subgroup (product S C))) =
      productLocalNormalizerConjugation
        S C h
        (x :
          localNormalizer
            (productSylow S C :
              Subgroup (product S C)))
  rw [productLocalNormalizerConjugation_inv_symm]

/-- Inverse-action bridge on the restricted Sylow subgroup. -/
@[simp]
theorem productSylowConjugation_inv_symm
    (h : ambientNormalizer S) :
    (productSylowConjugation S C h⁻¹).symm =
      productSylowConjugation S C h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change
    (productConjugationHom S C h⁻¹).symm
        (x : product S C) =
      productConjugationHom S C h
        (x : product S C)
  rw [productConjugationHom_inv_symm]

/-- Ambient-normalizer conjugation transports the exact active-orbit
index of the canonical source kernel. -/
def productActiveOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    ActiveOrbit
        (productPPrimeKernel S C hcentral) q ≃
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q :=
  activeOrbitComapEquiv
    (productPPrimeKernel S C hcentral)
    (productPPrimeKernel S C hcentral)
    q
    (productConjugationHom S C h)
    (productPPrimeKernelConjugationHom
      S C hcentral h)
    (productPPrimeKernelConjugation_subtype_commutes
      S C hcentral h)

/-- Bridge from the forward-comap convention used for equivalence
naturality to the inverse-action convention used by the normalizer-action
API. -/
theorem productActiveOrbitComap_eq_sourceConjugation_inv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    productActiveOrbitComap S C hcentral h =
      productSourceActiveOrbitConjugation
        S C hcentral h⁻¹ := by
  apply Equiv.ext
  intro r
  apply Subtype.ext
  change
    orbitSpaceComapEquiv
        (productPPrimeKernel S C hcentral)
        (productPPrimeKernel S C hcentral)
        (productConjugationHom S C h)
        (productPPrimeKernelConjugationHom
          S C hcentral h)
        (productPPrimeKernelConjugation_subtype_commutes
          S C hcentral h) r.1 =
      orbitSpaceComapEquiv
        (productPPrimeKernel S C hcentral)
        (productPPrimeKernel S C hcentral)
        (productConjugationHom S C h⁻¹).symm
        (productPPrimeKernelConjugationHom
          S C hcentral h⁻¹).symm
        (productPPrimeKernelConjugation_symm_subtype_commutes
          S C hcentral h⁻¹) r.1
  refine Quotient.inductionOn' r.1 ?_
  intro θ
  rw [orbitSpaceComapEquiv_mk,
    orbitSpaceComapEquiv_mk]
  rw [productPPrimeKernelConjugationHom_inv_symm]

/-- Pointwise bridge in the exact DGN normalizer-action orientation. -/
@[simp]
theorem productActiveOrbitComap_inv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    productActiveOrbitComap S C hcentral h⁻¹ r =
      productSourceActiveOrbitConjugation
        S C hcentral h r := by
  rw [productActiveOrbitComap_eq_sourceConjugation_inv]
  simp

/-- Although active-orbit transport initially identifies only conjugacy
orbits, the selected source extension forces its kernel constituent to be
invariant.  Hence the chosen representative of the transported active orbit
is literally the pullback of the old chosen representative. -/
theorem productActiveOrbitComap_pPrimeOut
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    ((productActiveOrbitComap
        S C hcentral h r).pPrimeOut
      (productPPrimeKernel S C hcentral)) =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productPPrimeKernelConjugationHom
          S C hcentral h)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)) := by
  let K :=
    productPPrimeKernel S C hcentral
  let eG :=
    productConjugationHom S C h
  let eK :=
    productPPrimeKernelConjugationHom
      S C hcentral h
  let r' :=
    productActiveOrbitComap S C hcentral h r
  let θ :=
    (r.pPrimeOut K).1
  let ψ :=
    (productSourcePPrimeExtension
      S C hcentral r).1
  have hψ :
      IrreducibleCharacter.IsExtensionAlong
        K.subtype θ ψ :=
    productSourcePPrimeExtension_isExtension
      S C hcentral r
  have htransport :
      IrreducibleCharacter.IsExtensionAlong
        K.subtype (θ.comap eK) (ψ.comap eG) :=
    hψ.comap_equiv eG eK
      (productPPrimeKernelConjugation_subtype_commutes
        S C hcentral h)
  have horbit :=
    orbitSpaceComapEquiv_out_eq
      K K eG eK
      (productPPrimeKernelConjugation_subtype_commutes
        S C hcentral h)
      r.1
  obtain ⟨g, hg⟩ := Quotient.exact horbit
  change g • (θ.comap eK) = r'.1.out at hg
  have hfixed := htransport.conjBy_eq g
  change g • (θ.comap eK) = θ.comap eK at hfixed
  apply Subtype.ext
  change r'.1.out = θ.comap eK
  exact hg.symm.trans hfixed

/-- The invariant kernel character selected at the transported orbit is
the normalizer-action transport of the old invariant character, in the
inverse-action convention. -/
theorem productSourceInvariantCharacter_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    productSourceInvariantCharacter
        S C hcentral a
        (productActiveOrbitComap
          S C hcentral h r) =
      productPInvariantCharacterConjugation
        S C hcentral h⁻¹
        (productSourceInvariantCharacter
          S C hcentral a r) := by
  apply Subtype.ext
  change
    (productActiveOrbitComap
        S C hcentral h r).pPrimeOut
          (productPPrimeKernel S C hcentral) =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productPPrimeKernelConjugationHom
          S C hcentral h⁻¹).symm
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral))
  rw [productActiveOrbitComap_pPrimeOut,
    productPPrimeKernelConjugationHom_inv_symm]

/-- The Glauberman fixed-point factor is covariant for forward pullback of
the active orbit. -/
theorem productGlaubermanCharacter_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    g.characterEquiv
        (productSourceInvariantCharacter
          S C hcentral a
          (productActiveOrbitComap
            S C hcentral h r)) =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral h)
        (g.characterEquiv
          (productSourceInvariantCharacter
            S C hcentral a r)) := by
  rw [productSourceInvariantCharacter_activeOrbitComap]
  rw [productGlaubermanCharacterEquiv_conjugation]
  change
    IrreducibleCharacter.pPrimeComapEquiv q
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral h⁻¹).symm
        (g.characterEquiv
          (productSourceInvariantCharacter
            S C hcentral a r)) =
      _
  rw [productPPrimeKernelFixedPointsConjugation_inv_symm]

/-- The local-kernel representative selected at the matched transported
orbit is the literal pullback of the old selected representative. -/
theorem productGlaubermanTargetPPrimeOut_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    ((productGlaubermanActiveOrbitEquiv
        S C hcentral g a
        (productActiveOrbitComap
          S C hcentral h r)).pPrimeOut
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))) =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productLocalKernelConjugation
          S C hcentral h)
        ((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))) := by
  rw [productGlaubermanTargetPPrimeOut_eq,
    productGlaubermanTargetPPrimeOut_eq,
    productGlaubermanCharacter_activeOrbitComap]
  have htransport :=
    localKernelAmbientFixedPointsPPrimeComap_conjugation
      S C hcentral h⁻¹
      (g.characterEquiv
        (productSourceInvariantCharacter
          S C hcentral a r))
  simpa only [
    productPPrimeKernelFixedPointsConjugation_smul_pPrime_eq_comap_symm,
    productLocalKernelConjugation_smul_pPrime_eq_comap_symm,
    productPPrimeKernelFixedPointsConjugation_inv_symm,
    productLocalKernelConjugation_inv_symm] using
      htransport

/-- The literal pullback of the selected source extension extends the
chosen representative of the transported active orbit. -/
theorem productSourcePPrimeExtension_comap_isExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter.IsExtensionAlong
      (productPPrimeKernel S C hcentral).subtype
      ((productActiveOrbitComap
          S C hcentral h r).pPrimeOut
        (productPPrimeKernel S C hcentral)).1
      ((productSourcePPrimeExtension
          S C hcentral r).1.comap
        (productConjugationHom S C h)) := by
  rw [productActiveOrbitComap_pPrimeOut
    S C hcentral h r]
  exact
    (productSourcePPrimeExtension_isExtension
      S C hcentral r).comap_equiv
        (productConjugationHom S C h)
        (productPPrimeKernelConjugationHom
          S C hcentral h)
        (productPPrimeKernelConjugation_subtype_commutes
          S C hcentral h)

/-- Literal-comap form of the preceding extension statement. -/
theorem productSourcePPrimeExtension_comap_isExtension_literal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter.IsExtensionAlong
      (productPPrimeKernel S C hcentral).subtype
      ((r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1.comap
        (productPPrimeKernelConjugationHom
          S C hcentral h))
      ((productSourcePPrimeExtension
          S C hcentral r).1.comap
        (productConjugationHom S C h)) :=
  (productSourcePPrimeExtension_isExtension
    S C hcentral r).comap_equiv
      (productConjugationHom S C h)
      (productPPrimeKernelConjugationHom
        S C hcentral h)
      (productPPrimeKernelConjugation_subtype_commutes
        S C hcentral h)

/-- The independently selected extension at the transported orbit also
extends the literal pullback of the old kernel representative. -/
theorem productSourcePPrimeExtension_transported_isExtension_literal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter.IsExtensionAlong
      (productPPrimeKernel S C hcentral).subtype
      ((r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1.comap
        (productPPrimeKernelConjugationHom
          S C hcentral h))
      (productSourcePPrimeExtension
        S C hcentral
        (productActiveOrbitComap
          S C hcentral h r)).1 := by
  have hout :
      ((productActiveOrbitComap
          S C hcentral h r).pPrimeOut
        (productPPrimeKernel S C hcentral)).1 =
        ((r.pPrimeOut
            (productPPrimeKernel S C hcentral)).1.comap
          (productPPrimeKernelConjugationHom
            S C hcentral h)) :=
    congrArg Subtype.val
      (productActiveOrbitComap_pPrimeOut
        S C hcentral h r)
  rw [← hout]
  exact
    productSourcePPrimeExtension_isExtension
      S C hcentral
      (productActiveOrbitComap S C hcentral h r)

/-- The canonical source-quotient parameter comparing the literal pullback
of the selected source extension with the independently selected extension
at the transported active orbit. -/
def productSourceExtensionTransportParameter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    ((product S C) ⧸
      productPPrimeKernel S C hcentral) →* ℂˣ :=
  IrreducibleCharacter.gallagherTransportBaseChangeParameter
    (productConjugationHom S C h)
    (productPPrimeKernelConjugationHom
      S C hcentral h)
    (productPPrimeKernelConjugation_subtype_commutes
      S C hcentral h)
    (productSourcePPrimeExtension_isExtension
      S C hcentral r)
    (productSourcePPrimeExtension_transported_isExtension_literal
      S C hcentral h r)

/-- The target selected source extension is the canonical quotient-linear
twist of the literal pullback.  This fixes the orientation of the
base-change parameter. -/
theorem productSourceExtensionTransportParameter_spec
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (productSourcePPrimeExtension
        S C hcentral
        (productActiveOrbitComap
          S C hcentral h r)).1 =
      IrreducibleCharacter.twist
        (IrreducibleCharacter.inflateLinearCharacter
          (productPPrimeKernel S C hcentral)
          (productSourceExtensionTransportParameter
            S C hcentral h r))
        ((productSourcePPrimeExtension
            S C hcentral r).1.comap
          (productConjugationHom S C h)) := by
  exact
    IrreducibleCharacter.gallagherBaseChangeParameter_spec
      (productSourcePPrimeExtension_comap_isExtension_literal
        S C hcentral h r)
      (productSourcePPrimeExtension_transported_isExtension_literal
        S C hcentral h r)

/-- In the reverse orientation, the literal pullback is the inverse
base-change twist of the target selected extension. -/
theorem productSourceExtension_comap_eq_inverse_twist
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (productSourcePPrimeExtension
        S C hcentral r).1.comap
        (productConjugationHom S C h) =
      IrreducibleCharacter.twist
        (IrreducibleCharacter.inflateLinearCharacter
          (productPPrimeKernel S C hcentral)
          (productSourceExtensionTransportParameter
            S C hcentral h r)⁻¹)
        (productSourcePPrimeExtension
          S C hcentral
          (productActiveOrbitComap
            S C hcentral h r)).1 := by
  rw [productSourceExtensionTransportParameter_spec
    S C hcentral h r]
  apply IrreducibleCharacter.ext
  funext x
  simp [IrreducibleCharacter.inflateLinearCharacter]

/-- The source transport parameter is uniquely characterized by the
preceding twist identity. -/
theorem eq_productSourceExtensionTransportParameter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ)
    (hlam :
      (productSourcePPrimeExtension
          S C hcentral
          (productActiveOrbitComap
            S C hcentral h r)).1 =
        IrreducibleCharacter.twist
          (IrreducibleCharacter.inflateLinearCharacter
            (productPPrimeKernel S C hcentral) lam)
          ((productSourcePPrimeExtension
              S C hcentral r).1.comap
            (productConjugationHom S C h))) :
    lam =
      productSourceExtensionTransportParameter
        S C hcentral h r :=
  IrreducibleCharacter.eq_gallagherBaseChangeParameter
    (productSourcePPrimeExtension_comap_isExtension_literal
      S C hcentral h r)
    (productSourcePPrimeExtension_transported_isExtension_literal
      S C hcentral h r)
    lam hlam

/-- Restriction to the Sylow complement of the inflated canonical source
base-change parameter. -/
def productSourceSylowTransportCorrection
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (productSylow S C :
        Subgroup (product S C)) →* ℂˣ :=
  (IrreducibleCharacter.inflateLinearCharacter
    (productPPrimeKernel S C hcentral)
    (productSourceExtensionTransportParameter
      S C hcentral h r)).comp
      (productSylow S C :
        Subgroup (product S C)).subtype

/-- Determinant-root normalization turns source-extension base change into
the same multiplicative correction on the Sylow factor. -/
theorem productSourceDeterminantRoot_transport
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    productSourceDeterminantRoot
        S C hcentral
        (productActiveOrbitComap
          S C hcentral h r) =
      productSourceSylowTransportCorrection
          S C hcentral h r *
        (productSourceDeterminantRoot
          S C hcentral r).comp
            (productSylowConjugation
              S C h).toMonoidHom := by
  let ψ :=
    (productSourcePPrimeExtension
      S C hcentral r).1
  let ψ' :=
    (productSourcePPrimeExtension
      S C hcentral
      (productActiveOrbitComap
        S C hcentral h r)).1
  let e :=
    productConjugationHom S C h
  let P : Subgroup (product S C) :=
    productSylow S C
  let lam :=
    IrreducibleCharacter.inflateLinearCharacter
      (productPPrimeKernel S C hcentral)
      (productSourceExtensionTransportParameter
        S C hcentral h r)
  have hbase :
      ψ' = IrreducibleCharacter.twist lam (ψ.comap e) :=
    productSourceExtensionTransportParameter_spec
      S C hcentral h r
  let hp :=
    productSylow_card_coprime_sourceExtension_degree
      S C hcentral r
  let hp' :=
    productSylow_card_coprime_sourceExtension_degree
      S C hcentral
      (productActiveOrbitComap
        S C hcentral h r)
  have hpTransported :
      (Nat.card P).Coprime (ψ.comap e).degree := by
    simpa only [IrreducibleCharacter.comap_degree] using hp
  let hpTwist :
      (Nat.card P).Coprime
        (IrreducibleCharacter.twist
          lam (ψ.comap e)).degree := by
    simpa only [IrreducibleCharacter.twist_degree] using
      hpTransported
  have hrootBase :
      IrreducibleCharacter.determinantRootParameter
          ψ' P.subtype hp' =
      IrreducibleCharacter.determinantRootParameter
          (IrreducibleCharacter.twist
            lam (ψ.comap e))
          P.subtype hpTwist := by
    apply MonoidHom.ext
    intro x
    change
      (IrreducibleCharacter.determinantParameter
        ψ' (P.subtype x)) ^
          (Nat.card P).gcdB ψ'.degree =
        (IrreducibleCharacter.determinantParameter
          (IrreducibleCharacter.twist
            lam (ψ.comap e))
          (P.subtype x)) ^
            (Nat.card P).gcdB
              (IrreducibleCharacter.twist
                lam (ψ.comap e)).degree
    rw [hbase]
  change
    IrreducibleCharacter.determinantRootParameter
        ψ' P.subtype hp' =
      (lam.comp P.subtype) *
        (IrreducibleCharacter.determinantRootParameter
          ψ P.subtype hp).comp
            (productSylowConjugation
              S C h).toMonoidHom
  calc
    IrreducibleCharacter.determinantRootParameter
        ψ' P.subtype hp' =
      IrreducibleCharacter.determinantRootParameter
        (IrreducibleCharacter.twist
          lam (ψ.comap e))
        P.subtype hpTwist :=
      hrootBase
    _ =
        (lam.comp P.subtype) *
          IrreducibleCharacter.determinantRootParameter
            (ψ.comap e) P.subtype hpTransported :=
      IrreducibleCharacter.determinantRootParameter_twist
        lam (ψ.comap e) P.subtype hpTransported
    _ =
        (lam.comp P.subtype) *
          (IrreducibleCharacter.determinantRootParameter
            ψ P.subtype hp).comp
              (productSylowConjugation
                S C h).toMonoidHom := by
      have htransportRoot :=
        IrreducibleCharacter.determinantRootParameter_comap_invariantSubgroupAutomorphism
          e P
          (productSylow_map_productConjugation S C h)
          ψ hp
      have htransportRoot' :
          IrreducibleCharacter.determinantRootParameter
              (ψ.comap e) P.subtype hpTransported =
            (IrreducibleCharacter.determinantRootParameter
              ψ P.subtype hp).comp
                (productSylowConjugation
                  S C h).toMonoidHom := by
        simpa only [productSylowConjugation] using
          htransportRoot
      exact congrArg (fun z => (lam.comp P.subtype) * z)
        htransportRoot'

/-- The source base-change parameter, transported across the canonical
identification between the local and source quotients. -/
def productLocalExtensionTransportParameter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) →* ℂˣ :=
  productLinearQuotientEquiv S C hcentral
    (productSourceExtensionTransportParameter
      S C hcentral h r)

/-- Inflating the transported local parameter and evaluating at a local
element is literally evaluation of the source parameter on the class of
the same ambient element. -/
theorem productLocalExtensionTransportParameter_inflate_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (x :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :
    IrreducibleCharacter.inflateLinearCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (productLocalExtensionTransportParameter
          S C hcentral h r) x =
      productSourceExtensionTransportParameter
        S C hcentral h r
        (QuotientGroup.mk'
          (productPPrimeKernel S C hcentral)
          (x : product S C)) := by
  change
    productSourceExtensionTransportParameter
        S C hcentral h r
        (productLocalSourceQuotientEquiv
          S C hcentral
          (QuotientGroup.mk'
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C)))
            x)) =
      productSourceExtensionTransportParameter
        S C hcentral h r
        (QuotientGroup.mk'
          (productPPrimeKernel S C hcentral)
          (x : product S C))
  rw [productLocalSourceQuotientEquiv_mk]

/-- The fixed-point direct factor of the local product decomposition is
preserved by local conjugation. -/
theorem productDirectFixedFactor_map_localConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (GroupTheory.internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)).map
        (productLocalNormalizerConjugation
          S C h).toMonoidHom =
      GroupTheory.internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral) := by
  rw [←
    internalKernelNormalizer_productPPrimeKernel_eq_fixedPoints
      S C hcentral]
  exact
    productLocalKernel_map_productLocalNormalizerConjugation
      S C hcentral h

/-- Conjugation restricted to the fixed-point direct factor. -/
def productDirectFixedFactorConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    MulAut
      (GroupTheory.internalPPrimeKernelFixedPoints
        (productSylow S C)
        (productPPrimeKernel S C hcentral)) :=
  invariantSubgroupAutomorphism
    (productLocalNormalizerConjugation S C h)
    (GroupTheory.internalPPrimeKernelFixedPoints
      (productSylow S C)
      (productPPrimeKernel S C hcentral))
    (productDirectFixedFactor_map_localConjugation
      S C hcentral h)

/-- The Sylow direct factor of the local product decomposition is
preserved by local conjugation. -/
theorem productDirectSylowFactor_map_localConjugation
    (h : ambientNormalizer S) :
    (GroupTheory.internalNormalizerSylow
        (productSylow S C)).map
        (productLocalNormalizerConjugation
          S C h).toMonoidHom =
      GroupTheory.internalNormalizerSylow
        (productSylow S C) := by
  let P : Subgroup (product S C) :=
    productSylow S C
  let H := localNormalizer P
  let e := productConjugationHom S C h
  let eH := productLocalNormalizerConjugation S C h
  ext x
  rw [Subgroup.mem_map_equiv]
  change
    (((eH.symm x : H) : product S C) ∈ P) ↔
      (((x : H) : product S C) ∈ P)
  rw [productLocalNormalizerConjugation_symm_apply_coe]
  have hmem :
      (((x : H) : product S C) ∈
          P.map e.toMonoidHom) ↔
        e.symm ((x : H) : product S C) ∈ P :=
    Subgroup.mem_map_equiv
  rw [productSylow_map_productConjugation
    S C h] at hmem
  exact hmem.symm

/-- Conjugation restricted to the Sylow direct factor. -/
def productDirectSylowFactorConjugation
    (h : ambientNormalizer S) :
    MulAut
      (GroupTheory.internalNormalizerSylow
        (productSylow S C)) :=
  invariantSubgroupAutomorphism
    (productLocalNormalizerConjugation S C h)
    (GroupTheory.internalNormalizerSylow
      (productSylow S C))
    (productDirectSylowFactor_map_localConjugation
      S C h)

/-- Local conjugation acts diagonally in the canonical fixed-point-times-
Sylow direct-product coordinates. -/
theorem normalizerProductEquiv_conjugation_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productLocalNormalizerConjugation
        S C h).toMonoidHom.comp
        (normalizerProductEquiv
          S C hcentral).toMonoidHom =
      (normalizerProductEquiv
        S C hcentral).toMonoidHom.comp
        (MulEquiv.prodCongr
          (productDirectFixedFactorConjugation
            S C hcentral h)
          (productDirectSylowFactorConjugation
            S C h)).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change
    productConjugationHom S C h
        ((x.1 :
          localNormalizer
            (productSylow S C :
              Subgroup (product S C))) *
          (x.2 :
            localNormalizer
              (productSylow S C :
                Subgroup (product S C)))) =
      ((productConjugationHom S C h
          (x.1 :
            localNormalizer
              (productSylow S C :
                Subgroup (product S C))) :
          product S C) *
        (productConjugationHom S C h
          (x.2 :
            localNormalizer
              (productSylow S C :
                Subgroup (product S C))) :
          product S C))
  exact map_mul _ _ _

/-- The first direct-factor character in the normalized local extension is
the pullback of the old factor character. -/
theorem productGlaubermanDirectFactorCharacter_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (productGlaubermanDirectFactorCharacter
        S C hcentral g a
        (productActiveOrbitComap
          S C hcentral h r)).1 =
      IrreducibleCharacter.directProductFirstFactorCharacterComap
        (B' :=
          GroupTheory.internalNormalizerSylow
            (productSylow S C))
        (productDirectFixedFactorConjugation
          S C hcentral h)
        (productGlaubermanDirectFactorCharacter
          S C hcentral g a r).1 := by
  apply IrreducibleCharacter.ext
  funext x
  change
    (g.characterEquiv
      (productSourceInvariantCharacter
        S C hcentral a
        (productActiveOrbitComap
          S C hcentral h r))).1.values
        (directProductFirstFactorAmbientFixedPointsEquiv
          S C hcentral x) =
      _
  rw [productGlaubermanCharacter_activeOrbitComap]
  rfl

/-- The source correction relabelled onto the Sylow direct factor of the
local normalizer. -/
def productLocalSylowTransportCorrection
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    GroupTheory.internalNormalizerSylow
        (productSylow S C) →* ℂˣ :=
  (productSourceSylowTransportCorrection
    S C hcentral h r).comp
      (Subgroup.subgroupOfEquivOfLe
        (show
          (productSylow S C :
              Subgroup (product S C)) ≤
            localNormalizer
              (productSylow S C :
                Subgroup (product S C)) from
          Subgroup.le_normalizer)).toMonoidHom

/-- The Sylow parameter of the transported normalized extension is
corrected by the relabelled source Gallagher parameter. -/
theorem productLocalSylowLinearParameter_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    productLocalSylowLinearParameter
        S C hcentral
        (productActiveOrbitComap
          S C hcentral h r) =
      productLocalSylowTransportCorrection
          S C hcentral h r *
        (productLocalSylowLinearParameter
          S C hcentral r).comp
            (productDirectSylowFactorConjugation
              S C h).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  have hroot :=
    DFunLike.congr_fun
      (productSourceDeterminantRoot_transport
        S C hcentral h r)
      (Subgroup.subgroupOfEquivOfLe
        (show
          (productSylow S C :
              Subgroup (product S C)) ≤
            localNormalizer
              (productSylow S C :
                Subgroup (product S C)) from
          Subgroup.le_normalizer) x)
  exact hroot

/-- In direct-product coordinates, the transported normalized local
extension is the pulled-back old extension twisted by the Sylow correction. -/
theorem productNormalizedDirectProductExtension_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (productNormalizedDirectProductExtension
        S C hcentral g a
        (productActiveOrbitComap
          S C hcentral h r)).1 =
      IrreducibleCharacter.twist
        ((productLocalSylowTransportCorrection
          S C hcentral h r).comp
            (MonoidHom.snd
              (GroupTheory.internalPPrimeKernelFixedPoints
                (productSylow S C)
                (productPPrimeKernel S C hcentral))
              (GroupTheory.internalNormalizerSylow
                (productSylow S C))))
        ((productNormalizedDirectProductExtension
          S C hcentral g a r).1.comap
            (MulEquiv.prodCongr
              (productDirectFixedFactorConjugation
                S C hcentral h)
              (productDirectSylowFactorConjugation
                S C h))) := by
  change
    IrreducibleCharacter.directProductFirstFactorLinearExtension
        (productGlaubermanDirectFactorCharacter
          S C hcentral g a
          (productActiveOrbitComap
            S C hcentral h r)).1
        (productLocalSylowLinearParameter
          S C hcentral
          (productActiveOrbitComap
            S C hcentral h r)) =
      IrreducibleCharacter.twist
        ((productLocalSylowTransportCorrection
          S C hcentral h r).comp
            (MonoidHom.snd
              (GroupTheory.internalPPrimeKernelFixedPoints
                (productSylow S C)
                (productPPrimeKernel S C hcentral))
              (GroupTheory.internalNormalizerSylow
                (productSylow S C))))
        ((IrreducibleCharacter.directProductFirstFactorLinearExtension
            (productGlaubermanDirectFactorCharacter
              S C hcentral g a r).1
            (productLocalSylowLinearParameter
              S C hcentral r)).comap
          (MulEquiv.prodCongr
            (productDirectFixedFactorConjugation
              S C hcentral h)
            (productDirectSylowFactorConjugation
              S C h)))
  rw [productGlaubermanDirectFactorCharacter_activeOrbitComap,
    productLocalSylowLinearParameter_activeOrbitComap]
  rw [
    IrreducibleCharacter.directProductFirstFactorLinearExtension_comap_prodCongr]
  rw [mul_comm
    (productLocalSylowTransportCorrection
      S C hcentral h r)
    ((productLocalSylowLinearParameter
      S C hcentral r).comp
        (productDirectSylowFactorConjugation
          S C h).toMonoidHom)]
  exact
    IrreducibleCharacter.directProductFirstFactorLinearExtension_mul
      (IrreducibleCharacter.directProductFirstFactorCharacterComap
        (B' :=
          GroupTheory.internalNormalizerSylow
            (productSylow S C))
        (productDirectFixedFactorConjugation
          S C hcentral h)
        (productGlaubermanDirectFactorCharacter
          S C hcentral g a r).1)
      ((productLocalSylowLinearParameter
        S C hcentral r).comp
          (productDirectSylowFactorConjugation
            S C h).toMonoidHom)
      (productLocalSylowTransportCorrection
        S C hcentral h r)

/-- The second-coordinate correction in direct-product coordinates is
exactly the inflated local quotient parameter on the corresponding local
element. -/
theorem productLocalSylowTransportCorrection_coordinate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (x :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :
    productLocalSylowTransportCorrection
        S C hcentral h r
        ((normalizerProductEquiv
          S C hcentral).symm x).2 =
      IrreducibleCharacter.inflateLinearCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (productLocalExtensionTransportParameter
          S C hcentral h r) x := by
  rw [
    productLocalExtensionTransportParameter_inflate_apply]
  change
    productSourceExtensionTransportParameter
        S C hcentral h r
        (QuotientGroup.mk'
          (productPPrimeKernel S C hcentral)
          ((((normalizerProductEquiv
            S C hcentral).symm x).2 :
              localNormalizer
                (productSylow S C :
                  Subgroup (product S C))) :
            product S C)) =
      productSourceExtensionTransportParameter
        S C hcentral h r
        (QuotientGroup.mk'
          (productPPrimeKernel S C hcentral)
          (x : product S C))
  congr 1
  let y :=
    (normalizerProductEquiv S C hcentral).symm x
  have ha :
      (((y.1 :
          localNormalizer
            (productSylow S C :
              Subgroup (product S C))) :
        product S C)) ∈
          productPPrimeKernel S C hcentral :=
    y.1.property.1
  have hclassA :
      QuotientGroup.mk'
          (productPPrimeKernel S C hcentral)
          (((y.1 :
              localNormalizer
                (productSylow S C :
                  Subgroup (product S C))) :
            product S C)) =
        1 :=
    (QuotientGroup.eq_one_iff _).mpr ha
  have hdecomp :
      (y.1 :
          localNormalizer
            (productSylow S C :
              Subgroup (product S C))) *
          (y.2 :
            localNormalizer
              (productSylow S C :
                Subgroup (product S C))) =
        x :=
    (normalizerProductEquiv
      S C hcentral).apply_symm_apply x
  calc
    QuotientGroup.mk'
        (productPPrimeKernel S C hcentral)
        (((y.2 :
            localNormalizer
              (productSylow S C :
                Subgroup (product S C))) :
          product S C)) =
        1 *
          QuotientGroup.mk'
            (productPPrimeKernel S C hcentral)
            (((y.2 :
                localNormalizer
                  (productSylow S C :
                    Subgroup (product S C))) :
              product S C)) := by
      rw [one_mul]
    _ =
        QuotientGroup.mk'
            (productPPrimeKernel S C hcentral)
            (((y.1 :
                localNormalizer
                  (productSylow S C :
                    Subgroup (product S C))) :
              product S C)) *
          QuotientGroup.mk'
            (productPPrimeKernel S C hcentral)
            (((y.2 :
                localNormalizer
                  (productSylow S C :
                    Subgroup (product S C))) :
              product S C)) := by
      rw [hclassA]
    _ =
        QuotientGroup.mk'
          (productPPrimeKernel S C hcentral)
          (((y.1 :
              localNormalizer
                (productSylow S C :
                  Subgroup (product S C))) :
            product S C) *
            ((y.2 :
              localNormalizer
                (productSylow S C :
                  Subgroup (product S C))) :
            product S C)) := by
      rw [map_mul]
    _ =
        QuotientGroup.mk'
          (productPPrimeKernel S C hcentral)
          (x : product S C) := by
      congr 1
      exact congrArg Subtype.val hdecomp

/-- The independently normalized local extension at the transported orbit
differs from the literal pullback of the old normalized local extension by
the inflated image of the *same* canonical source quotient parameter. -/
theorem productNormalizedLocalExtension_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (productNormalizedLocalExtension
        S C hcentral g a
        (productActiveOrbitComap
          S C hcentral h r)).1 =
      IrreducibleCharacter.twist
        (IrreducibleCharacter.inflateLinearCharacter
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          (productLocalExtensionTransportParameter
            S C hcentral h r))
        ((productNormalizedLocalExtension
          S C hcentral g a r).1.comap
            (productLocalNormalizerConjugation
              S C h)) := by
  apply IrreducibleCharacter.ext
  funext x
  rw [IrreducibleCharacter.twist_values,
    IrreducibleCharacter.comap_values]
  change
    (productNormalizedDirectProductExtension
      S C hcentral g a
      (productActiveOrbitComap
        S C hcentral h r)).1.values
        ((normalizerProductEquiv
          S C hcentral).symm x) =
      (IrreducibleCharacter.inflateLinearCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (productLocalExtensionTransportParameter
          S C hcentral h r) x : ℂ) *
        (productNormalizedDirectProductExtension
          S C hcentral g a r).1.values
          ((normalizerProductEquiv
            S C hcentral).symm
              (productLocalNormalizerConjugation
                S C h x))
  rw [
    productNormalizedDirectProductExtension_activeOrbitComap]
  rw [IrreducibleCharacter.twist_values,
    IrreducibleCharacter.comap_values]
  change
    (productLocalSylowTransportCorrection
        S C hcentral h r
        ((normalizerProductEquiv
          S C hcentral).symm x).2 : ℂ) *
        (productNormalizedDirectProductExtension
          S C hcentral g a r).1.values
          ((MulEquiv.prodCongr
            (productDirectFixedFactorConjugation
              S C hcentral h)
            (productDirectSylowFactorConjugation
              S C h))
            ((normalizerProductEquiv
              S C hcentral).symm x)) =
      _
  rw [productLocalSylowTransportCorrection_coordinate]
  congr 2
  apply (normalizerProductEquiv
    S C hcentral).injective
  rw [(normalizerProductEquiv
      S C hcentral).apply_symm_apply]
  have hpoint :=
    DFunLike.congr_fun
      (normalizerProductEquiv_conjugation_commutes
        S C hcentral h)
      ((normalizerProductEquiv
        S C hcentral).symm x)
  change
    productLocalNormalizerConjugation S C h
        (normalizerProductEquiv S C hcentral
          ((normalizerProductEquiv
            S C hcentral).symm x)) =
      normalizerProductEquiv S C hcentral
        ((MulEquiv.prodCongr
          (productDirectFixedFactorConjugation
            S C hcentral h)
          (productDirectSylowFactorConjugation
            S C h))
          ((normalizerProductEquiv
            S C hcentral).symm x)) at hpoint
  rw [(normalizerProductEquiv
      S C hcentral).apply_symm_apply] at hpoint
  exact hpoint.symm

/-- The independently normalized extension at the transported orbit
extends the literal pullback of the old selected local-kernel
representative. -/
theorem productNormalizedLocalExtension_transported_isExtension_literal
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    IrreducibleCharacter.IsExtensionAlong
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))).subtype
      (((productGlaubermanActiveOrbitEquiv
          S C hcentral g a r).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))).1.comap
        (productLocalKernelConjugation
          S C hcentral h))
      (productNormalizedLocalExtension
        S C hcentral g a
        (productActiveOrbitComap
          S C hcentral h r)).1 := by
  have hout :
      ((productGlaubermanActiveOrbitEquiv
          S C hcentral g a
          (productActiveOrbitComap
            S C hcentral h r)).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))).1 =
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1.comap
          (productLocalKernelConjugation
            S C hcentral h)) :=
    congrArg Subtype.val
      (productGlaubermanTargetPPrimeOut_activeOrbitComap
        S C hcentral g a h r)
  rw [← hout]
  exact
    productNormalizedLocalExtension_isExtension
      S C hcentral g a
      (productActiveOrbitComap
        S C hcentral h r)

/-- The canonical Gallagher base-change parameter comparing the pulled-back
old normalized local extension with the independently normalized target
extension. -/
def productNormalizedLocalExtensionTransportParameter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (localNormalizer
          (productSylow S C :
            Subgroup (product S C)) ⧸
        internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) →* ℂˣ :=
  IrreducibleCharacter.gallagherTransportBaseChangeParameter
    (productLocalNormalizerConjugation S C h)
    (productLocalKernelConjugation
      S C hcentral h)
    (productLocalKernelConjugation_subtype_commutes
      S C hcentral h)
    (productNormalizedLocalExtension_isExtension
      S C hcentral g a r)
    (productNormalizedLocalExtension_transported_isExtension_literal
      S C hcentral g a h r)

/-- Determinant normalization makes the canonical local Gallagher
base-change parameter exactly the image of the canonical source parameter
under the source-to-local quotient equivalence. -/
theorem productNormalizedLocalExtensionTransportParameter_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    productNormalizedLocalExtensionTransportParameter
        S C hcentral g a h r =
      productLocalExtensionTransportParameter
        S C hcentral h r := by
  symm
  exact
    IrreducibleCharacter.eq_gallagherBaseChangeParameter
      ((productNormalizedLocalExtension_isExtension
        S C hcentral g a r).comap_equiv
          (productLocalNormalizerConjugation
            S C h)
          (productLocalKernelConjugation
            S C hcentral h)
          (productLocalKernelConjugation_subtype_commutes
            S C hcentral h))
      (productNormalizedLocalExtension_transported_isExtension_literal
        S C hcentral g a h r)
      (productLocalExtensionTransportParameter
        S C hcentral h r)
      (productNormalizedLocalExtension_activeOrbitComap
        S C hcentral g a h r)

/-- Quotient coordinate of a transported source Gallagher character,
corrected for the independently selected target source extension. -/
def productSourceTransportedLinearParameter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) :
    ((product S C) ⧸
      productPPrimeKernel S C hcentral) →* ℂˣ :=
  (productSourceExtensionTransportParameter
      S C hcentral h r)⁻¹ *
    lam.comp
      (productPPrimeKernelQuotientConjugation
        S C hcentral h).toMonoidHom

/-- Transporting a corrected source Gallagher coordinate to the local
quotient gives exactly the corrected transport of the old local coordinate. -/
theorem productLinearQuotientEquiv_sourceTransported
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) :
    productLinearQuotientEquiv S C hcentral
        (productSourceTransportedLinearParameter
          S C hcentral h r lam) =
      (productNormalizedLocalExtensionTransportParameter
          S C hcentral g a h r)⁻¹ *
        (productLinearQuotientEquiv
          S C hcentral lam).comp
            (productLocalKernelQuotientConjugation
              S C hcentral h).toMonoidHom := by
  rw [productNormalizedLocalExtensionTransportParameter_eq]
  apply MonoidHom.ext
  intro x
  change
    ((productSourceExtensionTransportParameter
        S C hcentral h r)⁻¹ *
      lam.comp
        (productPPrimeKernelQuotientConjugation
          S C hcentral h).toMonoidHom)
        (productLocalSourceQuotientEquiv
          S C hcentral x) =
      ((productLocalExtensionTransportParameter
          S C hcentral h r)⁻¹ *
        (productLinearQuotientEquiv
          S C hcentral lam).comp
            (productLocalKernelQuotientConjugation
              S C hcentral h).toMonoidHom) x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply,
    MonoidHom.comp_apply]
  change
    (productSourceExtensionTransportParameter
        S C hcentral h r
        (productLocalSourceQuotientEquiv
          S C hcentral x))⁻¹ *
      lam
        (productPPrimeKernelQuotientConjugation
          S C hcentral h
          (productLocalSourceQuotientEquiv
            S C hcentral x)) =
      (productSourceExtensionTransportParameter
        S C hcentral h r
        (productLocalSourceQuotientEquiv
          S C hcentral x))⁻¹ *
      lam
        (productLocalSourceQuotientEquiv
          S C hcentral
          (productLocalKernelQuotientConjugation
            S C hcentral h x))
  rw [productLocalSourceQuotientEquiv_conjugation_apply]

/-- Pointwise covariance of the source ambient Gallagher family, including
the correction for the independently selected target source extension. -/
theorem productSourceAmbientGallagherEquiv_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) :
    (productSourceAmbientGallagherEquiv
        S C hcentral r lam).1.1.comap
        (productConjugationHom S C h) =
      (productSourceAmbientGallagherEquiv
        S C hcentral
        (productActiveOrbitComap
          S C hcentral h r)
        (productSourceTransportedLinearParameter
          S C hcentral h r lam)).1.1 := by
  apply IrreducibleCharacter.ext
  funext x
  rw [IrreducibleCharacter.comap_values,
    productSourceAmbientGallagherEquiv_values,
    productSourceAmbientGallagherEquiv_values]
  have hbase :=
    congrArg
      (fun χ : IrreducibleCharacter (product S C) ↦
        χ.values x)
      (productSourceExtensionTransportParameter_spec
        S C hcentral h r)
  rw [IrreducibleCharacter.twist_values,
    IrreducibleCharacter.comap_values] at hbase
  rw [hbase]
  rw [IrreducibleCharacter.inflateLinearCharacter_apply]
  simp only [productSourceTransportedLinearParameter,
    MonoidHom.mul_apply, MonoidHom.inv_apply,
    MonoidHom.comp_apply, Units.val_mul]
  have hquotient :=
    congrArg lam
      (productPPrimeKernelQuotientConjugation_mk
        S C hcentral h x)
  have hquotient' :
      lam
          ((productPPrimeKernelQuotientConjugation
            S C hcentral h).toMonoidHom
            (QuotientGroup.mk'
              (productPPrimeKernel S C hcentral) x)) =
        lam
          (QuotientGroup.mk'
            (productPPrimeKernel S C hcentral)
            (productConjugationHom S C h x)) :=
    hquotient
  rw [hquotient']
  simp only [Units.val_inv_eq_inv_val]
  field_simp

/-- Pointwise covariance of the normalized local ambient Gallagher family.
The local quotient parameter is the image of the corrected source
parameter, so no independent local choice remains in the formula. -/
theorem productNormalizedLocalAmbientGallagherEquiv_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (lam :
      ((product S C) ⧸
        productPPrimeKernel S C hcentral) →* ℂˣ) :
    (productNormalizedLocalAmbientGallagherEquiv
        S C hcentral g a r
        (productLinearQuotientEquiv
          S C hcentral lam)).1.1.comap
        (productLocalNormalizerConjugation S C h) =
      (productNormalizedLocalAmbientGallagherEquiv
        S C hcentral g a
        (productActiveOrbitComap
          S C hcentral h r)
        (productLinearQuotientEquiv
          S C hcentral
          (productSourceTransportedLinearParameter
            S C hcentral h r lam))).1.1 := by
  apply IrreducibleCharacter.ext
  funext x
  rw [IrreducibleCharacter.comap_values,
    productNormalizedLocalAmbientGallagherEquiv_values,
    productNormalizedLocalAmbientGallagherEquiv_values]
  have hbase :=
    congrArg
      (fun χ :
        IrreducibleCharacter
          (localNormalizer
            (productSylow S C :
              Subgroup (product S C))) ↦
        χ.values x)
      (productNormalizedLocalExtension_activeOrbitComap
        S C hcentral g a h r)
  rw [IrreducibleCharacter.twist_values,
    IrreducibleCharacter.comap_values] at hbase
  rw [hbase]
  have hparameter :=
    DFunLike.congr_fun
      (productLinearQuotientEquiv_sourceTransported
        S C hcentral g a h r lam)
      (QuotientGroup.mk'
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) x)
  rw [hparameter]
  rw [IrreducibleCharacter.inflateLinearCharacter_apply]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply,
    MonoidHom.comp_apply, Units.val_mul]
  have hquotient :=
    congrArg
      (productLinearQuotientEquiv
        S C hcentral lam)
      (productLocalKernelQuotientConjugation_mk
        S C hcentral h x)
  have hquotient' :
      productLinearQuotientEquiv S C hcentral lam
          ((productLocalKernelQuotientConjugation
            S C hcentral h).toMonoidHom
            (QuotientGroup.mk'
              (internalKernelNormalizer
                (productPPrimeKernel S C hcentral)
                (productSylow S C :
                  Subgroup (product S C))) x)) =
        productLinearQuotientEquiv S C hcentral lam
          (QuotientGroup.mk'
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C)))
            (productLocalNormalizerConjugation
              S C h x)) :=
    hquotient
  rw [hquotient']
  rw [productNormalizedLocalExtensionTransportParameter_eq]
  simp only [Units.val_inv_eq_inv_val]
  field_simp

/-- The inertia-top identification on the source side, named so that
normalizer covariance can be stated without repeating its proof term. -/
def productSourceInertiaAmbientEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q ≃
      PPrimeIrreducibleCharactersOverAlong
        (productPPrimeKernel S C hcentral).subtype
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q :=
  pPrimeIrreducibleCharactersOverInertiaEquivAmbient
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
    q

/-- The inertia-top identification on the normalized local side. -/
def productLocalInertiaAmbientEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
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
              Subgroup (product S C)))).1) q ≃
      PPrimeIrreducibleCharactersOverAlong
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))).subtype
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1) q :=
  pPrimeIrreducibleCharactersOverInertiaEquivAmbient
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
    q

/-- In named inertia-top coordinates, the normalized inertia-fibre map is
literally source Gallagher inversion, quotient transport, and normalized
local Gallagher evaluation. -/
theorem productNormalizedOkuyamaWajimaInertiaFibreEquiv_ambient_apply
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (rho :
      PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q) :
    productLocalInertiaAmbientEquiv
        S C hcentral g a r
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a r rho) =
      productNormalizedLocalAmbientGallagherEquiv
        S C hcentral g a r
        (productLinearQuotientEquiv
          S C hcentral
          ((productSourceAmbientGallagherEquiv
            S C hcentral r).symm
            (productSourceInertiaAmbientEquiv
              S C hcentral r rho))) := by
  rfl

/-- Covariance of the complete normalized Okuyama--Wajima inertia-fibre
equivalence in forward-pullback orientation.

The hypothesis is exactly the underlying ambient-character equality
provided by transport of the source inertia fibre.  The conclusion is the
corresponding equality after applying the complete normalized fibre map. -/
theorem productNormalizedOkuyamaWajimaInertiaFibreEquiv_activeOrbitComap
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (rho :
      PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q)
    (rho' :
      PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        ((productActiveOrbitComap
          S C hcentral h r).pPrimeOut
            (productPPrimeKernel S C hcentral)).1 q)
    (hrho :
      (productSourceInertiaAmbientEquiv
          S C hcentral r rho).1.1.comap
          (productConjugationHom S C h) =
        (productSourceInertiaAmbientEquiv
          S C hcentral
          (productActiveOrbitComap
            S C hcentral h r) rho').1.1) :
    (productLocalInertiaAmbientEquiv
        S C hcentral g a r
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a r rho)).1.1.comap
          (productLocalNormalizerConjugation S C h) =
      (productLocalInertiaAmbientEquiv
        S C hcentral g a
        (productActiveOrbitComap
          S C hcentral h r)
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a
          (productActiveOrbitComap
            S C hcentral h r) rho')).1.1 := by
  let lam :=
    (productSourceAmbientGallagherEquiv
      S C hcentral r).symm
      (productSourceInertiaAmbientEquiv
        S C hcentral r rho)
  let nu :=
    productSourceTransportedLinearParameter
      S C hcentral h r lam
  have hold :
      productSourceAmbientGallagherEquiv
          S C hcentral r lam =
        productSourceInertiaAmbientEquiv
          S C hcentral r rho :=
    (productSourceAmbientGallagherEquiv
      S C hcentral r).apply_symm_apply
        (productSourceInertiaAmbientEquiv
          S C hcentral r rho)
  have holdChar :
      (productSourceAmbientGallagherEquiv
          S C hcentral r lam).1.1 =
        (productSourceInertiaAmbientEquiv
          S C hcentral r rho).1.1 :=
    congrArg (fun z => z.1.1) hold
  have hsource :=
    productSourceAmbientGallagherEquiv_activeOrbitComap
      S C hcentral h r lam
  have htargetChar :
      (productSourceAmbientGallagherEquiv
          S C hcentral
          (productActiveOrbitComap
            S C hcentral h r) nu).1.1 =
        (productSourceInertiaAmbientEquiv
          S C hcentral
          (productActiveOrbitComap
            S C hcentral h r) rho').1.1 := by
    exact hsource.symm.trans
      ((congrArg
        (fun χ : IrreducibleCharacter (product S C) ↦
          χ.comap (productConjugationHom S C h))
        holdChar).trans hrho)
  have htargetFibre :
      productSourceAmbientGallagherEquiv
          S C hcentral
          (productActiveOrbitComap
            S C hcentral h r) nu =
        productSourceInertiaAmbientEquiv
          S C hcentral
          (productActiveOrbitComap
            S C hcentral h r) rho' := by
    apply Subtype.ext
    apply Subtype.ext
    exact htargetChar
  have htargetCoordinate :
      (productSourceAmbientGallagherEquiv
          S C hcentral
          (productActiveOrbitComap
            S C hcentral h r)).symm
          (productSourceInertiaAmbientEquiv
            S C hcentral
            (productActiveOrbitComap
              S C hcentral h r) rho') =
        nu := by
    rw [← htargetFibre]
    exact
      (productSourceAmbientGallagherEquiv
        S C hcentral
        (productActiveOrbitComap
          S C hcentral h r)).symm_apply_apply nu
  rw [
    productNormalizedOkuyamaWajimaInertiaFibreEquiv_ambient_apply,
    productNormalizedOkuyamaWajimaInertiaFibreEquiv_ambient_apply]
  rw [htargetCoordinate]
  exact
    productNormalizedLocalAmbientGallagherEquiv_activeOrbitComap
      S C hcentral g a h r lam

/-- Covariance of the complete normalized Okuyama--Wajima inertia-fibre
equivalence in the inverse-pullback convention used by the DGN normalizer
action. -/
theorem productNormalizedOkuyamaWajimaInertiaFibreEquiv_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (rho :
      PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q)
    (rho' :
      PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        ((productSourceActiveOrbitConjugation
          S C hcentral h r).pPrimeOut
            (productPPrimeKernel S C hcentral)).1 q)
    (hrho :
      (productSourceInertiaAmbientEquiv
          S C hcentral r rho).1.1.comap
          (productConjugationHom S C h).symm =
        (productSourceInertiaAmbientEquiv
          S C hcentral
          (productSourceActiveOrbitConjugation
            S C hcentral h r) rho').1.1) :
    (productLocalInertiaAmbientEquiv
        S C hcentral g a r
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a r rho)).1.1.comap
          (productLocalNormalizerConjugation
            S C h).symm =
      (productLocalInertiaAmbientEquiv
        S C hcentral g a
        (productSourceActiveOrbitConjugation
          S C hcentral h r)
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a
          (productSourceActiveOrbitConjugation
            S C hcentral h r) rho')).1.1 := by
  let rForward :=
    productActiveOrbitComap
      S C hcentral h⁻¹ r
  let rConjugate :=
    productSourceActiveOrbitConjugation
      S C hcentral h r
  have horbit :
      rForward = rConjugate :=
    productActiveOrbitComap_inv
      S C hcentral h r
  let rhoForward :
      PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        (rForward.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q :=
    Eq.mp
      (congrArg
        (fun t :
          ActiveOrbit
            (productPPrimeKernel S C hcentral) q ↦
          PPrimeIrreducibleCharactersOverInertia
            (productPPrimeKernel S C hcentral)
            (t.pPrimeOut
              (productPPrimeKernel S C hcentral)).1 q)
        horbit).symm rho'
  have hsourceCast :
      (productSourceInertiaAmbientEquiv
          S C hcentral rForward rhoForward).1.1 =
        (productSourceInertiaAmbientEquiv
          S C hcentral rConjugate rho').1.1 := by
    cases horbit
    rfl
  have htargetCast :
      (productLocalInertiaAmbientEquiv
        S C hcentral g a rForward
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a rForward rhoForward)).1.1 =
        (productLocalInertiaAmbientEquiv
          S C hcentral g a rConjugate
          (productNormalizedOkuyamaWajimaInertiaFibreEquiv
            S C hcentral g a rConjugate rho')).1.1 := by
    cases horbit
    rfl
  have hrho' :
      (productSourceInertiaAmbientEquiv
          S C hcentral r rho).1.1.comap
          (productConjugationHom S C h⁻¹) =
        (productSourceInertiaAmbientEquiv
          S C hcentral rForward rhoForward).1.1 := by
    calc
      (productSourceInertiaAmbientEquiv
          S C hcentral r rho).1.1.comap
          (productConjugationHom S C h⁻¹) =
        (productSourceInertiaAmbientEquiv
          S C hcentral r rho).1.1.comap
          (productConjugationHom S C h).symm := by
            rw [productConjugationHom_inv]
      _ =
        (productSourceInertiaAmbientEquiv
          S C hcentral rConjugate rho').1.1 :=
        hrho
      _ =
        (productSourceInertiaAmbientEquiv
          S C hcentral rForward rhoForward).1.1 :=
        hsourceCast.symm
  have hforward :=
    productNormalizedOkuyamaWajimaInertiaFibreEquiv_activeOrbitComap
      S C hcentral g a h⁻¹ r rho rhoForward hrho'
  calc
    (productLocalInertiaAmbientEquiv
        S C hcentral g a r
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a r rho)).1.1.comap
          (productLocalNormalizerConjugation
            S C h).symm =
      (productLocalInertiaAmbientEquiv
        S C hcentral g a r
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a r rho)).1.1.comap
          (productLocalNormalizerConjugation
            S C h⁻¹) := by
        rw [productLocalNormalizerConjugation_inv]
    _ =
      (productLocalInertiaAmbientEquiv
        S C hcentral g a rForward
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a rForward rhoForward)).1.1 :=
      hforward
    _ =
      (productLocalInertiaAmbientEquiv
        S C hcentral g a rConjugate
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a rConjugate rho')).1.1 :=
      htargetCast

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
