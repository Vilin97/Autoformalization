/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordActiveEquivalenceTransport
import McKayConjecture.Character.GlaubermanEquivariance
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerQuotientTransport

/-!
# Ambient-normalizer transport in character coordinates

The group automorphisms constructed from `N_X(S)` act on irreducible
characters by the contragredient convention.  This file identifies those
actions exactly with pullback along the inverse automorphisms and packages
the induced transport of the source and local active Clifford orbits.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordCorrespondence
open CliffordPartition
open CentralIntersectionKernelAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

omit [Finite X] [Fact q.Prime] in
/-- Source-character conjugation is pullback along inverse source
conjugation. -/
@[simp]
theorem productConjugation_smul_pPrime_eq_comap_symm
    (h : ambientNormalizer S)
    (χ : PPrimeIrreducibleCharacter (product S C) q) :
    productConjugationHom S C h • χ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productConjugationHom S C h).symm χ :=
  rfl

omit [Finite X] [Fact q.Prime] in
/-- Local-character conjugation is pullback along inverse local
conjugation. -/
@[simp]
theorem productLocalNormalizerConjugation_smul_pPrime_eq_comap_symm
    (h : ambientNormalizer S)
    (χ :
      PPrimeIrreducibleCharacter
        (localNormalizer
          (productSylow S C :
            Subgroup (product S C))) q) :
    productLocalNormalizerConjugation S C h • χ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productLocalNormalizerConjugation S C h).symm χ :=
  rfl

/-- Source-kernel conjugation is pullback along inverse kernel
conjugation. -/
@[simp]
theorem productPPrimeKernelConjugation_smul_pPrime_eq_comap_symm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      PPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral) q) :
    productPPrimeKernelConjugationHom
        S C hcentral h • θ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productPPrimeKernelConjugationHom
          S C hcentral h).symm θ :=
  rfl

/-- Local-kernel conjugation is pullback along inverse local-kernel
conjugation. -/
@[simp]
theorem productLocalKernelConjugation_smul_pPrime_eq_comap_symm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      PPrimeIrreducibleCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q) :
    productLocalKernelConjugation
        S C hcentral h • θ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productLocalKernelConjugation
          S C hcentral h).symm θ :=
  rfl

/-- Fixed-point character conjugation is pullback along inverse
fixed-point conjugation. -/
@[simp]
theorem productPPrimeKernelFixedPointsConjugation_smul_pPrime_eq_comap_symm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (φ :
      PPrimeIrreducibleCharacter
        (productPPrimeKernelFixedPoints
          S C hcentral) q) :
    productPPrimeKernelFixedPointsConjugation
        S C hcentral h • φ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral h).symm φ :=
  rfl

/-- The restricted local automorphisms, packaged as a homomorphism from
the ambient normalizer. -/
def productLocalNormalizerConjugationHom :
    ambientNormalizer S →*
      MulAut
        (localNormalizer
          (productSylow S C :
            Subgroup (product S C))) where
  toFun := productLocalNormalizerConjugation S C
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change
      productConjugationHom S C 1 (x : product S C) =
        (x : product S C)
    simp
  map_mul' h k := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change
      productConjugationHom S C (h * k)
          (x : product S C) =
        productConjugationHom S C h
          (productConjugationHom S C k
            (x : product S C))
    rw [map_mul]
    rfl

/-- The restricted local-kernel automorphisms, packaged as a homomorphism
from the ambient normalizer. -/
def productLocalKernelConjugationHom
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    ambientNormalizer S →*
      MulAut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) where
  toFun := productLocalKernelConjugation S C hcentral
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change
      productLocalNormalizerConjugation S C 1
          (x :
            localNormalizer
              (productSylow S C :
                Subgroup (product S C))) =
        (x :
          localNormalizer
            (productSylow S C :
              Subgroup (product S C)))
    exact congrArg
      (fun e :
        MulAut
          (localNormalizer
            (productSylow S C :
              Subgroup (product S C))) ↦ e x)
      (map_one
        (productLocalNormalizerConjugationHom S C))
  map_mul' h k := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change
      productLocalNormalizerConjugation S C (h * k)
          (x :
            localNormalizer
              (productSylow S C :
                Subgroup (product S C))) =
        productLocalNormalizerConjugation S C h
          (productLocalNormalizerConjugation S C k
            (x :
              localNormalizer
                (productSylow S C :
                  Subgroup (product S C))))
    exact congrArg
      (fun e :
        MulAut
          (localNormalizer
            (productSylow S C :
              Subgroup (product S C))) ↦ e x)
      (map_mul
        (productLocalNormalizerConjugationHom S C) h k)

/-- The fixed-point automorphisms, packaged as a homomorphism from the
ambient normalizer. -/
def productPPrimeKernelFixedPointsConjugationHom
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    ambientNormalizer S →*
      MulAut
        (productPPrimeKernelFixedPoints
          S C hcentral) where
  toFun :=
    productPPrimeKernelFixedPointsConjugation
      S C hcentral
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change
      productConjugationHom S C 1
          (x : product S C) =
        (x : product S C)
    simp
  map_mul' h k := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change
      productConjugationHom S C (h * k)
          (x : product S C) =
        productConjugationHom S C h
          (productConjugationHom S C k
            (x : product S C))
    rw [map_mul]
    rfl

/-- The ambient normalizer acts on prime-to-`q` source characters. -/
noncomputable instance productSourcePPrimeAmbientNormalizerMulAction :
    MulAction
      (ambientNormalizer S)
      (PPrimeIrreducibleCharacter
        (product S C) q) :=
  MulAction.compHom _
    (productConjugationHom S C)

/-- The ambient normalizer acts on prime-to-`q` local characters. -/
noncomputable instance productLocalPPrimeAmbientNormalizerMulAction :
    MulAction
      (ambientNormalizer S)
      (PPrimeIrreducibleCharacter
        (localNormalizer
          (productSylow S C :
            Subgroup (product S C))) q) :=
  MulAction.compHom _
    (productLocalNormalizerConjugationHom S C)

/-- The ambient normalizer acts on prime-to-`q` source-kernel
characters. -/
noncomputable instance productKernelPPrimeAmbientNormalizerMulAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    MulAction
      (ambientNormalizer S)
      (PPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral) q) :=
  MulAction.compHom _
    (productPPrimeKernelConjugationHom
      S C hcentral)

/-- The ambient normalizer acts on prime-to-`q` local-kernel
characters. -/
noncomputable instance productLocalKernelPPrimeAmbientNormalizerMulAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    MulAction
      (ambientNormalizer S)
      (PPrimeIrreducibleCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q) :=
  MulAction.compHom _
    (productLocalKernelConjugationHom
      S C hcentral)

/-- The ambient normalizer acts on prime-to-`q` fixed-point
characters. -/
noncomputable instance productFixedPointsPPrimeAmbientNormalizerMulAction
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    MulAction
      (ambientNormalizer S)
      (PPrimeIrreducibleCharacter
        (productPPrimeKernelFixedPoints
          S C hcentral) q) :=
  MulAction.compHom _
    (productPPrimeKernelFixedPointsConjugationHom
      S C hcentral)

omit [Finite X] [Fact q.Prime] in
/-- Ambient-normalizer smul on source characters is inverse pullback. -/
@[simp]
theorem ambientNormalizer_smul_productSourcePPrime
    (h : ambientNormalizer S)
    (χ : PPrimeIrreducibleCharacter (product S C) q) :
    h • χ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productConjugationHom S C h).symm χ :=
  rfl

omit [Finite X] [Fact q.Prime] in
/-- Ambient-normalizer smul on local characters is inverse pullback. -/
@[simp]
theorem ambientNormalizer_smul_productLocalPPrime
    (h : ambientNormalizer S)
    (χ :
      PPrimeIrreducibleCharacter
        (localNormalizer
          (productSylow S C :
            Subgroup (product S C))) q) :
    h • χ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productLocalNormalizerConjugation
          S C h).symm χ :=
  rfl

/-- Ambient-normalizer smul on source-kernel characters is inverse
pullback. -/
@[simp]
theorem ambientNormalizer_smul_productKernelPPrime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      PPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral) q) :
    h • θ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productPPrimeKernelConjugationHom
          S C hcentral h).symm θ :=
  rfl

/-- Ambient-normalizer smul on local-kernel characters is inverse
pullback. -/
@[simp]
theorem ambientNormalizer_smul_productLocalKernelPPrime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      PPrimeIrreducibleCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q) :
    h • θ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productLocalKernelConjugation
          S C hcentral h).symm θ :=
  rfl

/-- Ambient-normalizer smul on fixed-point characters is inverse
pullback. -/
@[simp]
theorem ambientNormalizer_smul_productFixedPointsPPrime
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (φ :
      PPrimeIrreducibleCharacter
        (productPPrimeKernelFixedPoints
          S C hcentral) q) :
    h • φ =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral h).symm φ :=
  rfl

/-- The inverse source and source-kernel automorphisms still commute with
the kernel inclusion. -/
theorem productPPrimeKernelConjugation_symm_subtype_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productConjugationHom S C h).symm.toMonoidHom.comp
        (productPPrimeKernel S C hcentral).subtype =
      (productPPrimeKernel S C hcentral).subtype.comp
        (productPPrimeKernelConjugationHom
          S C hcentral h).symm.toMonoidHom :=
  subgroupEquivalenceSquare_symm
    (productPPrimeKernel S C hcentral)
    (productPPrimeKernel S C hcentral)
    (productConjugationHom S C h)
    (productPPrimeKernelConjugationHom
      S C hcentral h)
    (productPPrimeKernelConjugation_subtype_commutes
      S C hcentral h)

/-- The inverse local and local-kernel automorphisms still commute with
the local-kernel inclusion. -/
theorem productLocalKernelConjugation_symm_subtype_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productLocalNormalizerConjugation
        S C h).symm.toMonoidHom.comp
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))).subtype =
      (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))).subtype.comp
        (productLocalKernelConjugation
          S C hcentral h).symm.toMonoidHom :=
  subgroupEquivalenceSquare_symm
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    (productLocalNormalizerConjugation S C h)
    (productLocalKernelConjugation
      S C hcentral h)
    (productLocalKernelConjugation_subtype_commutes
      S C hcentral h)

/-- Active source orbits transported by an ambient-normalizer element. -/
def productSourceActiveOrbitConjugation
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
    (productConjugationHom S C h).symm
    (productPPrimeKernelConjugationHom
      S C hcentral h).symm
    (productPPrimeKernelConjugation_symm_subtype_commutes
      S C hcentral h)

/-- Active local-kernel orbits transported by an ambient-normalizer
element. -/
def productLocalActiveOrbitConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    ActiveOrbit
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q ≃
      ActiveOrbit
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q :=
  activeOrbitComapEquiv
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    q
    (productLocalNormalizerConjugation S C h).symm
    (productLocalKernelConjugation
      S C hcentral h).symm
    (productLocalKernelConjugation_symm_subtype_commutes
      S C hcentral h)

/-- The source-kernel and fixed-point automorphisms commute with the
canonical fixed-point inclusion into the source kernel. -/
theorem productPPrimeKernelFixedPointsConjugation_inclusion_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productPPrimeKernelConjugationHom
        S C hcentral h).toMonoidHom.comp
        (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) =
      (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))).comp
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral h).toMonoidHom := by
  ext x
  rfl

/-- Inverse form of the fixed-point inclusion square. -/
theorem productPPrimeKernelFixedPointsConjugation_symm_inclusion_commutes
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productPPrimeKernelConjugationHom
        S C hcentral h).symm.toMonoidHom.comp
        (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) =
      (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))).comp
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral h).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply
    (productPPrimeKernelConjugationHom
      S C hcentral h).injective
  change
    productPPrimeKernelConjugationHom S C hcentral h
        ((productPPrimeKernelConjugationHom
          S C hcentral h).symm
          (coprimeFixedPointsInclusion
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)) x)) =
      productPPrimeKernelConjugationHom S C hcentral h
        (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))
          ((productPPrimeKernelFixedPointsConjugation
            S C hcentral h).symm x))
  rw [(productPPrimeKernelConjugationHom
      S C hcentral h).apply_symm_apply]
  have hpoint :=
    congrArg
      (fun f :
        productPPrimeKernelFixedPoints S C hcentral →*
          productPPrimeKernel S C hcentral ↦
        f
          ((productPPrimeKernelFixedPointsConjugation
            S C hcentral h).symm x))
      (productPPrimeKernelFixedPointsConjugation_inclusion_commutes
        S C hcentral h)
  change
    productPPrimeKernelConjugationHom S C hcentral h
        (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))
          ((productPPrimeKernelFixedPointsConjugation
            S C hcentral h).symm x)) =
      coprimeFixedPointsInclusion
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral h
          ((productPPrimeKernelFixedPointsConjugation
            S C hcentral h).symm x)) at hpoint
  rw [(productPPrimeKernelFixedPointsConjugation
    S C hcentral h).apply_symm_apply] at hpoint
  exact hpoint.symm

/-- Pulling a `P`-invariant source-kernel character back along an
ambient-normalizer automorphism preserves `P`-invariance. -/
def productPInvariantCharacterConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :
    PInvariantPPrimeIrreducibleCharacter
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)) q := by
  let eG :=
    (productConjugationHom S C h).symm
  let eK :=
    (productPPrimeKernelConjugationHom
      S C hcentral h).symm
  let hcomm :=
    productPPrimeKernelConjugation_symm_subtype_commutes
      S C hcentral h
  refine
    ⟨IrreducibleCharacter.pPrimeComapEquiv q eK θ.1, ?_⟩
  intro x hx
  have hxpre :
      eG x ∈
        (productSylow S C :
          Subgroup (product S C)) := by
    have hmem :
        x ∈
            (productSylow S C :
              Subgroup (product S C)).map
              (productConjugationHom
                S C h).toMonoidHom ↔
          eG x ∈
            (productSylow S C :
              Subgroup (product S C)) :=
      Subgroup.mem_map_equiv
    rw [productSylow_map_productConjugation
      S C h] at hmem
    exact hmem.mp hx
  have hfixed :
      (eG x) • θ.1 = θ.1 := by
    apply Subtype.ext
    exact
      (IrreducibleCharacter.mem_inertia_iff
        (productPPrimeKernel S C hcentral)
        θ.1.1 (eG x)).mp
        (θ.2 hxpre)
  have htransport :=
    pPrimeComapEquiv_conjBy
      (productPPrimeKernel S C hcentral)
      (productPPrimeKernel S C hcentral)
      q eG eK hcomm x θ.1
  rw [hfixed] at htransport
  exact
    (IrreducibleCharacter.mem_inertia_iff
      (productPPrimeKernel S C hcentral)
      (IrreducibleCharacter.pPrimeComapEquiv
        q eK θ.1).1 x).mpr
      (congrArg Subtype.val htransport.symm)

@[simp]
theorem productPInvariantCharacterConjugation_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :
    (productPInvariantCharacterConjugation
      S C hcentral h θ).1 =
      productPPrimeKernelConjugationHom
        S C hcentral h • θ.1 :=
  rfl

/-- The Glauberman character correspondence intertwines the outer
automorphisms induced by every element of `N_X(S)`. -/
theorem productGlaubermanCharacterEquiv_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (h : ambientNormalizer S)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :
    g.characterEquiv
        (productPInvariantCharacterConjugation
          S C hcentral h θ) =
      productPPrimeKernelFixedPointsConjugation
        S C hcentral h •
        g.characterEquiv θ := by
  symm
  apply g.eq_correspondent_of_multiplicity_isPPrime
  let eK :=
    (productPPrimeKernelConjugationHom
      S C hcentral h).symm
  let eF :=
    (productPPrimeKernelFixedPointsConjugation
      S C hcentral h).symm
  have hmult :=
    restrictionMultiplicity_comap_equiv
      eK eF
      (coprimeFixedPointsInclusion
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      (coprimeFixedPointsInclusion
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      (productPPrimeKernelFixedPointsConjugation_symm_inclusion_commutes
        S C hcentral h)
      (g.characterEquiv θ).1 θ.1.1
  change
    ¬q ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        ((g.characterEquiv θ).1.comap eF)
        (θ.1.1.comap eK)
  rw [hmult]
  exact g.multiplicity_isPPrime θ

/-- The existing inner-normalizer equivariance theorem, specialized to
the `CP` Glauberman correspondence. -/
theorem productGlaubermanCharacterEquiv_conjByLocalNormalizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (n :
      localNormalizer
        (productSylow S C :
          Subgroup (product S C)))
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)) q) :
    g.characterEquiv
        (invariantCharacterConjByNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))
          n θ) =
      fixedPointCharacterConjByNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))
        n (g.characterEquiv θ) :=
  GlaubermanCorrespondence.characterEquiv_conjByNormalizer
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    g n θ

/-- Inverse form of the conjugation square for the canonical
local-kernel/fixed-point equivalence. -/
theorem localKernelAmbientFixedPointsEquiv_conjugation_symm
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (x :
      internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) :
    localKernelAmbientFixedPointsEquiv
        S C hcentral
        ((productLocalKernelConjugation
          S C hcentral h).symm x) =
      (productPPrimeKernelFixedPointsConjugation
        S C hcentral h).symm
        (localKernelAmbientFixedPointsEquiv
          S C hcentral x) := by
  apply
    (productPPrimeKernelFixedPointsConjugation
      S C hcentral h).injective
  rw [(productPPrimeKernelFixedPointsConjugation
      S C hcentral h).apply_symm_apply]
  rw [← localKernelAmbientFixedPointsEquiv_conjugation
    S C hcentral h]
  rw [(productLocalKernelConjugation
      S C hcentral h).apply_symm_apply]

/-- Relabelling fixed-point characters to the internal local kernel
intertwines outer-normalizer conjugation. -/
theorem localKernelAmbientFixedPointsPPrimeComap_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (φ :
      PPrimeIrreducibleCharacter
        (productPPrimeKernelFixedPoints
          S C hcentral) q) :
    IrreducibleCharacter.pPrimeComapEquiv q
        (localKernelAmbientFixedPointsEquiv
          S C hcentral)
        (productPPrimeKernelFixedPointsConjugation
          S C hcentral h • φ) =
      productLocalKernelConjugation
        S C hcentral h •
        IrreducibleCharacter.pPrimeComapEquiv q
          (localKernelAmbientFixedPointsEquiv
            S C hcentral) φ := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  change
    φ.1.values
        ((productPPrimeKernelFixedPointsConjugation
          S C hcentral h).symm
          (localKernelAmbientFixedPointsEquiv
            S C hcentral x)) =
      φ.1.values
        (localKernelAmbientFixedPointsEquiv
          S C hcentral
          ((productLocalKernelConjugation
            S C hcentral h).symm x))
  congr 1

/-- The inverse kernel automorphism transports active source-kernel
characters. -/
def productSourceActivePPrimeCharacterConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      ActivePPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral) q) :
    ActivePPrimeIrreducibleCharacter
      (productPPrimeKernel S C hcentral) q := by
  let eG :=
    (productConjugationHom S C h).symm
  let eK :=
    (productPPrimeKernelConjugationHom
      S C hcentral h).symm
  let hcomm :=
    productPPrimeKernelConjugation_symm_subtype_commutes
      S C hcentral h
  refine
    ⟨IrreducibleCharacter.pPrimeComapEquiv q eK θ.1, ?_⟩
  exact
    (isActivePPrimeCharacter_comap_equiv_iff
      (productPPrimeKernel S C hcentral)
      (productPPrimeKernel S C hcentral)
      eG eK hcomm θ.1).mpr θ.2

@[simp]
theorem productSourceActivePPrimeCharacterConjugation_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      ActivePPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral) q) :
    (productSourceActivePPrimeCharacterConjugation
      S C hcentral h θ).1 =
      productPPrimeKernelConjugationHom
        S C hcentral h • θ.1 :=
  rfl

/-- The chosen representative of the transported active source orbit is
the literal conjugate of the chosen source representative.  Full inertia
of active kernel characters removes the otherwise harmless orbit
ambiguity. -/
theorem productSourceActiveOrbitConjugation_pPrimeOut
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (productSourceActiveOrbitConjugation
        S C hcentral h r).pPrimeOut
        (productPPrimeKernel S C hcentral) =
      (productSourceActivePPrimeCharacterConjugation
        S C hcentral h
        (activePPrimeOut
          (productPPrimeKernel S C hcentral) r)).1 := by
  let K :=
    productPPrimeKernel S C hcentral
  let eG :=
    (productConjugationHom S C h).symm
  let eK :=
    (productPPrimeKernelConjugationHom
      S C hcentral h).symm
  let hcomm :=
    productPPrimeKernelConjugation_symm_subtype_commutes
      S C hcentral h
  let θh :=
    productSourceActivePPrimeCharacterConjugation
      S C hcentral h (activePPrimeOut K r)
  have horbit :
      (Quotient.mk''
          ((productSourceActiveOrbitConjugation
            S C hcentral h r).pPrimeOut K).1 :
            OrbitSpace K) =
        Quotient.mk'' θh.1.1 := by
    calc
      (Quotient.mk''
          ((productSourceActiveOrbitConjugation
            S C hcentral h r).pPrimeOut K).1 :
            OrbitSpace K) =
          (productSourceActiveOrbitConjugation
            S C hcentral h r).1 :=
        Quotient.out_eq' _
      _ =
          orbitSpaceComapEquiv
            K K eG eK hcomm r.1 :=
        rfl
      _ =
          orbitSpaceComapEquiv
            K K eG eK hcomm
            (Quotient.mk''
              (r.pPrimeOut K).1) := by
        exact congrArg
          (orbitSpaceComapEquiv
            K K eG eK hcomm)
          (Quotient.out_eq' r.1).symm
      _ =
          Quotient.mk''
            ((r.pPrimeOut K).1.comap eK) :=
        orbitSpaceComapEquiv_mk
          K K eG eK hcomm (r.pPrimeOut K).1
      _ = Quotient.mk'' θh.1.1 :=
        rfl
  obtain ⟨y, hy⟩ :=
    Quotient.exact horbit
  change y • θh.1.1 =
    ((productSourceActiveOrbitConjugation
      S C hcentral h r).pPrimeOut K).1 at hy
  have hfixed :
      y • θh = θh :=
    NormalPPrimeKernelGlauberman.ActivationData.active_smul_eq_of_inertia_eq_top
      K θh
      ((productPPrimeKernelCentralIntersectionSetup
        S C hcentral).activeKernel_inertia_eq_top
          K
          (productSylow S C :
            Subgroup (product S C))
          θh.1 θh.2)
      y
  apply Subtype.ext
  calc
    ((productSourceActiveOrbitConjugation
        S C hcentral h r).pPrimeOut K).1 =
        y • θh.1.1 :=
      hy.symm
    _ = θh.1.1 := by
      exact congrArg
        (fun η :
          ActivePPrimeIrreducibleCharacter K q ↦
          η.1.1)
        hfixed

/-- Active-subtype form of
`productSourceActiveOrbitConjugation_pPrimeOut`. -/
theorem productSourceActiveOrbitConjugation_activePPrimeOut
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    activePPrimeOut
        (productPPrimeKernel S C hcentral)
        (productSourceActiveOrbitConjugation
          S C hcentral h r) =
      productSourceActivePPrimeCharacterConjugation
        S C hcentral h
        (activePPrimeOut
          (productPPrimeKernel S C hcentral) r) := by
  apply Subtype.ext
  exact
    productSourceActiveOrbitConjugation_pPrimeOut
      S C hcentral h r

/-- Character-level form of Glauberman covariance after relabelling the
fixed-point correspondent to the internal local kernel. -/
theorem productGlaubermanActiveCharacterEquiv_conjugation_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S)
    (θ :
      ActivePPrimeIrreducibleCharacter
        (productPPrimeKernel S C hcentral) q) :
    (a.activeCharacterEquiv g
        (productSourceActivePPrimeCharacterConjugation
          S C hcentral h θ)).1 =
      productLocalKernelConjugation
        S C hcentral h •
        (a.activeCharacterEquiv g θ).1 := by
  have hinvariant :
      a.sourceActiveEquivInvariant
          (productSourceActivePPrimeCharacterConjugation
            S C hcentral h θ) =
        productPInvariantCharacterConjugation
          S C hcentral h
          (a.sourceActiveEquivInvariant θ) := by
    apply Subtype.ext
    rfl
  rw [
    NormalPPrimeKernelGlauberman.ActivationData.activeCharacterEquiv_apply_coe]
  rw [hinvariant]
  rw [productGlaubermanCharacterEquiv_conjugation
    S C hcentral g h]
  rw [
    NormalPPrimeKernelGlauberman.ActivationData.activeCharacterEquiv_apply_coe]
  exact
    localKernelAmbientFixedPointsPPrimeComap_conjugation
      S C hcentral h
      (g.characterEquiv
        (a.sourceActiveEquivInvariant θ))

/-- The Glauberman active-orbit equivalence intertwines the source and
local active-orbit transports induced by `N_X(S)`. -/
theorem productGlaubermanActiveOrbitEquiv_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    productGlaubermanActiveOrbitEquiv
        S C hcentral g a
        (productSourceActiveOrbitConjugation
          S C hcentral h r) =
      productLocalActiveOrbitConjugation
        S C hcentral h
        (productGlaubermanActiveOrbitEquiv
          S C hcentral g a r) := by
  apply Subtype.ext
  change
    (a.activeOrbitEquiv g
      (productSourceActiveOrbitConjugation
        S C hcentral h r)).1 =
      (productLocalActiveOrbitConjugation
        S C hcentral h
        (a.activeOrbitEquiv g r)).1
  rw [
    NormalPPrimeKernelGlauberman.ActivationData.activeOrbitEquiv_apply_coe]
  simp only [productLocalActiveOrbitConjugation]
  rw [activeOrbitComapEquiv_apply_coe]
  rw [
    NormalPPrimeKernelGlauberman.ActivationData.activeOrbitEquiv_apply_coe]
  rw [orbitSpaceComapEquiv_mk]
  rw [
    productSourceActiveOrbitConjugation_activePPrimeOut
      S C hcentral h r]
  exact congrArg
    (fun η :
      PPrimeIrreducibleCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q ↦
      (Quotient.mk'' η.1 :
        OrbitSpace
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))))
    (productGlaubermanActiveCharacterEquiv_conjugation_coe
      S C hcentral g a h
      (activePPrimeOut
        (productPPrimeKernel S C hcentral) r))

/-- Equivalence-level form of Glauberman active-orbit covariance. -/
theorem productGlaubermanActiveOrbitEquiv_conjugation_equiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S) :
    (productSourceActiveOrbitConjugation
        S C hcentral h).trans
        (productGlaubermanActiveOrbitEquiv
          S C hcentral g a) =
      (productGlaubermanActiveOrbitEquiv
        S C hcentral g a).trans
        (productLocalActiveOrbitConjugation
          S C hcentral h) := by
  apply Equiv.ext
  intro r
  exact
    productGlaubermanActiveOrbitEquiv_conjugation
      S C hcentral g a h r

/-- Canonical-activation form of Glauberman active-orbit covariance. -/
theorem productGlaubermanActiveOrbitEquivCanonical_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    productGlaubermanActiveOrbitEquivCanonical
        S C hcentral g
        (productSourceActiveOrbitConjugation
          S C hcentral h r) =
      productLocalActiveOrbitConjugation
        S C hcentral h
        (productGlaubermanActiveOrbitEquivCanonical
          S C hcentral g r) :=
  productGlaubermanActiveOrbitEquiv_conjugation
    S C hcentral g
    (productGlaubermanActivationData
      S C hcentral)
    h r

/-- Equivalence-level canonical-activation form of Glauberman
active-orbit covariance. -/
theorem productGlaubermanActiveOrbitEquivCanonical_conjugation_equiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (h : ambientNormalizer S) :
    (productSourceActiveOrbitConjugation
        S C hcentral h).trans
        (productGlaubermanActiveOrbitEquivCanonical
          S C hcentral g) =
      (productGlaubermanActiveOrbitEquivCanonical
        S C hcentral g).trans
        (productLocalActiveOrbitConjugation
          S C hcentral h) := by
  apply Equiv.ext
  intro r
  exact
    productGlaubermanActiveOrbitEquivCanonical_conjugation
      S C hcentral g h r

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
