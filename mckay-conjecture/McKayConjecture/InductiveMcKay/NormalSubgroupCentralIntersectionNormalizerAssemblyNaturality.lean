/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordActivePartitionNaturality
import McKayConjecture.Character.CliffordAutomorphismNaturality
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerCharacterTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizedExtensionTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionOkuyamaWajima
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanLift

/-!
# Ambient-normalizer naturality of the central-intersection assembly

This file packages the conjugation transports on the source and local
active Clifford partitions as exact
`ActivePPrimeOrbitwiseCorrespondence`s.  It also packages the normalized
Okuyama--Wajima construction as an orbitwise correspondence.

Glauberman equivariance proves the index part of the resulting naturality
square.  Consequently, equivariance of the assembled correspondence is
reduced to one pointwise normalized-fibre statement: equality of the
underlying characters produced by the two routes through a matched
Clifford block.
-/

noncomputable section

open scoped Pointwise

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordCorrespondence
open CliffordEquivalence
open CliffordPartition
open CliffordPartition.ActivePPrimeOrbitwiseCorrespondence
open CentralIntersectionKernelAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productNormalizerAssemblyNaturalityFintypeSource :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

noncomputable local instance productNormalizerAssemblyNaturalityFintypeLocal :
    Fintype
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :=
  Fintype.ofFinite
    (localNormalizer
      (productSylow S C :
        Subgroup (product S C)))

/-- The exact source active-Clifford transport induced by an element of
`N_X(S)`.  Its assembled equivalence is pullback along inverse
conjugation on `CS`. -/
def productSourceActivePPrimeOrbitwiseConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    ActivePPrimeOrbitwiseCorrespondence
      (productPPrimeKernel S C hcentral)
      (productPPrimeKernel S C hcentral) q :=
  activePPrimeOrbitwiseComapCorrespondence
    (productPPrimeKernel S C hcentral)
    (productPPrimeKernel S C hcentral)
    q
    (productConjugationHom S C h).symm
    (productPPrimeKernelConjugationHom
      S C hcentral h).symm
    (productPPrimeKernelConjugation_symm_subtype_commutes
      S C hcentral h)

/-- The exact local active-Clifford transport induced by an element of
`N_X(S)`.  Its assembled equivalence is pullback along inverse
conjugation on `N_{CS}(S)`. -/
def productLocalActivePPrimeOrbitwiseConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    ActivePPrimeOrbitwiseCorrespondence
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) q :=
  activePPrimeOrbitwiseComapCorrespondence
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

/-- Source conjugation, viewed as an ambient automorphism stabilizing the
normal `q′`-kernel. -/
def productSourceKernelConjugationAutStabilizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    IrreducibleCharacter.NormalSubgroupAutStabilizer
      (productPPrimeKernel S C hcentral) :=
  ⟨productConjugationHom S C h, by
    rw [IrreducibleCharacter.NormalSubgroupAutStabilizer.mem_iff]
    rw [Subgroup.pointwise_smul_def]
    exact
      productPPrimeKernel_map_productConjugation
        S C hcentral h⟩

/-- Local conjugation, viewed as an ambient automorphism stabilizing the
normal internal local kernel. -/
def productLocalKernelConjugationAutStabilizer
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    IrreducibleCharacter.NormalSubgroupAutStabilizer
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) :=
  ⟨productLocalNormalizerConjugation S C h, by
    rw [IrreducibleCharacter.NormalSubgroupAutStabilizer.mem_iff]
    rw [Subgroup.pointwise_smul_def]
    exact
      productLocalKernel_map_productLocalNormalizerConjugation
        S C hcentral h⟩

@[simp]
theorem productSourceKernelConjugationAutStabilizer_restrict
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    IrreducibleCharacter.NormalSubgroupAutStabilizer.restrict
        (productSourceKernelConjugationAutStabilizer
          S C hcentral h) =
      productPPrimeKernelConjugationHom
        S C hcentral h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

@[simp]
theorem productLocalKernelConjugationAutStabilizer_restrict
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    IrreducibleCharacter.NormalSubgroupAutStabilizer.restrict
        (productLocalKernelConjugationAutStabilizer
          S C hcentral h) =
      productLocalKernelConjugation
        S C hcentral h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- The inverse local-kernel automorphism transports active local-kernel
characters. -/
def productLocalActivePPrimeCharacterConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      ActivePPrimeIrreducibleCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q) :
    ActivePPrimeIrreducibleCharacter
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) q := by
  let eG :=
    (productLocalNormalizerConjugation S C h).symm
  let eK :=
    (productLocalKernelConjugation
      S C hcentral h).symm
  let hcomm :=
    productLocalKernelConjugation_symm_subtype_commutes
      S C hcentral h
  refine
    ⟨IrreducibleCharacter.pPrimeComapEquiv q eK θ.1, ?_⟩
  exact
    (isActivePPrimeCharacter_comap_equiv_iff
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      eG eK hcomm θ.1).mpr θ.2

@[simp]
theorem productLocalActivePPrimeCharacterConjugation_coe
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (θ :
      ActivePPrimeIrreducibleCharacter
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q) :
    (productLocalActivePPrimeCharacterConjugation
      S C hcentral h θ).1 =
      productLocalKernelConjugation
        S C hcentral h • θ.1 :=
  rfl

/-- Full inertia of active local-kernel characters removes the
`Quotient.out` ambiguity: the chosen representative of a transported
local active orbit is its literal conjugate. -/
theorem productLocalActiveOrbitConjugation_pPrimeOut
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q) :
    (productLocalActiveOrbitConjugation
        S C hcentral h r).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) =
      (productLocalActivePPrimeCharacterConjugation
        S C hcentral h
        (activePPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C))) r)).1 := by
  let K :=
    internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))
  let eG :=
    (productLocalNormalizerConjugation S C h).symm
  let eK :=
    (productLocalKernelConjugation
      S C hcentral h).symm
  let hcomm :=
    productLocalKernelConjugation_symm_subtype_commutes
      S C hcentral h
  let θh :=
    productLocalActivePPrimeCharacterConjugation
      S C hcentral h (activePPrimeOut K r)
  have horbit :
      (Quotient.mk''
          ((productLocalActiveOrbitConjugation
            S C hcentral h r).pPrimeOut K).1 :
            OrbitSpace K) =
        Quotient.mk'' θh.1.1 := by
    calc
      (Quotient.mk''
          ((productLocalActiveOrbitConjugation
            S C hcentral h r).pPrimeOut K).1 :
            OrbitSpace K) =
          (productLocalActiveOrbitConjugation
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
    ((productLocalActiveOrbitConjugation
      S C hcentral h r).pPrimeOut K).1 at hy
  have hfixed :
      y • θh = θh :=
    NormalPPrimeKernelGlauberman.ActivationData.active_smul_eq_of_inertia_eq_top
      K θh
      ((productPPrimeKernelCentralIntersectionSetup
        S C hcentral).activeLocalKernel_inertia_eq_top
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))
          θh.1 θh.2)
      y
  apply Subtype.ext
  calc
    ((productLocalActiveOrbitConjugation
        S C hcentral h r).pPrimeOut K).1 =
        y • θh.1.1 :=
      hy.symm
    _ = θh.1.1 := by
      exact congrArg
        (fun η :
          ActivePPrimeIrreducibleCharacter K q ↦
          η.1.1)
        hfixed

/-- Relabel an inertia fibre along an equality of its base normal
characters. -/
def pPrimeInertiaFibreEquivOfCharacterEq
    {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    (p : ℕ)
    {θ φ : IrreducibleCharacter N}
    (hθφ : θ = φ) :
    PPrimeIrreducibleCharactersOverInertia N θ p ≃
      PPrimeIrreducibleCharactersOverInertia N φ p :=
  Equiv.cast
    (congrArg
      (fun η : IrreducibleCharacter N ↦
        PPrimeIrreducibleCharactersOverInertia N η p)
      hθφ)

/-- Clifford induction commutes with automorphism transport even when the
transported normal character is subsequently relabelled by an equality.
This equality-transported form is convenient for constructions using
`Quotient.out` representatives. -/
theorem cliffordPPrimeCorrespondence_transport_character_of_eq
    {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    (p : ℕ)
    (hp : p.Prime)
    (b :
      IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (θ φ : IrreducibleCharacter N)
    (hθφ : b • θ = φ)
    (hindexθ :
      ¬p ∣ (IrreducibleCharacter.inertia N θ).index)
    (hindexφ :
      ¬p ∣ (IrreducibleCharacter.inertia N φ).index)
    (ρ :
      PPrimeIrreducibleCharactersOverInertia N θ p) :
    ((cliffordPPrimeCorrespondence
        N φ hp hindexφ)
      (((IrreducibleCharacter.pPrimeInertiaFibreTransportEquiv
          N p b θ).trans
        (pPrimeInertiaFibreEquivOfCharacterEq
          N p hθφ)) ρ)).1.1 =
      ((cliffordPPrimeCorrespondence
        N θ hp hindexθ ρ).1.1).comap b.1.symm := by
  subst φ
  let transported :=
    IrreducibleCharacter.pPrimeInertiaFibreTransportEquiv
      N p b θ ρ
  have hcast :
      (((IrreducibleCharacter.pPrimeInertiaFibreTransportEquiv
          N p b θ).trans
        (pPrimeInertiaFibreEquivOfCharacterEq
          N p rfl)) ρ) =
        transported := by
    simp [transported, pPrimeInertiaFibreEquivOfCharacterEq]
  rw [hcast]
  let htransportedIndex :
      ¬p ∣
        (IrreducibleCharacter.inertia
          N (b • θ)).index := by
    simpa only [
      IrreducibleCharacter.inertia_index_smul_eq
        N b θ] using hindexθ
  calc
    ((cliffordPPrimeCorrespondence
        N (b • θ) hp hindexφ) transported).1.1 =
        ((cliffordPPrimeCorrespondence
          N (b • θ) hp htransportedIndex)
          transported).1.1 := by
      congr
    _ =
        ((cliffordPPrimeCorrespondence
          N θ hp hindexθ ρ).1.1).comap b.1.symm := by
      convert
        (IrreducibleCharacter.cliffordPPrimeCorrespondence_transport_character
          N p hp b θ hindexθ ρ) using 1
      all_goals rfl

/-- Full-inertia identification with the ambient group commutes with
automorphism transport, including a final equality relabelling of the
transported normal character. -/
theorem pPrimeInertiaAmbient_transport_character_of_eq
    {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    (p : ℕ)
    (b :
      IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (θ φ : IrreducibleCharacter N)
    (hθφ : b • θ = φ)
    (hinertiaθ :
      IrreducibleCharacter.inertia N θ = ⊤)
    (hinertiaφ :
      IrreducibleCharacter.inertia N φ = ⊤)
    (ρ :
      PPrimeIrreducibleCharactersOverInertia N θ p) :
    ((pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N θ hinertiaθ p ρ).1.1).comap b.1.symm =
      (pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N φ hinertiaφ p
        (((IrreducibleCharacter.pPrimeInertiaFibreTransportEquiv
            N p b θ).trans
          (pPrimeInertiaFibreEquivOfCharacterEq
            N p hθφ)) ρ)).1.1 := by
  subst φ
  let transported :=
    IrreducibleCharacter.pPrimeInertiaFibreTransportEquiv
      N p b θ ρ
  have hcast :
      (((IrreducibleCharacter.pPrimeInertiaFibreTransportEquiv
          N p b θ).trans
        (pPrimeInertiaFibreEquivOfCharacterEq
          N p rfl)) ρ) =
        transported := by
    simp [transported, pPrimeInertiaFibreEquivOfCharacterEq]
  rw [hcast]
  apply IrreducibleCharacter.ext
  funext x
  let xOld :
      IrreducibleCharacter.inertia N θ :=
    ⟨b.1.symm x, by
      rw [hinertiaθ]
      exact Subgroup.mem_top _⟩
  let xNew :
      IrreducibleCharacter.inertia N (b • θ) :=
    ⟨x, by
      rw [hinertiaφ]
      exact Subgroup.mem_top _⟩
  change
    (pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N θ hinertiaθ p ρ).1.1.values
          (b.1.symm x) =
      (pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N (b • θ) hinertiaφ p transported).1.1.values x
  calc
    (pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N θ hinertiaθ p ρ).1.1.values
          (b.1.symm x) =
        ρ.1.1.values xOld :=
      pPrimeIrreducibleCharactersOverInertiaEquivAmbient_values
        N θ hinertiaθ p ρ xOld
    _ =
        transported.1.1.values xNew := by
      change
        ρ.1.1.values xOld =
          ρ.1.1.values
            ((IrreducibleCharacter.inertiaEquiv
              N b θ).symm xNew)
      congr 1
    _ =
        (pPrimeIrreducibleCharactersOverInertiaEquivAmbient
          N (b • θ) hinertiaφ p transported).1.1.values x :=
      (pPrimeIrreducibleCharactersOverInertiaEquivAmbient_values
        N (b • θ) hinertiaφ p transported xNew).symm

/-- Exact source-representative covariance in the automorphism-stabilizer
coordinates used by inertia-fibre transport. -/
theorem productSourceKernelConjugationAutStabilizer_smul_pPrimeOut
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    productSourceKernelConjugationAutStabilizer
        S C hcentral h •
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 =
      ((productSourceActiveOrbitConjugation
          S C hcentral h r).pPrimeOut
        (productPPrimeKernel S C hcentral)).1 := by
  symm
  change
    ((productSourceActiveOrbitConjugation
        S C hcentral h r).pPrimeOut
      (productPPrimeKernel S C hcentral)).1 =
      (productSourceActivePPrimeCharacterConjugation
        S C hcentral h
        (activePPrimeOut
          (productPPrimeKernel S C hcentral) r)).1.1
  exact congrArg Subtype.val
    (productSourceActiveOrbitConjugation_pPrimeOut
      S C hcentral h r)

/-- Exact local-representative covariance in the
automorphism-stabilizer coordinates used by inertia-fibre transport. -/
theorem productLocalKernelConjugationAutStabilizer_smul_pPrimeOut
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q) :
    productLocalKernelConjugationAutStabilizer
        S C hcentral h •
        (r.pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1 =
      ((productLocalActiveOrbitConjugation
          S C hcentral h r).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))).1 := by
  symm
  change
    ((productLocalActiveOrbitConjugation
        S C hcentral h r).pPrimeOut
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))).1 =
      (productLocalActivePPrimeCharacterConjugation
        S C hcentral h
        (activePPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C))) r)).1.1
  exact congrArg Subtype.val
    (productLocalActiveOrbitConjugation_pPrimeOut
      S C hcentral h r)

/-- The normalized target representative over the transported source
orbit is the local automorphism transport of the original target
representative. -/
theorem productNormalizedTargetRepresentative_conjugation
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
    productLocalKernelConjugationAutStabilizer
        S C hcentral h •
        ((productGlaubermanActiveOrbitEquiv
            S C hcentral g a r).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1 =
      ((productGlaubermanActiveOrbitEquiv
          S C hcentral g a
          (productSourceActiveOrbitConjugation
            S C hcentral h r)).pPrimeOut
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))).1 := by
  calc
    productLocalKernelConjugationAutStabilizer
          S C hcentral h •
          ((productGlaubermanActiveOrbitEquiv
              S C hcentral g a r).pPrimeOut
            (internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C)))).1 =
        ((productLocalActiveOrbitConjugation
            S C hcentral h
            (productGlaubermanActiveOrbitEquiv
              S C hcentral g a r)).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1 :=
      productLocalKernelConjugationAutStabilizer_smul_pPrimeOut
        S C hcentral h
        (productGlaubermanActiveOrbitEquiv
          S C hcentral g a r)
    _ =
        ((productGlaubermanActiveOrbitEquiv
            S C hcentral g a
            (productSourceActiveOrbitConjugation
              S C hcentral h r)).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1 := by
      rw [productGlaubermanActiveOrbitEquiv_conjugation
        S C hcentral g a h r]

/-- Inertia-fibre transport on the source, with its target relabelled to
the exact `Quotient.out` representative used by the normalized fibre at
the transported orbit. -/
def productSourceNormalizedInertiaFibreConjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q ≃
      PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        ((productSourceActiveOrbitConjugation
            S C hcentral h r).pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q :=
  (IrreducibleCharacter.pPrimeInertiaFibreTransportEquiv
    (productPPrimeKernel S C hcentral)
    q
    (productSourceKernelConjugationAutStabilizer
      S C hcentral h)
    (r.pPrimeOut
      (productPPrimeKernel S C hcentral)).1).trans
    (pPrimeInertiaFibreEquivOfCharacterEq
      (productPPrimeKernel S C hcentral)
      q
      (productSourceKernelConjugationAutStabilizer_smul_pPrimeOut
        S C hcentral h r))

/-- Inertia-fibre transport on the local side, with its target relabelled
to the exact normalized target representative over the transported
source orbit. -/
def productLocalNormalizedInertiaFibreConjugation
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
      PPrimeIrreducibleCharactersOverInertia
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C)))
        (((productGlaubermanActiveOrbitEquiv
            S C hcentral g a
            (productSourceActiveOrbitConjugation
              S C hcentral h r)).pPrimeOut
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))).1) q :=
  (IrreducibleCharacter.pPrimeInertiaFibreTransportEquiv
    (internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)))
    q
    (productLocalKernelConjugationAutStabilizer
      S C hcentral h)
    ((productGlaubermanActiveOrbitEquiv
      S C hcentral g a r).pPrimeOut
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))).1).trans
    (pPrimeInertiaFibreEquivOfCharacterEq
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      q
      (productNormalizedTargetRepresentative_conjugation
        S C hcentral g a h r))

/-- Raw normalized inertia-fibre naturality under an ambient-normalizer
element.  This is the single pointwise equality needed to deduce
naturality of the Clifford blocks and hence of the global assembly. -/
def ProductNormalizedInertiaFibreNaturality
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S) : Prop :=
  ∀ (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (ρ :
      PPrimeIrreducibleCharactersOverInertia
        (productPPrimeKernel S C hcentral)
        (r.pPrimeOut
          (productPPrimeKernel S C hcentral)).1 q),
    productNormalizedOkuyamaWajimaInertiaFibreEquiv
        S C hcentral g a
        (productSourceActiveOrbitConjugation
          S C hcentral h r)
        (productSourceNormalizedInertiaFibreConjugation
          S C hcentral h r ρ) =
      productLocalNormalizedInertiaFibreConjugation
        S C hcentral g a h r
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a r ρ)

/-- The normalized Okuyama--Wajima fibre covariance theorem supplies the
raw inertia-fibre naturality square unconditionally. -/
theorem productNormalizedInertiaFibreNaturality_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S) :
    ProductNormalizedInertiaFibreNaturality
      S C hcentral g a h := by
  intro r ρ
  let K :=
    productPPrimeKernel S C hcentral
  let P :=
    (productSylow S C :
      Subgroup (product S C))
  let M :=
    internalKernelNormalizer K P
  let r' :=
    productSourceActiveOrbitConjugation
      S C hcentral h r
  let t :=
    productGlaubermanActiveOrbitEquiv
      S C hcentral g a r
  let t' :=
    productGlaubermanActiveOrbitEquiv
      S C hcentral g a r'
  let ρ' :=
    productSourceNormalizedInertiaFibreConjugation
      S C hcentral h r ρ
  let σ :=
    productNormalizedOkuyamaWajimaInertiaFibreEquiv
      S C hcentral g a r ρ
  let σ' :=
    productNormalizedOkuyamaWajimaInertiaFibreEquiv
      S C hcentral g a r' ρ'
  let bSource :=
    productSourceKernelConjugationAutStabilizer
      S C hcentral h
  let bLocal :=
    productLocalKernelConjugationAutStabilizer
      S C hcentral h
  have hsource :
      (productSourceInertiaAmbientEquiv
          S C hcentral r ρ).1.1.comap
          (productConjugationHom S C h).symm =
        (productSourceInertiaAmbientEquiv
          S C hcentral r' ρ').1.1 := by
    exact
      pPrimeInertiaAmbient_transport_character_of_eq
        K q bSource
        (r.pPrimeOut K).1
        (r'.pPrimeOut K).1
        (productSourceKernelConjugationAutStabilizer_smul_pPrimeOut
          S C hcentral h r)
        ((productPPrimeKernelCentralIntersectionSetup
          S C hcentral).activeKernel_inertia_eq_top
            K P
            (r.pPrimeOut K)
            (activePPrimeOut K r).2)
        ((productPPrimeKernelCentralIntersectionSetup
          S C hcentral).activeKernel_inertia_eq_top
            K P
            (r'.pPrimeOut K)
            (activePPrimeOut K r').2)
        ρ
  have hnormalized :
      (productLocalInertiaAmbientEquiv
          S C hcentral g a r σ).1.1.comap
          (productLocalNormalizerConjugation
            S C h).symm =
        (productLocalInertiaAmbientEquiv
          S C hcentral g a r' σ').1.1 :=
    productNormalizedOkuyamaWajimaInertiaFibreEquiv_conjugation
      S C hcentral g a h r ρ ρ' hsource
  have hlocal :
      (productLocalInertiaAmbientEquiv
          S C hcentral g a r σ).1.1.comap
          (productLocalNormalizerConjugation
            S C h).symm =
        (productLocalInertiaAmbientEquiv
          S C hcentral g a r'
          (productLocalNormalizedInertiaFibreConjugation
            S C hcentral g a h r σ)).1.1 := by
    exact
      pPrimeInertiaAmbient_transport_character_of_eq
        M q bLocal
        (t.pPrimeOut M).1
        (t'.pPrimeOut M).1
        (productNormalizedTargetRepresentative_conjugation
          S C hcentral g a h r)
        ((productPPrimeKernelCentralIntersectionSetup
          S C hcentral).activeLocalKernel_inertia_eq_top
            K P
            (t.pPrimeOut M)
            (activePPrimeOut M t).2)
        ((productPPrimeKernelCentralIntersectionSetup
          S C hcentral).activeLocalKernel_inertia_eq_top
            K P
            (t'.pPrimeOut M)
            (activePPrimeOut M t').2)
        σ
  apply
    (productLocalInertiaAmbientEquiv
      S C hcentral g a r').injective
  apply Subtype.ext
  apply Subtype.ext
  exact hnormalized.symm.trans hlocal

/-- The normalized Okuyama--Wajima construction, before global Clifford
assembly, as an exact active-orbitwise correspondence. -/
def productNormalizedActivePPrimeOrbitwiseCorrespondence
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral) :
    ActivePPrimeOrbitwiseCorrespondence
      (productPPrimeKernel S C hcentral)
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C))) q :=
  AdaptedCliffordFibreAssemblyData.toActivePPrimeOrbitwiseCorrespondence
    (((productOkuyamaWajimaFibreData
      S C hcentral g a).toActiveKernelCentralFibreData
        S C).toAdaptedCliffordFibreAssemblyData)

/-- The source inertia coordinate extracted from one element of an active
source Clifford block. -/
def productNormalizedSourceInertiaCoordinate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (χ :
      PPrimeOrbitBlock
        (productPPrimeKernel S C hcentral) q r.1) :
    PPrimeIrreducibleCharactersOverInertia
      (productPPrimeKernel S C hcentral)
      (r.pPrimeOut
        (productPPrimeKernel S C hcentral)).1 q :=
  (cliffordPPrimeCorrespondence
    (productPPrimeKernel S C hcentral)
    (r.pPrimeOut
      (productPPrimeKernel S C hcentral)).1
    (Fact.out : q.Prime)
    (activeOrbit_inertia_index_isPPrime
      (productPPrimeKernel S C hcentral) r)).symm χ

/-- Unfolding one normalized block exposes exactly the stored normalized
inertia-fibre equivalence followed by Clifford induction. -/
theorem productNormalizedActivePPrimeOrbitwiseCorrespondence_block_character
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (χ :
      PPrimeOrbitBlock
        (productPPrimeKernel S C hcentral) q r.1) :
    ((productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a).blockEquiv r χ).1.1 =
      ((cliffordPPrimeCorrespondence
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
        (Fact.out : q.Prime)
        (activeOrbit_inertia_index_isPPrime
          (internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C)))
          (productGlaubermanActiveOrbitEquiv
            S C hcentral g a r)))
        (productNormalizedOkuyamaWajimaInertiaFibreEquiv
          S C hcentral g a r
          (productNormalizedSourceInertiaCoordinate
            S C hcentral r χ))).1.1 :=
  rfl

/-- Extracting the source inertia coordinate after blockwise conjugation is
the same as transporting the original inertia coordinate. -/
theorem productNormalizedSourceInertiaCoordinate_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (χ :
      PPrimeOrbitBlock
        (productPPrimeKernel S C hcentral) q r.1) :
    productNormalizedSourceInertiaCoordinate
        S C hcentral
        (productSourceActiveOrbitConjugation
          S C hcentral h r)
        ((productSourceActivePPrimeOrbitwiseConjugation
          S C hcentral h).blockEquiv r χ) =
      productSourceNormalizedInertiaFibreConjugation
        S C hcentral h r
        (productNormalizedSourceInertiaCoordinate
          S C hcentral r χ) := by
  let K :=
    productPPrimeKernel S C hcentral
  let r' :=
    productSourceActiveOrbitConjugation
      S C hcentral h r
  let b :=
    productSourceKernelConjugationAutStabilizer
      S C hcentral h
  let ρ :=
    productNormalizedSourceInertiaCoordinate
      S C hcentral r χ
  let χ' :=
    (productSourceActivePPrimeOrbitwiseConjugation
      S C hcentral h).blockEquiv r χ
  let e :=
    cliffordPPrimeCorrespondence
      K (r.pPrimeOut K).1
      (Fact.out : q.Prime)
      (activeOrbit_inertia_index_isPPrime K r)
  let e' :=
    cliffordPPrimeCorrespondence
      K (r'.pPrimeOut K).1
      (Fact.out : q.Prime)
      (activeOrbit_inertia_index_isPPrime K r')
  apply e'.injective
  apply Subtype.ext
  apply Subtype.ext
  calc
    (e'
        (productNormalizedSourceInertiaCoordinate
          S C hcentral r' χ')).1.1 =
        χ'.1.1 := by
      exact congrArg
        (fun η :
          PPrimeIrreducibleCharactersOverOrbit
            K (r'.pPrimeOut K).1 q ↦
          η.1.1)
        (e'.apply_symm_apply χ')
    _ = χ.1.1.comap
          (productConjugationHom S C h).symm :=
      rfl
    _ = (e ρ).1.1.comap b.1.symm := by
      have he :
          e ρ = χ := by
        exact e.apply_symm_apply χ
      exact congrArg
        (fun η :
          PPrimeIrreducibleCharactersOverOrbit
            K (r.pPrimeOut K).1 q ↦
          η.1.1.comap
            (productConjugationHom S C h).symm)
        he.symm
    _ =
        (e'
          (productSourceNormalizedInertiaFibreConjugation
            S C hcentral h r ρ)).1.1 := by
      exact
        (cliffordPPrimeCorrespondence_transport_character_of_eq
          K q (Fact.out : q.Prime) b
          (r.pPrimeOut K).1
          (r'.pPrimeOut K).1
          (productSourceKernelConjugationAutStabilizer_smul_pPrimeOut
            S C hcentral h r)
          (activeOrbit_inertia_index_isPPrime K r)
          (activeOrbit_inertia_index_isPPrime K r')
          ρ).symm

@[simp]
theorem productSourceActivePPrimeOrbitwiseConjugation_activeOrbitEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productSourceActivePPrimeOrbitwiseConjugation
        S C hcentral h).activeOrbitEquiv =
      productSourceActiveOrbitConjugation
        S C hcentral h :=
  rfl

@[simp]
theorem productLocalActivePPrimeOrbitwiseConjugation_activeOrbitEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productLocalActivePPrimeOrbitwiseConjugation
        S C hcentral h).activeOrbitEquiv =
      productLocalActiveOrbitConjugation
        S C hcentral h :=
  rfl

@[simp]
theorem productNormalizedActivePPrimeOrbitwiseCorrespondence_activeOrbitEquiv
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral) :
    (productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a).activeOrbitEquiv =
      productGlaubermanActiveOrbitEquiv
        S C hcentral g a :=
  rfl

/-- The source vertical correspondence assembles to inverse pullback by
ambient-normalizer conjugation. -/
theorem productSourceActivePPrimeOrbitwiseConjugation_assemble
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productSourceActivePPrimeOrbitwiseConjugation
        S C hcentral h).assemble =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productConjugationHom S C h).symm :=
  activePPrimeOrbitwiseComapCorrespondence_assemble
    (productPPrimeKernel S C hcentral)
    (productPPrimeKernel S C hcentral)
    q
    (productConjugationHom S C h).symm
    (productPPrimeKernelConjugationHom
      S C hcentral h).symm
    (productPPrimeKernelConjugation_symm_subtype_commutes
      S C hcentral h)

/-- The local vertical correspondence assembles to inverse pullback by
ambient-normalizer conjugation. -/
theorem productLocalActivePPrimeOrbitwiseConjugation_assemble
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (h : ambientNormalizer S) :
    (productLocalActivePPrimeOrbitwiseConjugation
        S C hcentral h).assemble =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productLocalNormalizerConjugation S C h).symm :=
  activePPrimeOrbitwiseComapCorrespondence_assemble
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

/-- Equality of active orbit indices and equality of the underlying
characters determine heterogeneous equality of dependent local Clifford
block elements. -/
private theorem productLocalPPrimeOrbitBlock_heq_of_character_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    {r₁ r₂ :
      ActiveOrbit
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q}
    (hr : r₁ = r₂)
    (χ :
      PPrimeOrbitBlock
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q r₁.1)
    (ψ :
      PPrimeOrbitBlock
        (internalKernelNormalizer
          (productPPrimeKernel S C hcentral)
          (productSylow S C :
            Subgroup (product S C))) q r₂.1)
    (hχψ : χ.1.1 = ψ.1.1) :
    HEq χ ψ := by
  subst r₂
  apply heq_of_eq
  apply Subtype.ext
  apply Subtype.ext
  exact hχψ

/-- The sole pointwise input still needed for naturality of the normalized
Okuyama--Wajima construction.

For every active source orbit and every character in its Clifford block,
the two routes around the conjugation square must produce the same
underlying irreducible character.  The orbit indices already agree by
Glauberman equivariance; proof irrelevance then upgrades this equality to
the heterogeneous equality of dependent block elements required by
`NaturalitySquare`. -/
def ProductNormalizedFibreBlockNaturality
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S) : Prop :=
  let sourceTransport :=
    productSourceActivePPrimeOrbitwiseConjugation
      S C hcentral h
  let localTransport :=
    productLocalActivePPrimeOrbitwiseConjugation
      S C hcentral h
  let normalized :=
    productNormalizedActivePPrimeOrbitwiseCorrespondence
      S C hcentral g a
  ∀ (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (χ :
      PPrimeOrbitBlock
        (productPPrimeKernel S C hcentral) q r.1),
    (normalized.blockEquiv
        (sourceTransport.activeOrbitEquiv r)
        (sourceTransport.blockEquiv r χ)).1.1 =
      (localTransport.blockEquiv
        (normalized.activeOrbitEquiv r)
        (normalized.blockEquiv r χ)).1.1

/-- Raw normalized inertia-fibre naturality implies the pointwise
Clifford-block equality.  The proof uses naturality of Clifford induction
for both vertical automorphism transports. -/
theorem productNormalizedInertiaFibreNaturality_to_block
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S)
    (hfibre :
      ProductNormalizedInertiaFibreNaturality
        S C hcentral g a h) :
    ProductNormalizedFibreBlockNaturality
      S C hcentral g a h := by
  intro r χ
  let K :=
    productPPrimeKernel S C hcentral
  let M :=
    internalKernelNormalizer
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C))
  let r' :=
    productSourceActiveOrbitConjugation
      S C hcentral h r
  let t :=
    productGlaubermanActiveOrbitEquiv
      S C hcentral g a r
  let t' :=
    productGlaubermanActiveOrbitEquiv
      S C hcentral g a r'
  let b :=
    productLocalKernelConjugationAutStabilizer
      S C hcentral h
  let ρ :=
    productNormalizedSourceInertiaCoordinate
      S C hcentral r χ
  let σ :=
    productNormalizedOkuyamaWajimaInertiaFibreEquiv
      S C hcentral g a r ρ
  let χ' :=
    (productSourceActivePPrimeOrbitwiseConjugation
      S C hcentral h).blockEquiv r χ
  let ψ :=
    (productNormalizedActivePPrimeOrbitwiseCorrespondence
      S C hcentral g a).blockEquiv r χ
  let e :=
    cliffordPPrimeCorrespondence
      M (t.pPrimeOut M).1
      (Fact.out : q.Prime)
      (activeOrbit_inertia_index_isPPrime M t)
  let e' :=
    cliffordPPrimeCorrespondence
      M (t'.pPrimeOut M).1
      (Fact.out : q.Prime)
      (activeOrbit_inertia_index_isPPrime M t')
  calc
    ((productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a).blockEquiv r' χ').1.1 =
        (e'
          (productNormalizedOkuyamaWajimaInertiaFibreEquiv
            S C hcentral g a r'
            (productNormalizedSourceInertiaCoordinate
              S C hcentral r' χ'))).1.1 :=
      productNormalizedActivePPrimeOrbitwiseCorrespondence_block_character
        S C hcentral g a r' χ'
    _ =
        (e'
          (productNormalizedOkuyamaWajimaInertiaFibreEquiv
            S C hcentral g a r'
            (productSourceNormalizedInertiaFibreConjugation
              S C hcentral h r ρ))).1.1 := by
      rw [productNormalizedSourceInertiaCoordinate_conjugation
        S C hcentral h r χ]
    _ =
        (e'
          (productLocalNormalizedInertiaFibreConjugation
            S C hcentral g a h r σ)).1.1 := by
      rw [hfibre r ρ]
    _ = (e σ).1.1.comap b.1.symm := by
      exact
        cliffordPPrimeCorrespondence_transport_character_of_eq
          M q (Fact.out : q.Prime) b
          (t.pPrimeOut M).1
          (t'.pPrimeOut M).1
          (productNormalizedTargetRepresentative_conjugation
            S C hcentral g a h r)
          (activeOrbit_inertia_index_isPPrime M t)
          (activeOrbit_inertia_index_isPPrime M t')
          σ
    _ = ψ.1.1.comap
          (productLocalNormalizerConjugation S C h).symm := by
      change
        (e σ).1.1.comap
            (productLocalNormalizerConjugation S C h).symm =
          ψ.1.1.comap
            (productLocalNormalizerConjugation S C h).symm
      exact congrArg
        (fun η :
          IrreducibleCharacter
            (localNormalizer
              (productSylow S C :
                Subgroup (product S C))) ↦
          η.comap
            (productLocalNormalizerConjugation
              S C h).symm)
        (productNormalizedActivePPrimeOrbitwiseCorrespondence_block_character
          S C hcentral g a r χ).symm
    _ =
        ((productLocalActivePPrimeOrbitwiseConjugation
          S C hcentral h).blockEquiv t ψ).1.1 :=
      rfl

/-- The exact naturality square for the normalized orbitwise
correspondence, reduced to the raw normalized inertia-fibre equality
`ProductNormalizedInertiaFibreNaturality`. -/
theorem productNormalizedActivePPrimeOrbitwise_naturalitySquare_of_inertiaFibreNaturality
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S)
    (hfibre :
      ProductNormalizedInertiaFibreNaturality
        S C hcentral g a h) :
    NaturalitySquare
      (productSourceActivePPrimeOrbitwiseConjugation
        S C hcentral h)
      (productLocalActivePPrimeOrbitwiseConjugation
        S C hcentral h)
      (productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a)
      (productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a) := by
  let sourceTransport :=
    productSourceActivePPrimeOrbitwiseConjugation
      S C hcentral h
  let localTransport :=
    productLocalActivePPrimeOrbitwiseConjugation
      S C hcentral h
  let normalized :=
    productNormalizedActivePPrimeOrbitwiseCorrespondence
      S C hcentral g a
  have hblock :
      ProductNormalizedFibreBlockNaturality
        S C hcentral g a h :=
    productNormalizedInertiaFibreNaturality_to_block
      S C hcentral g a h hfibre
  have hindex :
      ∀ r :
        ActiveOrbit
          (productPPrimeKernel S C hcentral) q,
        normalized.activeOrbitEquiv
            (sourceTransport.activeOrbitEquiv r) =
          localTransport.activeOrbitEquiv
            (normalized.activeOrbitEquiv r) := by
    intro r
    exact
      productGlaubermanActiveOrbitEquiv_conjugation
        S C hcentral g a h r
  refine
    { index_commutes := hindex
      block_commutes := ?_ }
  intro r χ
  exact
    productLocalPPrimeOrbitBlock_heq_of_character_eq
      S C hcentral
      (hindex r)
      _ _
      (hblock r χ)

/-- Equivariance of the globally assembled normalized correspondence,
assuming only the pointwise normalized-fibre square. -/
theorem productNormalizedActivePPrimeOrbitwise_assemble_naturality_of_inertiaFibreNaturality
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S)
    (hfibre :
      ProductNormalizedInertiaFibreNaturality
        S C hcentral g a h) :
    (IrreducibleCharacter.pPrimeComapEquiv q
        (productConjugationHom S C h).symm).trans
        (productNormalizedActivePPrimeOrbitwiseCorrespondence
          S C hcentral g a).assemble =
      (productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a).assemble.trans
        (IrreducibleCharacter.pPrimeComapEquiv q
          (productLocalNormalizerConjugation S C h).symm) :=
  assemble_naturality_under_comap
    (productConjugationHom S C h).symm
    (productLocalNormalizerConjugation S C h).symm
    (productPPrimeKernelConjugationHom
      S C hcentral h).symm
    (productLocalKernelConjugation
      S C hcentral h).symm
    (productPPrimeKernelConjugation_symm_subtype_commutes
      S C hcentral h)
    (productLocalKernelConjugation_symm_subtype_commutes
      S C hcentral h)
    (productNormalizedActivePPrimeOrbitwiseCorrespondence
      S C hcentral g a)
    (productNormalizedActivePPrimeOrbitwiseCorrespondence
      S C hcentral g a)
    (productNormalizedActivePPrimeOrbitwise_naturalitySquare_of_inertiaFibreNaturality
      S C hcentral g a h hfibre)

/-- Pointwise ambient-normalizer equivariance of the assembled normalized
correspondence. -/
theorem productNormalizedActivePPrimeOrbitwise_assemble_smul_of_inertiaFibreNaturality
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S)
    (hfibre :
      ProductNormalizedInertiaFibreNaturality
        S C hcentral g a h)
    (χ :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    (productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a).assemble (h • χ) =
      h •
        (productNormalizedActivePPrimeOrbitwiseCorrespondence
          S C hcentral g a).assemble χ := by
  have hnatural :=
    congrArg
      (fun e :
        PPrimeIrreducibleCharacter (product S C) q ≃
          PPrimeIrreducibleCharacter
            (localNormalizer
              (productSylow S C :
                Subgroup (product S C))) q ↦
        e χ)
      (productNormalizedActivePPrimeOrbitwise_assemble_naturality_of_inertiaFibreNaturality
        S C hcentral g a h hfibre)
  exact hnatural

/-- The unconditional exact naturality square for the normalized
orbitwise correspondence. -/
theorem productNormalizedActivePPrimeOrbitwise_naturalitySquare
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S) :
    NaturalitySquare
      (productSourceActivePPrimeOrbitwiseConjugation
        S C hcentral h)
      (productLocalActivePPrimeOrbitwiseConjugation
        S C hcentral h)
      (productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a)
      (productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a) :=
  productNormalizedActivePPrimeOrbitwise_naturalitySquare_of_inertiaFibreNaturality
    S C hcentral g a h
    (productNormalizedInertiaFibreNaturality_conjugation
      S C hcentral g a h)

/-- Unconditional equivalence-level ambient-normalizer naturality of the
globally assembled normalized correspondence. -/
theorem productNormalizedActivePPrimeOrbitwise_assemble_naturality
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S) :
    (IrreducibleCharacter.pPrimeComapEquiv q
        (productConjugationHom S C h).symm).trans
        (productNormalizedActivePPrimeOrbitwiseCorrespondence
          S C hcentral g a).assemble =
      (productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a).assemble.trans
        (IrreducibleCharacter.pPrimeComapEquiv q
          (productLocalNormalizerConjugation S C h).symm) :=
  productNormalizedActivePPrimeOrbitwise_assemble_naturality_of_inertiaFibreNaturality
    S C hcentral g a h
    (productNormalizedInertiaFibreNaturality_conjugation
      S C hcentral g a h)

/-- Unconditional pointwise ambient-normalizer equivariance of the
assembled normalized correspondence. -/
theorem productNormalizedActivePPrimeOrbitwise_assemble_smul
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (a :
      ProductGlaubermanActivationData
        S C hcentral)
    (h : ambientNormalizer S)
    (χ :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    (productNormalizedActivePPrimeOrbitwiseCorrespondence
        S C hcentral g a).assemble (h • χ) =
      h •
        (productNormalizedActivePPrimeOrbitwiseCorrespondence
          S C hcentral g a).assemble χ :=
  productNormalizedActivePPrimeOrbitwise_assemble_smul_of_inertiaFibreNaturality
    S C hcentral g a h
    (productNormalizedInertiaFibreNaturality_conjugation
      S C hcentral g a h)
    χ

/-- Canonical-activation form of raw inertia-fibre naturality. -/
abbrev ProductNormalizedInertiaFibreNaturalityCanonical
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (h : ambientNormalizer S) : Prop :=
  ProductNormalizedInertiaFibreNaturality
    S C hcentral g
    (productGlaubermanActivationData
      S C hcentral)
    h

/-- Ambient-normalizer equivariance of the canonical
Glauberman--Okuyama--Wajima character equivalence. -/
theorem productCanonicalComplementCharacterEquiv_smul
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (h : ambientNormalizer S)
    (χ :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    complementCharacterEquiv
        S C hcentral
        ((productOkuyamaWajimaFibreDataCanonical
          S C hcentral g).toActiveKernelCentralFibreData
            S C)
        (h • χ) =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productLocalNormalizerConjugation S C h).symm
        (complementCharacterEquiv
          S C hcentral
          ((productOkuyamaWajimaFibreDataCanonical
            S C hcentral g).toActiveKernelCentralFibreData
              S C)
          χ) := by
  exact
    productNormalizedActivePPrimeOrbitwise_assemble_smul
      S C hcentral g
      (productGlaubermanActivationData
        S C hcentral)
      h χ

end ComplementReduction

namespace Proposition45

open ComplementReduction

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The concrete Theorem-4.4 equivalence constructed from Glauberman and
normalized Okuyama--Wajima fibres intertwines ambient-normalizer
conjugation.  The target action is written explicitly as inverse pullback
so this statement is independent of downstream choices of action
instances. -/
theorem complementCharacterEquivOfGlauberman_conjugation
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral)
    (h : ambientNormalizer S)
    (χ :
      PPrimeIrreducibleCharacter
        (product S C) q) :
    complementCharacterEquivOfGlauberman
        S C hcentral g (h • χ) =
      IrreducibleCharacter.pPrimeComapEquiv q
        (productLocalNormalizerConjugation S C h).symm
        (complementCharacterEquivOfGlauberman
          S C hcentral g χ) :=
  productCanonicalComplementCharacterEquiv_smul
    S C hcentral g h χ

/-- Equivariance after transporting the concrete Theorem-4.4
correspondence to the subgroup internal to `N_X(S)`.  This is the exact
`characterEquiv_smul` field used by the ambient projective-obstruction
interfaces. -/
theorem complementCharacterEquivOfGlauberman_internal_smul
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g :
      ProductGlaubermanCorrespondence
        S C hcentral) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal
        S C hgenerate
    ∀ (h : ambientNormalizer S)
      (χ :
        PPrimeIrreducibleCharacter
          (product S C) q),
      internalTheorem44CharacterEquiv
          S C
          (complementCharacterEquivOfGlauberman
            S C hcentral g)
          (h • χ) =
        h •
          internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g)
            χ := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  intro h χ
  change
    IrreducibleCharacter.pPrimeComapEquiv q
        (productNormalizerEquivInternal S C).symm
        (complementCharacterEquivOfGlauberman
          S C hcentral g (h • χ)) =
      h •
        IrreducibleCharacter.pPrimeComapEquiv q
          (productNormalizerEquivInternal S C).symm
          (complementCharacterEquivOfGlauberman
            S C hcentral g χ)
  rw [complementCharacterEquivOfGlauberman_conjugation
    S C hcentral g h χ]
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  rfl

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
