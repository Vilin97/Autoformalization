/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DirectProductLinearExtension
import McKayConjecture.Character.InertiaTopOrbitRepresentative
import McKayConjecture.Character.PPrimeDeterminantRoot
import McKayConjecture.Character.CentralScalarProduct
import McKayConjecture.GroupTheory.NormalComplementCentralFactors
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionFibreEquivalence

/-!
# A determinant-normalized local extension

For the normal `q′`-kernel `R ◁ RP`, choose a prime-to-`q` source
extension of an invariant kernel character.  Its determinant on `P`,
with the degree exponent inverted modulo `|P|`, records exactly the
central scalar by which `P` acts.

We extend the Glauberman correspondent to `C_R(P) × P` using that
linear character on the second factor.  This gives the normalized local
base point required for the central Okuyama--Wajima fibre comparison.
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

noncomputable local instance productNormalizedExtensionFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

noncomputable local instance productNormalizedExtensionLocalFintype :
    Fintype
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) :=
  Fintype.ofFinite _

/-- The invariant source character represented by an active kernel
orbit. -/
def productSourceInvariantCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    PInvariantPPrimeIrreducibleCharacter
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)) q :=
  a.sourceActiveEquivInvariant
    (activePPrimeOut
      (productPPrimeKernel S C hcentral) r)

/-- The order of the Sylow complement is coprime to the degree of the
selected source extension. -/
theorem productSylow_card_coprime_sourceExtension_degree
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (Nat.card
        (productSylow S C :
          Subgroup (product S C))).Coprime
      (productSourcePPrimeExtension
        S C hcentral r).1.degree := by
  obtain ⟨n, hn⟩ :=
    (productSylow S C).isPGroup'.exists_card_eq
  rw [hn]
  exact
    ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr
      (productSourcePPrimeExtension
        S C hcentral r).2).pow_left n

/-- The determinant-root parameter of the source extension on the
Sylow complement. -/
def productSourceDeterminantRoot
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    (productSylow S C :
        Subgroup (product S C)) →* ℂˣ :=
  IrreducibleCharacter.determinantRootParameter
    (productSourcePPrimeExtension
      S C hcentral r).1
    (productSylow S C :
      Subgroup (product S C)).subtype
    (productSylow_card_coprime_sourceExtension_degree
      S C hcentral r)

/-- The normal `q′`-kernel and the Sylow subgroup are complementary in
the product reduction group. -/
theorem productPPrimeKernel_isComplement'_productSylow
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    (productPPrimeKernel S C hcentral).IsComplement'
      (productSylow S C :
        Subgroup (product S C)) := by
  apply
    (GroupTheory.isComplement'_of_normal_disjoint_sup_eq_top
      (productPPrimeKernel S C hcentral)
      (productSylow S C :
        Subgroup (product S C)) ?_
      (productPPrimeKernel_sup_productSylow_eq_top
        S C hcentral)).symm
  apply disjoint_iff_inf_le.mpr
  rw [inf_comm,
    productPPrimeKernel_inf_productSylow_eq_bot
      S C hcentral]

/-- The `q′`-kernel coordinate of an element of the product reduction
group. -/
def productKernelCoordinate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C) :
    productPPrimeKernel S C hcentral :=
  GroupTheory.normalComplementKernelPart
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    (productPPrimeKernel_isComplement'_productSylow
      S C hcentral) z

/-- The Sylow coordinate of an element of the product reduction group. -/
def productSylowCoordinate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C) :
    (productSylow S C :
      Subgroup (product S C)) :=
  GroupTheory.normalComplementFactorPart
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    (productPPrimeKernel_isComplement'_productSylow
      S C hcentral) z

/-- The two product coordinates multiply to the original element. -/
@[simp]
theorem productKernelCoordinate_mul_productSylowCoordinate
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C) :
    (productKernelCoordinate S C hcentral z :
        product S C) *
        (productSylowCoordinate S C hcentral z :
          product S C) =
      z :=
  GroupTheory.normalComplementKernelPart_mul_factorPart
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    (productPPrimeKernel_isComplement'_productSylow
      S C hcentral) z

/-- For a central element, both its `q′` and Sylow coordinates are
central. -/
theorem productCentralCoordinate_mem_center
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C)) :
    (productKernelCoordinate S C hcentral z :
        product S C) ∈
        Subgroup.center (product S C) ∧
      (productSylowCoordinate S C hcentral z :
        product S C) ∈
        Subgroup.center (product S C) :=
  GroupTheory.normalComplement_central_parts
    (p := q)
    (productPPrimeKernel S C hcentral)
    (productSylow S C :
      Subgroup (product S C))
    (productPPrimeKernel_isPPrimeGroup
      S C hcentral)
    (productSylow S C).isPGroup'
    (productPPrimeKernel_isComplement'_productSylow
      S C hcentral) hz

/-- The central `q′`-coordinate, viewed as the fixed-point factor inside
the local normalizer. -/
def productCentralKernelLocalFactor
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C)) :
    GroupTheory.internalPPrimeKernelFixedPoints
      (productSylow S C)
      (productPPrimeKernel S C hcentral) :=
  ⟨⟨(productKernelCoordinate S C hcentral z :
        product S C),
      Subgroup.center_le_normalizer
        (productSylow S C :
          Set (product S C))
        (productCentralCoordinate_mem_center
          S C hcentral z hz).1⟩,
    ⟨(productKernelCoordinate S C hcentral z).2,
      Subgroup.mem_centralizer_iff.mpr
        (fun x _hx ↦
          Subgroup.mem_center_iff.mp
            (productCentralCoordinate_mem_center
              S C hcentral z hz).1 x)⟩⟩

/-- The central Sylow coordinate, viewed as the Sylow factor inside the
local normalizer. -/
def productCentralSylowLocalFactor
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C) :
    GroupTheory.internalNormalizerSylow
      (productSylow S C) :=
  ⟨⟨(productSylowCoordinate S C hcentral z :
        product S C),
      Subgroup.le_normalizer
        (productSylowCoordinate S C hcentral z).2⟩,
    (productSylowCoordinate S C hcentral z).2⟩

/-- Direct-product coordinates of an ambient-central element in the
local normalizer are its central kernel and Sylow coordinates. -/
theorem normalizerProductEquiv_symm_central
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C)) :
    (normalizerProductEquiv S C hcentral).symm
        ⟨z,
          Subgroup.center_le_normalizer
            (productSylow S C :
              Set (product S C)) hz⟩ =
      (productCentralKernelLocalFactor
          S C hcentral z hz,
        productCentralSylowLocalFactor
          S C hcentral z) := by
  apply (normalizerProductEquiv S C hcentral).injective
  rw [(normalizerProductEquiv S C hcentral).apply_symm_apply]
  apply Subtype.ext
  change
    z =
      (productKernelCoordinate S C hcentral z :
        product S C) *
        (productSylowCoordinate S C hcentral z :
          product S C)
  exact
    (productKernelCoordinate_mul_productSylowCoordinate
      S C hcentral z).symm

/-- The internal first-factor coordinate of a central element relabels
to the ambient fixed-point element used by Glauberman correspondence. -/
theorem directProductFirstFactorAmbientFixedPointsEquiv_centralKernel
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C)) :
    directProductFirstFactorAmbientFixedPointsEquiv
        S C hcentral
        ((IrreducibleCharacter.directProductFirstFactorEquiv
          (G := GroupTheory.internalPPrimeKernelFixedPoints
            (productSylow S C)
            (productPPrimeKernel S C hcentral))
          (H := GroupTheory.internalNormalizerSylow
            (productSylow S C))).symm
          (productCentralKernelLocalFactor
            S C hcentral z hz)) =
      GlaubermanCorrespondence.centralFixedPointElement
        (K := productPPrimeKernel S C hcentral)
        (P := (productSylow S C :
          Subgroup (product S C)))
        (productKernelCoordinate S C hcentral z :
          product S C)
        (productKernelCoordinate S C hcentral z).2
        (productCentralCoordinate_mem_center
          S C hcentral z hz).1 := by
  apply Subtype.ext
  rfl

/-- Relabelling the internal Sylow coordinate gives the original Sylow
coordinate. -/
theorem internalNormalizerSylowEquiv_centralSylow
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (z : product S C) :
    Subgroup.subgroupOfEquivOfLe
        (show
          (productSylow S C :
              Subgroup (product S C)) ≤
            localNormalizer
              (productSylow S C :
                Subgroup (product S C)) from
          Subgroup.le_normalizer)
        (productCentralSylowLocalFactor
          S C hcentral z) =
      productSylowCoordinate S C hcentral z := by
  apply Subtype.ext
  rfl

/-- The source determinant-root parameter, relabelled on the internal
Sylow factor of the local normalizer. -/
def productLocalSylowLinearParameter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    GroupTheory.internalNormalizerSylow
        (productSylow S C) →* ℂˣ :=
  (productSourceDeterminantRoot
    S C hcentral r).comp
      (Subgroup.subgroupOfEquivOfLe
        (show
          (productSylow S C :
              Subgroup (product S C)) ≤
            localNormalizer
              (productSylow S C :
                Subgroup (product S C)) from
          Subgroup.le_normalizer)).toMonoidHom

/-- The Glauberman correspondent, relabelled as a character of the first
factor in the direct-product model of the local normalizer. -/
def productGlaubermanDirectFactorCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    PPrimeIrreducibleCharacter
      (IrreducibleCharacter.directProductFirstFactor
        (G := GroupTheory.internalPPrimeKernelFixedPoints
          (productSylow S C)
          (productPPrimeKernel S C hcentral))
        (H := GroupTheory.internalNormalizerSylow
          (productSylow S C))) q :=
  IrreducibleCharacter.pPrimeComapEquiv q
    (directProductFirstFactorAmbientFixedPointsEquiv
      S C hcentral)
    (g.characterEquiv
      (productSourceInvariantCharacter
        S C hcentral a r))

/-- The local-kernel character selected by the matched active orbit is
literally the transported Glauberman correspondent. -/
theorem productGlaubermanTargetPPrimeOut_eq
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    ((productGlaubermanActiveOrbitEquiv
        S C hcentral g a r).pPrimeOut
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))) =
      IrreducibleCharacter.pPrimeComapEquiv q
        (localKernelAmbientFixedPointsEquiv
          S C hcentral)
        (g.characterEquiv
          (productSourceInvariantCharacter
            S C hcentral a r)) := by
  let K :=
    productPPrimeKernel S C hcentral
  let P : Subgroup (product S C) :=
    productSylow S C
  let M :=
    internalKernelNormalizer K P
  let θ :=
    g.characterEquiv
      (productSourceInvariantCharacter
        S C hcentral a r)
  let θM :
      PPrimeIrreducibleCharacter M q :=
    IrreducibleCharacter.pPrimeComapEquiv q
      (localKernelAmbientFixedPointsEquiv
        S C hcentral) θ
  let t :
      ActivePPrimeIrreducibleCharacter M q :=
    a.fixedPointsEquivTargetActive θ
  have htcoe : t.1 = θM := rfl
  let orbit :=
    productGlaubermanActiveOrbitEquiv
      S C hcentral g a r
  have hmk :
      (Quotient.mk'' θM.1 : OrbitSpace M) =
        orbit.1 := by
    rw [← htcoe]
    exact
      (a.activeOrbitEquiv_apply_coe g
        r).symm
  have hinertia :
      IrreducibleCharacter.inertia M θM.1 = ⊤ := by
    exact
      (productPPrimeKernelCentralIntersectionSetup
        S C hcentral).activeLocalKernel_inertia_eq_top
          K P θM
          (by
            rw [← htcoe]
            exact t.2)
  exact
    ActiveOrbit.pPrimeOut_eq_of_mk_eq_of_inertia_eq_top
      M orbit θM hmk hinertia

/-- The determinant-normalized extension on direct-product
coordinates. -/
def productNormalizedDirectProductExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    PPrimeIrreducibleCharacter
      (GroupTheory.internalPPrimeKernelFixedPoints
          (productSylow S C)
          (productPPrimeKernel S C hcentral) ×
        GroupTheory.internalNormalizerSylow
          (productSylow S C)) q :=
  IrreducibleCharacter.directProductFirstFactorLinearPPrimeExtension
    (productGlaubermanDirectFactorCharacter
      S C hcentral g a r)
    (productLocalSylowLinearParameter
      S C hcentral r)

/-- Transport the normalized direct-product extension to the actual
local Sylow normalizer. -/
def productNormalizedLocalExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q) :
    PPrimeIrreducibleCharacter
      (localNormalizer
        (productSylow S C :
          Subgroup (product S C))) q :=
  IrreducibleCharacter.pPrimeComapEquiv q
    (normalizerProductEquiv S C hcentral).symm
    (productNormalizedDirectProductExtension
      S C hcentral g a r)

/-- The normalized local character extends the local-kernel character
selected by the matched active orbit. -/
theorem productNormalizedLocalExtension_isExtension
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
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
            Subgroup (product S C)))).1)
      (productNormalizedLocalExtension
        S C hcentral g a r).1 := by
  rw [productGlaubermanTargetPPrimeOut_eq
    S C hcentral g a r]
  intro x
  let eM :=
    localKernelDirectProductFirstFactorEquiv
      S C hcentral
  have hcoord :
      (normalizerProductEquiv S C hcentral).symm
          ((internalKernelNormalizer
            (productPPrimeKernel S C hcentral)
            (productSylow S C :
              Subgroup (product S C))).subtype x) =
        (IrreducibleCharacter.directProductFirstFactor
          (G := GroupTheory.internalPPrimeKernelFixedPoints
            (productSylow S C)
            (productPPrimeKernel S C hcentral))
          (H := GroupTheory.internalNormalizerSylow
            (productSylow S C))).subtype
          (eM x) := by
    exact
      DFunLike.congr_fun
        (localKernelDirectProductFirstFactorEquiv_comm
          S C hcentral) x
  change
    (productNormalizedDirectProductExtension
      S C hcentral g a r).1.values
        ((normalizerProductEquiv
          S C hcentral).symm
            ((internalKernelNormalizer
              (productPPrimeKernel S C hcentral)
              (productSylow S C :
                Subgroup (product S C))).subtype x)) =
      (g.characterEquiv
        (productSourceInvariantCharacter
          S C hcentral a r)).1.values
        (localKernelAmbientFixedPointsEquiv
          S C hcentral x)
  rw [hcoord]
  change
    (IrreducibleCharacter.directProductFirstFactorLinearPPrimeExtension
        (productGlaubermanDirectFactorCharacter
          S C hcentral g a r)
        (productLocalSylowLinearParameter
          S C hcentral r)).1.values
          ((IrreducibleCharacter.directProductFirstFactor
            (G := GroupTheory.internalPPrimeKernelFixedPoints
              (productSylow S C)
              (productPPrimeKernel S C hcentral))
            (H := GroupTheory.internalNormalizerSylow
              (productSylow S C))).subtype
            (eM x)) =
      (g.characterEquiv
        (productSourceInvariantCharacter
          S C hcentral a r)).1.values
        (localKernelAmbientFixedPointsEquiv
          S C hcentral x)
  rw [IrreducibleCharacter.directProductFirstFactorLinearPPrimeExtension_isExtension]
  rfl

/-- At a central element, the normalized local extension has the
Glauberman fixed-point value times the source scalar on the Sylow
coordinate. -/
theorem productNormalizedLocalExtension_central_value
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C))
    (c : ℂ)
    (hc :
      (productSourcePPrimeExtension
        S C hcentral r).1.realization.ρ
          (productSylowCoordinate
            S C hcentral z :
              product S C) =
        c • (LinearMap.id :
          Module.End ℂ
            (productSourcePPrimeExtension
              S C hcentral r).1.realization)) :
    (productNormalizedLocalExtension
        S C hcentral g a r).1.values
        ⟨z,
          Subgroup.center_le_normalizer
            (productSylow S C :
              Set (product S C)) hz⟩ =
      (g.characterEquiv
        (productSourceInvariantCharacter
          S C hcentral a r)).1.values
          (GlaubermanCorrespondence.centralFixedPointElement
            (K := productPPrimeKernel S C hcentral)
            (P := (productSylow S C :
              Subgroup (product S C)))
            (productKernelCoordinate S C hcentral z :
              product S C)
            (productKernelCoordinate S C hcentral z).2
            (productCentralCoordinate_mem_center
              S C hcentral z hz).1) *
        c := by
  change
    (productNormalizedDirectProductExtension
      S C hcentral g a r).1.values
        ((normalizerProductEquiv
          S C hcentral).symm
            ⟨z,
              Subgroup.center_le_normalizer
                (productSylow S C :
                  Set (product S C)) hz⟩) =
      _
  rw [normalizerProductEquiv_symm_central
    S C hcentral z hz]
  change
    (IrreducibleCharacter.directProductFirstFactorLinearExtension
      (productGlaubermanDirectFactorCharacter
        S C hcentral g a r).1
      (productLocalSylowLinearParameter
        S C hcentral r)).values
      (productCentralKernelLocalFactor
          S C hcentral z hz,
        productCentralSylowLocalFactor
          S C hcentral z) =
      _
  rw [IrreducibleCharacter.directProductFirstFactorLinearExtension,
    IrreducibleCharacter.externalTensor_values,
    IrreducibleCharacter.comap_values,
    IrreducibleCharacter.linear_values]
  change
    (g.characterEquiv
      (productSourceInvariantCharacter
        S C hcentral a r)).1.values
        (directProductFirstFactorAmbientFixedPointsEquiv
          S C hcentral
          ((IrreducibleCharacter.directProductFirstFactorEquiv
            (G := GroupTheory.internalPPrimeKernelFixedPoints
              (productSylow S C)
              (productPPrimeKernel S C hcentral))
            (H := GroupTheory.internalNormalizerSylow
              (productSylow S C))).symm
            (productCentralKernelLocalFactor
              S C hcentral z hz))) *
      ((productLocalSylowLinearParameter
        S C hcentral r)
        (productCentralSylowLocalFactor
          S C hcentral z) : ℂ) =
      _
  rw [directProductFirstFactorAmbientFixedPointsEquiv_centralKernel
    S C hcentral z hz]
  change
    (g.characterEquiv
      (productSourceInvariantCharacter
        S C hcentral a r)).1.values _ *
      ((productSourceDeterminantRoot
        S C hcentral r)
        (Subgroup.subgroupOfEquivOfLe
          (show
            (productSylow S C :
                Subgroup (product S C)) ≤
              localNormalizer
                (productSylow S C :
                  Subgroup (product S C)) from
            Subgroup.le_normalizer)
          (productCentralSylowLocalFactor
            S C hcentral z)) : ℂ) =
      _
  rw [internalNormalizerSylowEquiv_centralSylow
    S C hcentral z]
  congr 1
  exact
    IrreducibleCharacter.determinantRootParameter_coe_eq_scalar
        (productSourcePPrimeExtension
          S C hcentral r).1
        (productSylow S C :
          Subgroup (product S C)).subtype
        (productSylow_card_coprime_sourceExtension_degree
          S C hcentral r)
        (productSylowCoordinate S C hcentral z)
        c hc

/-- The selected source extension and the determinant-normalized local
extension have identical normalized values on ambient-central
elements. -/
theorem productNormalizedExtensions_central_cross
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (a : ProductGlaubermanActivationData S C hcentral)
    (r :
      ActiveOrbit
        (productPPrimeKernel S C hcentral) q)
    (z : product S C)
    (hz : z ∈ Subgroup.center (product S C)) :
    (productSourcePPrimeExtension
        S C hcentral r).1.values z *
        ((productNormalizedLocalExtension
          S C hcentral g a r).1.degree : ℂ) =
      (productNormalizedLocalExtension
        S C hcentral g a r).1.values
          ⟨z,
            Subgroup.center_le_normalizer
              (productSylow S C :
                Set (product S C)) hz⟩ *
        ((productSourcePPrimeExtension
          S C hcentral r).1.degree : ℂ) := by
  let ψ :=
    (productSourcePPrimeExtension
      S C hcentral r).1
  let θ :=
    productSourceInvariantCharacter
      S C hcentral a r
  let φ :=
    (g.characterEquiv θ).1
  let ξ :=
    (productNormalizedLocalExtension
      S C hcentral g a r).1
  let k :=
    productKernelCoordinate S C hcentral z
  let s :=
    productSylowCoordinate S C hcentral z
  have hkcenter :
      (k : product S C) ∈
        Subgroup.center (product S C) :=
    (productCentralCoordinate_mem_center
      S C hcentral z hz).1
  have hscenter :
      (s : product S C) ∈
        Subgroup.center (product S C) :=
    (productCentralCoordinate_mem_center
      S C hcentral z hz).2
  obtain ⟨c, hc⟩ :=
    ψ.exists_realization_scalar_of_mem_center
      (s : product S C) hscenter
  have hlocalValue :
      ξ.values
          ⟨z,
            Subgroup.center_le_normalizer
              (productSylow S C :
                Set (product S C)) hz⟩ =
        φ.values
          (GlaubermanCorrespondence.centralFixedPointElement
            (K := productPPrimeKernel S C hcentral)
            (P := (productSylow S C :
              Subgroup (product S C)))
            (k : product S C) k.2 hkcenter) *
          c := by
    exact
      productNormalizedLocalExtension_central_value
        S C hcentral g a r z hz c hc
  have hsourceProduct :=
    ψ.values_mul_mul_degree_of_mem_center
      (k : product S C) (s : product S C)
      hkcenter hscenter
  have hks : (k : product S C) * (s : product S C) = z :=
    productKernelCoordinate_mul_productSylowCoordinate
      S C hcentral z
  rw [hks] at hsourceProduct
  have hsValue :
      ψ.values (s : product S C) =
        c * (ψ.degree : ℂ) :=
    ψ.values_eq_scalar_mul_degree
      (s : product S C) c hc
  have hzFactor :
      ψ.values z =
        ψ.values (k : product S C) * c := by
    apply
      mul_right_cancel₀
        (Nat.cast_ne_zero.mpr ψ.degree_ne_zero)
    calc
      ψ.values z * (ψ.degree : ℂ) =
          ψ.values (k : product S C) *
            ψ.values (s : product S C) :=
        hsourceProduct
      _ =
          (ψ.values (k : product S C) * c) *
            (ψ.degree : ℂ) := by
        rw [hsValue]
        ring
  have hkValue :
      ψ.values (k : product S C) =
        θ.1.1.values k := by
    exact
      productSourcePPrimeExtension_isExtension
        S C hcentral r k
  have hsourceDegree :
      ψ.degree = θ.1.1.degree := by
    exact
      (productSourcePPrimeExtension_isExtension
        S C hcentral r).degree_eq
  have hGlauberman :=
    g.central_cross θ
      (k : product S C) k.2 hkcenter
  have hkernelCross :
      ψ.values (k : product S C) *
          (φ.degree : ℂ) =
        φ.values
            (GlaubermanCorrespondence.centralFixedPointElement
              (K := productPPrimeKernel S C hcentral)
              (P := (productSylow S C :
                Subgroup (product S C)))
              (k : product S C) k.2 hkcenter) *
          (ψ.degree : ℂ) := by
    rw [hkValue, hsourceDegree]
    exact hGlauberman
  have hlocalDegree :
      ξ.degree = φ.degree := by
    have hdegree :=
      (productNormalizedLocalExtension_isExtension
        S C hcentral g a r).degree_eq
    rw [productGlaubermanTargetPPrimeOut_eq
      S C hcentral g a r] at hdegree
    exact hdegree
  change
    ψ.values z * (ξ.degree : ℂ) =
      ξ.values
          ⟨z,
            Subgroup.center_le_normalizer
              (productSylow S C :
                Set (product S C)) hz⟩ *
        (ψ.degree : ℂ)
  rw [hlocalDegree, hlocalValue, hzFactor]
  calc
    (ψ.values (k : product S C) * c) *
          (φ.degree : ℂ) =
        (ψ.values (k : product S C) *
          (φ.degree : ℂ)) * c := by
      ring
    _ =
        (φ.values
            (GlaubermanCorrespondence.centralFixedPointElement
              (K := productPPrimeKernel S C hcentral)
              (P := (productSylow S C :
                Subgroup (product S C)))
              (k : product S C) k.2 hkcenter) *
          (ψ.degree : ℂ)) * c := by
      rw [hkernelCross]
    _ =
        (φ.values
            (GlaubermanCorrespondence.centralFixedPointElement
              (K := productPPrimeKernel S C hcentral)
              (P := (productSylow S C :
                Subgroup (product S C)))
              (k : product S C) k.2 hkcenter) * c) *
          (ψ.degree : ℂ) := by
      ring

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
