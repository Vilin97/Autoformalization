/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PGroupQuotientClifford
import McKayConjecture.InductiveMcKay.AdaptedCentralTripleCliffordAssembly
import McKayConjecture.InductiveMcKay.MatchedCentralTripleCliffordAssembly

/-!
# Kernel-level assembly for the central-intersection theorem

This file isolates the ordinary-character/Clifford shell of
Navarro--Späth Corollary 5.14, used as Rossi's Theorem 4.4.

Let `K ◁ L`, let `P ≤ L` be a `p`-subgroup, and assume `L = K P`.
Put `H = N_L(P)` and view `K ∩ H` internally as a normal subgroup of
`H`.  Then `L = K H`.  Consequently an equivariant
Dade--Glauberman--Nagao correspondence on the kernel characters, together
with complete central witnesses for the matched inertia triples, assembles
by Clifford theory to the desired equivalence

`Irr_{p'}(L) ≃ Irr_{p'}(N_L(P))`.

The central-intersection and quotient hypotheses are bundled explicitly in
`CentralIntersectionSetup`.  They are the hypotheses used by the missing
block-theoretic DGN construction; they are not needed again by the
Clifford assembly once `ActiveKernelDGNData` has been supplied.

Importantly, `ActiveKernelDGNData` is not a renamed copy of the desired
global equivalence.  It matches only active Clifford orbits of the smaller
normal subgroups `K` and `K ∩ N_L(P)` and supplies complete
central-isomorphism witnesses at their inertia triples.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace CentralIntersectionKernelAssembly

open CharacterTriple
open CliffordPartition

variable {L : Type} [Group L] [Finite L]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup L) [K.Normal]

/-- The local group in Rossi's Theorem 4.4. -/
abbrev localNormalizer : Subgroup L :=
  Subgroup.normalizer (P : Set L)

/-- The intersection `K ∩ N_L(P)`, represented internally as a subgroup
of `N_L(P)`. -/
abbrev internalKernelNormalizer :
    Subgroup (localNormalizer P) :=
  K.subgroupOf (localNormalizer P)

/-- The internal kernel-normalizer intersection is normal in the local
normalizer. -/
instance internalKernelNormalizerNormal :
    (internalKernelNormalizer K P).Normal :=
  inferInstance

/-- The chosen `p`-subgroup, viewed inside its normalizer. -/
abbrev internalPNormalizer :
    Subgroup (localNormalizer P) :=
  P.subgroupOf (localNormalizer P)

omit [Finite L] [Fact p.Prime] [K.Normal] in
/-- Mapping the internal kernel-normalizer intersection into `L` gives the
literal intersection `K ∩ N_L(P)`. -/
theorem map_internalKernelNormalizer_subtype :
    (internalKernelNormalizer K P).map
        (localNormalizer P).subtype =
      K ⊓ localNormalizer P := by
  rw [Subgroup.subgroupOf_map_subtype, inf_comm]

omit [Finite L] [Fact p.Prime] [K.Normal] in
/-- If `L = KP`, then `K` together with `N_L(P)` generates `L`. -/
theorem kernel_sup_localNormalizer_eq_top
    (hgenerate : K ⊔ P = ⊤) :
    K ⊔ localNormalizer P = ⊤ := by
  apply top_unique
  rw [← hgenerate]
  exact sup_le le_sup_left
    (Subgroup.le_normalizer.trans le_sup_right)

omit [Finite L] [Fact p.Prime] in
/-- Inside `N_L(P)`, the two subgroups
`K ∩ N_L(P)` and `P` still generate whenever `L = KP`. -/
theorem internalKernelNormalizer_sup_internalP_eq_top
    (hgenerate : K ⊔ P = ⊤) :
    internalKernelNormalizer K P ⊔
        internalPNormalizer P =
      ⊤ := by
  apply top_unique
  intro h _
  have hh : (h : L) ∈ K ⊔ P := by
    rw [hgenerate]
    exact Subgroup.mem_top _
  obtain ⟨k, hkK, x, hxP, hkx⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hh
  have hxH : x ∈ localNormalizer P :=
    Subgroup.le_normalizer hxP
  have hkH : k ∈ localNormalizer P := by
    have heq : k = (h : L) * x⁻¹ := by
      rw [← hkx]
      group
    rw [heq]
    exact mul_mem h.property (inv_mem hxH)
  apply Subgroup.mem_sup_of_normal_left.mpr
  exact
    ⟨⟨k, hkH⟩, hkK,
      ⟨x, hxH⟩, hxP,
      Subtype.ext hkx⟩

omit [Finite L] [Fact p.Prime] in
/-- The quotient of `N_L(P)` by `K ∩ N_L(P)` is a `p`-group. -/
theorem localNormalizer_quotient_internalKernel_isPGroup
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤) :
    IsPGroup p
      (localNormalizer P ⧸
        internalKernelNormalizer K P) := by
  have hInternalP :
      IsPGroup p (internalPNormalizer P) :=
    hP.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (show P ≤ localNormalizer P from
          Subgroup.le_normalizer)).symm
  exact
    GroupTheory.quotient_isPGroup_of_sup_eq_top
      (internalKernelNormalizer K P)
      (internalPNormalizer P)
      hInternalP
      (internalKernelNormalizer_sup_internalP_eq_top
        K P hgenerate)

/-- If the chosen `p`-subgroup is normal, its local normalizer is
canonically isomorphic to the whole group. -/
def localNormalizerEquivOfNormal [P.Normal] :
    localNormalizer P ≃* L :=
  (MulEquiv.subgroupCongr
    (Subgroup.normalizer_eq_top (H := P))).trans
      Subgroup.topEquiv

/-- The normal-`P` base case of the central-intersection theorem. -/
def pPrimeEquivOfNormal [P.Normal] :
    PPrimeIrreducibleCharacter L p ≃
      PPrimeIrreducibleCharacter
        (localNormalizer P) p :=
  IrreducibleCharacter.pPrimeComapEquiv p
    (localNormalizerEquivOfNormal P)

/-- The exact group-theoretic hypotheses in the character-equivalence
part of Rossi's Theorem 4.4.

The quotient field is included because it occurs explicitly in the
published statement.  It also follows from `pSubgroup` and `generate`,
as recorded below. -/
structure CentralIntersectionSetup : Prop where
  /-- `P` is a `p`-subgroup. -/
  pSubgroup : IsPGroup p P
  /-- `L = KP`. -/
  generate : K ⊔ P = ⊤
  /-- The explicitly stated quotient hypothesis. -/
  quotientPGroup : IsPGroup p (L ⧸ K)
  /-- The intersection `K ∩ P` is central in `L`. -/
  intersection_le_center :
    K ⊓ P ≤ Subgroup.center L

omit [Finite L] [Fact p.Prime] in
/-- Construct the exact setup without separately proving the redundant
quotient condition. -/
theorem CentralIntersectionSetup.ofGenerate
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (hcentral : K ⊓ P ≤ Subgroup.center L) :
    CentralIntersectionSetup (p := p) K P where
  pSubgroup := hP
  generate := hgenerate
  quotientPGroup :=
    GroupTheory.quotient_isPGroup_of_sup_eq_top
      K P hP hgenerate
  intersection_le_center := hcentral

/-- Under the exact Theorem 4.4 hypotheses, every active Clifford
character of `K` is `L`-invariant. -/
theorem CentralIntersectionSetup.activeKernel_inertia_eq_top
    (s : CentralIntersectionSetup (p := p) K P)
    (θ : PPrimeIrreducibleCharacter K p)
    (hactive : IsActivePPrimeCharacter K θ) :
    IrreducibleCharacter.inertia K θ.1 = ⊤ :=
  inertia_eq_top_of_isActivePPrimeCharacter
    K s.quotientPGroup θ hactive

/-- Active characters of `K ∩ N_L(P)` likewise have full inertia in
`N_L(P)`. -/
theorem CentralIntersectionSetup.activeLocalKernel_inertia_eq_top
    (s : CentralIntersectionSetup (p := p) K P)
    (φ :
      PPrimeIrreducibleCharacter
        (internalKernelNormalizer K P) p)
    (hactive :
      IsActivePPrimeCharacter
        (internalKernelNormalizer K P) φ) :
    IrreducibleCharacter.inertia
        (internalKernelNormalizer K P) φ.1 =
      ⊤ :=
  inertia_eq_top_of_isActivePPrimeCharacter
    (internalKernelNormalizer K P)
    (localNormalizer_quotient_internalKernel_isPGroup
      K P s.pSubgroup s.generate)
    φ hactive

/-- The exact active-orbit Dade--Glauberman--Nagao input that remains
after the group and Clifford reductions.

Only active kernel orbits occur.  This matters already for
`S₃ = A₃ C₂` at `p = 2`: all three characters of `A₃` have odd degree,
but only the trivial orbit is active, matching the single character of
`A₃ ∩ N_{S₃}(C₂) = 1`. -/
structure ActiveKernelDGNData where
  /-- Matching of the active kernel-character orbits. -/
  activeOrbitEquiv :
    ActiveOrbit K p ≃
      ActiveOrbit (internalKernelNormalizer K P) p
  /-- Complete central character-triple compatibility at the exact
  quotient-chosen representatives of matched active orbits. -/
  centralWitness :
    ∀ a : ActiveOrbit K p,
      CompleteCentralIsomorphismWitness
        (ofInertia K (a.pPrimeOut K).1)
        (ofInertia
          (internalKernelNormalizer K P)
          ((activeOrbitEquiv a).pPrimeOut
            (internalKernelNormalizer K P)).1)
  /-- The abstract embedding in each central witness is the canonical
  inclusion of the matched local inertia group into the ambient source
  inertia group.  This is the precise element-level coherence needed to
  transport normalized values of central elements. -/
  embedding_coe :
    ∀ (a : ActiveOrbit K p)
      (h : IrreducibleCharacter.inertia
        (internalKernelNormalizer K P)
        ((activeOrbitEquiv a).pPrimeOut
          (internalKernelNormalizer K P)).1),
      ((((centralWitness a).embedding h :
          IrreducibleCharacter.inertia K
            (a.pPrimeOut K).1) : L)) =
        (((h :
          IrreducibleCharacter.inertia
            (internalKernelNormalizer K P)
            ((activeOrbitEquiv a).pPrimeOut
              (internalKernelNormalizer K P)).1) :
          localNormalizer P) : L)

/-- Turn exact active kernel DGN data into the adapted Clifford assembly
package. -/
def ActiveKernelDGNData.toAdaptedCentralTripleCliffordAssemblyData
    (d : ActiveKernelDGNData (p := p) K P) :
    AdaptedCentralTripleCliffordAssemblyData
      K (internalKernelNormalizer K P) p := by
  letI : Fintype L := Fintype.ofFinite L
  letI : Fintype (localNormalizer P) :=
    Fintype.ofFinite (localNormalizer P)
  exact
    { activeOrbitEquiv := d.activeOrbitEquiv
      sourceRepresentative := fun a => a.pPrimeOut K
      sourceRepresentative_orbit := fun a =>
        Quotient.out_eq' a.1
      sourceInertiaIndex_isPPrime := fun a =>
        activeOrbit_inertia_index_isPPrime K a
      targetRepresentative := fun a =>
        (d.activeOrbitEquiv a).pPrimeOut
          (internalKernelNormalizer K P)
      targetRepresentative_orbit := fun a =>
        Quotient.out_eq' (d.activeOrbitEquiv a).1
      targetInertiaIndex_isPPrime := fun a =>
        activeOrbit_inertia_index_isPPrime
          (internalKernelNormalizer K P)
          (d.activeOrbitEquiv a)
      centralWitness := d.centralWitness }

/-- Assemble the Theorem 4.4 ordinary-character equivalence from the exact
active kernel DGN correspondence. -/
def pPrimeEquivOfActiveKernelDGNData
    (d : ActiveKernelDGNData (p := p) K P) :
    PPrimeIrreducibleCharacter L p ≃
      PPrimeIrreducibleCharacter
        (localNormalizer P) p :=
  d.toAdaptedCentralTripleCliffordAssemblyData
    |>.assembledPPrimeEquiv

/-- Assemble the ordinary-character equivalence with the hypotheses of
Rossi's Theorem 4.4 recorded explicitly.

The setup is the input from which the still-missing block-theoretic DGN
datum must eventually be constructed.  Clifford assembly itself only
uses that datum, hence the underscore on `s`. -/
def pPrimeEquivOfCentralIntersectionActiveKernelDGNData
    (_s : CentralIntersectionSetup (p := p) K P)
    (d : ActiveKernelDGNData (p := p) K P) :
    PPrimeIrreducibleCharacter L p ≃
      PPrimeIrreducibleCharacter
        (localNormalizer P) p :=
  pPrimeEquivOfActiveKernelDGNData K P d

/-- A stronger, convenient kernel-level input.

This data is on `K` and `K ∩ N_L(P)`, not on the two groups occurring in
the desired conclusion.  It is deliberately not the preferred exact
form: an equivalence on *all* prime-to-`p` kernel characters can fail even
when Theorem 4.4 applies.  Use `ActiveKernelDGNData` when formalizing the
Navarro--Späth correspondence itself. -/
structure StrongKernelDGNData where
  /-- Correspondence on prime-to-`p` kernel characters. -/
  characterEquiv :
    PPrimeIrreducibleCharacter K p ≃
      PPrimeIrreducibleCharacter
        (internalKernelNormalizer K P) p
  /-- Equivariance under `N_L(P)`. -/
  characterEquiv_smul :
    ∀ (h : localNormalizer P)
      (θ : PPrimeIrreducibleCharacter K p),
      characterEquiv ((h : L) • θ) =
        h • characterEquiv θ
  /-- Complete central character-triple compatibility for exactly matched
  kernel characters. -/
  centralWitness :
    ∀ θ : PPrimeIrreducibleCharacter K p,
      CompleteCentralIsomorphismWitness
        (ofInertia K θ.1)
        (ofInertia
          (internalKernelNormalizer K P)
          (characterEquiv θ).1)

/-- Turn kernel-level DGN data into the existing matched Clifford
assembly package. -/
def StrongKernelDGNData.toMatchedCentralTripleCliffordAssemblyData
    (hgenerate : K ⊔ P = ⊤)
    (d : StrongKernelDGNData (p := p) K P) :
    MatchedCentralTripleCliffordAssemblyData
      K (localNormalizer P)
        (internalKernelNormalizer K P) p where
  sup_eq_top :=
    kernel_sup_localNormalizer_eq_top K P hgenerate
  characterEquiv := d.characterEquiv
  characterEquiv_smul := d.characterEquiv_smul
  centralWitness := d.centralWitness

/-- The ordinary-character conclusion of Rossi's Theorem 4.4, assembled
from the stronger all-kernel-character correspondence.

The returned equivalence is the desired
`Irr_{p'}(L) ≃ Irr_{p'}(N_L(P))`.  No hypothesis here contains an
equivalence between these two global character sets. -/
def pPrimeEquivOfStrongKernelDGNData
    (s : CentralIntersectionSetup (p := p) K P)
    (d : StrongKernelDGNData (p := p) K P) :
    PPrimeIrreducibleCharacter L p ≃
      PPrimeIrreducibleCharacter
        (localNormalizer P) p :=
  (StrongKernelDGNData.toMatchedCentralTripleCliffordAssemblyData
    (p := p) K P s.generate d).assembledPPrimeEquiv

end CentralIntersectionKernelAssembly
end InductiveMcKay
end McKayConjecture
