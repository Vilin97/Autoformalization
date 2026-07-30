/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicExtensionAlong
import McKayConjecture.Character.OkuyamaWajimaFullFixedBurnsideAdapter
import McKayConjecture.Character.OkuyamaWajimaProperBranchCoordinates
import McKayConjecture.GroupTheory.SubgroupProductIndex

/-!
# Outer group coordinates for the full-fixed Okuyama--Wajima branch

Let `M` be the canonical `p'`-complement in `N_G(P)` and let `U ◁ M`
be the subgroup selected by the Gorenstein theorem.  In the full-fixed
branch, Burnside basis theory gives `U ≤ C_G(P)`.  The two intermediate
groups in the printed argument are

* `U K`, where the Isaacs 13.29 maximal-fibre comparison is applied; and
* `M K`, across which the selected character extends because
  `M K / U K` is cyclic.

This file records those group coordinates independently of the character
transport.  In particular, no normality of the proper-branch subgroup
`Q M K` is asserted here.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedOuterCoordinates

open GroupTheory
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

section SelectedSubgroup

variable (M P : Subgroup G)
variable
  (hM :
    M ≤ Subgroup.normalizer (P : Set G))
variable {L : Subgroup M}
variable
  (d :
    @OkuyamaWajimaCyclicQuotientSubgroup
      M P inferInstance inferInstance
      (OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        M P hM) L)

/-- The selected subgroup in `M`, with the conjugation action made
explicit so that its type does not rely on an ambient action instance. -/
abbrev selectedSubgroupInM : Subgroup M := by
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  exact d.U.toSubgroup

/-- The selected subgroup in the original ambient group, with its action
instance fixed explicitly by the normalizer inclusion. -/
abbrev selectedAmbientSubgroup : Subgroup G :=
  (selectedSubgroupInM M P hM d).map M.subtype

/-- The ambient image of the selected subgroup, pulled back to `M`, is
literally the selected normal subgroup `d.U`. -/
theorem ambientSelectedSubgroup_subgroupOf_M_eq :
    (selectedAmbientSubgroup M P hM d).subgroupOf M =
      selectedSubgroupInM M P hM d := by
  ext x
  change
    (x : G) ∈
        (selectedSubgroupInM M P hM d).map M.subtype ↔
      x ∈ selectedSubgroupInM M P hM d
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := by
      apply Subtype.ext
      exact hxy
    subst y
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Consequently the ambient selected subgroup is normal inside `M`. -/
theorem ambientSelectedSubgroup_normal_in_M :
    ((selectedAmbientSubgroup M P hM d).subgroupOf M).Normal := by
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  rw [ambientSelectedSubgroup_subgroupOf_M_eq M P hM d]
  infer_instance

end SelectedSubgroup

section SourceAndMiddle

variable (K M U : Subgroup G) [K.Normal]

/-- The selected source group `U K` lies in the middle group `M K`. -/
theorem source_le_middle
    (hUM : U ≤ M) :
    U ⊔ K ≤ M ⊔ K :=
  sup_le (hUM.trans le_sup_left) le_sup_right

/-- `M` normalizes `U K`: it normalizes `U` by hypothesis and `K`
because `K ◁ G`. -/
theorem M_le_normalizer_source :
    (U ≤ M) →
    (U.subgroupOf M).Normal →
    M ≤ Subgroup.normalizer ((U ⊔ K : Subgroup G) : Set G) := by
  intro hUM hUnormal
  have hMnormalizesU :
      M ≤ Subgroup.normalizer (U : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hUM]
    exact hUnormal
  exact
    (le_inf hMnormalizesU
      Subgroup.le_normalizer_of_normal).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup U K)

/-- The source group `U K` is normal in the middle group `M K`. -/
theorem source_normal_in_middle :
    (hUM : U ≤ M) →
    (hUnormal : (U.subgroupOf M).Normal) →
    ((U ⊔ K : Subgroup G).subgroupOf
      (M ⊔ K : Subgroup G)).Normal := by
  intro hUM hUnormal
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact sup_le
    (M_le_normalizer_source K M U hUM hUnormal)
    (le_sup_right.trans Subgroup.le_normalizer)

/-- If `K ∩ M ≤ U`, then `(U K) ∩ M = U`. -/
theorem source_inf_M_eq
    (hUM : U ≤ M)
    (hKM : K ⊓ M ≤ U) :
    (U ⊔ K) ⊓ M = U := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, k, hk, huk⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hx.1
    have huM : u ∈ M := hUM hu
    have hkM : k ∈ M := by
      have hkEq : k = u⁻¹ * x := by
        rw [← huk]
        group
      rw [hkEq]
      exact M.mul_mem (M.inv_mem huM) hx.2
    rw [← huk]
    exact U.mul_mem hu (hKM ⟨hk, hkM⟩)
  · exact le_inf le_sup_left hUM

/-- The denominator cut out by `U K` inside `M` is exactly the internal
copy of `U`. -/
theorem source_subgroupOf_M_eq
    (hUM : U ≤ M)
    (hKM : K ⊓ M ≤ U) :
    (U ⊔ K).subgroupOf M = U.subgroupOf M := by
  apply Subgroup.subgroupOf_inj.mpr
  calc
    (U ⊔ K) ⊓ M = U :=
      source_inf_M_eq K M U hUM hKM
    _ = U ⊓ M := (inf_eq_left.mpr hUM).symm

/-- Adjoining `U K` to `M` gives the same middle group as adjoining
`K`, because `U ≤ M`. -/
theorem M_sup_source_eq_middle
    (hUM : U ≤ M) :
    M ⊔ (U ⊔ K) = M ⊔ K := by
  calc
    M ⊔ (U ⊔ K) = (M ⊔ U) ⊔ K := sup_assoc M U K |>.symm
    _ = M ⊔ K := by rw [sup_eq_left.mpr hUM]

/-- Noether's second isomorphism theorem transports cyclicity from
`M/U` to the printed middle quotient `M K / U K`. -/
theorem middle_quotient_isCyclic
    (hUM : U ≤ M)
    (hUnormal : (U.subgroupOf M).Normal)
    (hKM : K ⊓ M ≤ U)
    (hcyclic : IsCyclic (M ⧸ U.subgroupOf M)) :
    letI := source_normal_in_middle K M U hUM hUnormal
    IsCyclic
      ((M ⊔ K : Subgroup G) ⧸
        (U ⊔ K).subgroupOf (M ⊔ K : Subgroup G)) := by
  letI :
      ((U ⊔ K : Subgroup G).subgroupOf
        (M ⊔ K : Subgroup G)).Normal :=
    source_normal_in_middle K M U hUM hUnormal
  let hNormalizer :
      M ≤ Subgroup.normalizer ((U ⊔ K : Subgroup G) : Set G) :=
    M_le_normalizer_source K M U hUM hUnormal
  letI :
      ((U ⊔ K : Subgroup G).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNormalizer
  letI :
      ((U ⊔ K : Subgroup G).subgroupOf
        (M ⊔ (U ⊔ K) : Subgroup G)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hNormalizer
  let e :=
    QuotientGroup.quotientInfEquivProdNormalizerQuotient
      M (U ⊔ K : Subgroup G) hNormalizer
  have hleft :
      IsCyclic
        (M ⧸ (U ⊔ K : Subgroup G).subgroupOf M) := by
    exact
      (QuotientGroup.quotientMulEquivOfEq
        (source_subgroupOf_M_eq K M U hUM hKM)).isCyclic.mpr
          hcyclic
  have hright :
      IsCyclic
        ((M ⊔ (U ⊔ K) : Subgroup G) ⧸
          (U ⊔ K).subgroupOf
            (M ⊔ (U ⊔ K) : Subgroup G)) :=
    e.isCyclic.mp hleft
  let eMiddle :=
    QuotientGroup.equivQuotientSubgroupOfOfEq
      (A' := U ⊔ K) (B' := U ⊔ K)
      rfl (M_sup_source_eq_middle K M U hUM)
  exact eMiddle.isCyclic.mp hright

end SourceAndMiddle

section SelectedMiddleQuotient

variable (K M P : Subgroup G) [K.Normal]
variable
  (hM :
    M ≤ Subgroup.normalizer (P : Set G))
variable {L : Subgroup M}
variable
  (d :
    @OkuyamaWajimaCyclicQuotientSubgroup
      M P inferInstance inferInstance
      (OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        M P hM) L)

/-- If the ambient intersection `K ∩ M` consists of fixed points on
`P`, then the action-kernel inclusion `L ≤ d.U` puts that intersection
inside the selected ambient subgroup. -/
theorem kernel_inf_M_le_selectedAmbientSubgroup
    (hfixedM :
      K ⊓ Subgroup.centralizer (P : Set G) ≤ M)
    (hKMcentral :
      K ⊓ M ≤ K ⊓ Subgroup.centralizer (P : Set G))
    (hL :
      L =
        letI : MulDistribMulAction M P :=
          OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
            M P hM
        okuyamaWajimaActionKernel M P) :
    K ⊓ M ≤ selectedAmbientSubgroup M P hM d :=
  hKMcentral.trans
    (OkuyamaWajimaFullFixedCoordinates.fixedPoints_le_ambientSelectedSubgroup
      M P hM d K hfixedM hL)

/-- For the subgroup selected by Gorenstein, the cyclic quotient
`M / d.U` is exactly the printed cyclic quotient `M K / d.U K`. -/
theorem selected_middle_quotient_isCyclic
    (hKM : K ⊓ M ≤ selectedAmbientSubgroup M P hM d) :
    let U := selectedAmbientSubgroup M P hM d
    letI :=
      source_normal_in_middle K M U
        (OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_le_M
          M P hM d)
        (ambientSelectedSubgroup_normal_in_M M P hM d)
    IsCyclic
      ((M ⊔ K : Subgroup G) ⧸
        (U ⊔ K).subgroupOf (M ⊔ K : Subgroup G)) := by
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  let U := selectedAmbientSubgroup M P hM d
  have hUM : U ≤ M :=
    OkuyamaWajimaFullFixedCoordinates.ambientSelectedSubgroup_le_M
      M P hM d
  have hUnormal : (U.subgroupOf M).Normal :=
    ambientSelectedSubgroup_normal_in_M M P hM d
  letI : (U.subgroupOf M).Normal := hUnormal
  have hdenominator :
      U.subgroupOf M = d.U.toSubgroup := by
    simpa only [U, selectedSubgroupInM] using
      ambientSelectedSubgroup_subgroupOf_M_eq M P hM d
  have hcyclic :
      IsCyclic (M ⧸ U.subgroupOf M) :=
    (QuotientGroup.quotientMulEquivOfEq
      hdenominator).isCyclic.mpr d.quotient_isCyclic
  exact
    middle_quotient_isCyclic K M U hUM hUnormal hKM hcyclic

end SelectedMiddleQuotient

end OkuyamaWajimaFullFixedOuterCoordinates
end McKayConjecture
