/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaFullFixedOuterIndex

/-!
# Quotient commutativity in the full-fixed Okuyama--Wajima branch

Let `M` be the canonical complement and let `U ≤ M` be the subgroup
selected by Gorenstein.  The printed commutator hypothesis and the exact
middle intersection give

`(U K)' ≤ G' ∩ M K ≤ K`.

Thus `(U K) / K` is commutative.  If `U` centralizes the Sylow subgroup
`P`, the internal copy of `K` in `U` is exactly `C_K(P)`, so
`U / C_K(P)` is commutative as well.  The latter transports to the
literal fixed-point quotient used by Isaacs 13.29.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedOuterCommutativity

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

/-- Every subgroup of the canonical middle group has commutator
contained in its internal copy of `K`. -/
theorem commutator_le_kernel_subgroupOf_of_le_middle
    (A : Subgroup G)
    (hA :
      A ≤
        OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
          K P hK hKP)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    _root_.commutator A ≤ K.subgroupOf A := by
  intro x hx
  have hxmap :
      ((x : A) : G) ∈
        (_root_.commutator A).map A.subtype :=
    Subgroup.mem_map_of_mem A.subtype hx
  rw [Subgroup.map_subtype_commutator] at hxmap
  have hxG :
      ((x : A) : G) ∈ _root_.commutator G :=
    (Subgroup.commutator_mono le_top le_top) hxmap
  have hxKP :
      ((x : A) : G) ∈ K ⊔ (P : Subgroup G) :=
    hcommutativeQuotient hxG
  have hxMiddle :
      ((x : A) : G) ∈
        OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
          K P hK hKP :=
    hA x.property
  have hxIntersection :
      ((x : A) : G) ∈
        (K ⊔ (P : Subgroup G)) ⊓
          OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
            K P hK hKP :=
    ⟨hxKP, hxMiddle⟩
  have hmiddleIntersection :
      (K ⊔ (P : Subgroup G)) ⊓
          OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
            K P hK hKP =
        K := by
    simpa only [
      OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle,
      okuyamaWajimaProperBranchComplement] using
        normalProduct_inf_ambientComplement_sup_kernel_eq_kernel
          P K hK hKP
  rw [hmiddleIntersection] at hxIntersection
  exact hxIntersection

/-- Quotient form of the preceding commutator containment. -/
theorem quotient_kernel_subgroupOf_isMulCommutative
    (A : Subgroup G)
    (hA :
      A ≤
        OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
          K P hK hKP)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    letI : (K.subgroupOf A).Normal :=
      (inferInstance : K.Normal).subgroupOf A
    IsMulCommutative (A ⧸ K.subgroupOf A) := by
  letI : (K.subgroupOf A).Normal :=
    (inferInstance : K.Normal).subgroupOf A
  exact
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      (commutator_le_kernel_subgroupOf_of_le_middle
        K P hK hKP A hA hcommutativeQuotient)

/-- If `U` centralizes `P`, its internal copy of `K` is literally the
copy of `C_K(P)`. -/
theorem kernel_subgroupOf_eq_internalFixedPoints
    (U : Subgroup G)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    K.subgroupOf U =
      OkuyamaWajimaFullFixedCoordinates.internalFixedPoints
        (P : Subgroup G) K U := by
  ext x
  change
    ((x : U) : G) ∈ K ↔
      ((x : U) : G) ∈
        K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)
  constructor
  · intro hx
    exact ⟨hx, hcentral x.property⟩
  · exact fun hx ↦ hx.1

/-- The selected source quotient `(U K) / K` is commutative whenever
`U ≤ M`. -/
theorem source_quotient_isMulCommutative
    (U : Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    letI :
        (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U).Normal :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormal_normal K U
    IsMulCommutative
      ((U ⊔ K : Subgroup G) ⧸
        OkuyamaWajimaFullFixedCoordinates.sourceNormal K U) := by
  let A := U ⊔ K
  have hA :
      A ≤
        OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
          K P hK hKP :=
    sup_le (hUM.trans le_sup_left) le_sup_right
  exact
    quotient_kernel_subgroupOf_isMulCommutative
      K P hK hKP A hA hcommutativeQuotient

/-- When `U` centralizes `P`, conjugation by `P` is trivial on the
source quotient `(U K) / K`. -/
theorem source_quotient_action_trivial
    (U : Subgroup G)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (s : P)
    (a : (U ⊔ K : Subgroup G)) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup G) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        (P : Subgroup G) (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            (P : Subgroup G) K U hcentral)
    let N :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
    QuotientGroup.mk' N (s • a) =
      QuotientGroup.mk' N a := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  let N :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal K U
  letI : N.Normal :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormal_normal K U
  apply (QuotientGroup.eq_iff_div_mem (N := N)).mpr
  change
    ((s : G) * (a : G) * (s : G)⁻¹) / (a : G) ∈ K
  obtain ⟨u, hu, k, hk, huk⟩ :=
    Subgroup.mem_sup_of_normal_right.mp a.property
  have hsu :
      (s : G) * u = u * (s : G) :=
    Subgroup.mem_centralizer_iff.mp (hcentral hu)
      (s : G) s.property
  have hconjugateK :
      (s : G) * k * (s : G)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem k hk (s : G)
  have hdelta :
      (s : G) * k * (s : G)⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem hconjugateK (K.inv_mem hk)
  have hconjugateDelta :
      u * ((s : G) * k * (s : G)⁻¹ * k⁻¹) * u⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem
      ((s : G) * k * (s : G)⁻¹ * k⁻¹)
      hdelta u
  rw [← huk, div_eq_mul_inv, mul_inv_rev]
  have heq :
      (s : G) * (u * k) * (s : G)⁻¹ * (k⁻¹ * u⁻¹) =
        u * ((s : G) * k * (s : G)⁻¹ * k⁻¹) * u⁻¹ := by
    rw [show
      (s : G) * (u * k) =
        u * ((s : G) * k) by
          rw [← mul_assoc, hsu, mul_assoc]]
    group
  rw [heq]
  exact hconjugateDelta

/-- Commutativity of `U / C_K(P)` in the full-fixed coordinates. -/
theorem target_coordinate_quotient_isMulCommutative
    (U : Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    letI :
        (OkuyamaWajimaFullFixedCoordinates.internalFixedPoints
          (P : Subgroup G) K U).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        ((hcentral.trans
            (Subgroup.centralizer_le_normalizer
              ((P : Subgroup G) : Set G))).trans
          (normalizer_le_normalizer_inf_centralizer
            K (P : Subgroup G)))
    IsMulCommutative
      (U ⧸
        OkuyamaWajimaFullFixedCoordinates.internalFixedPoints
          (P : Subgroup G) K U) := by
  letI : (K.subgroupOf U).Normal :=
    (inferInstance : K.Normal).subgroupOf U
  letI :
      (OkuyamaWajimaFullFixedCoordinates.internalFixedPoints
        (P : Subgroup G) K U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((hcentral.trans
          (Subgroup.centralizer_le_normalizer
            ((P : Subgroup G) : Set G))).trans
        (normalizer_le_normalizer_inf_centralizer
          K (P : Subgroup G)))
  have hU :
      U ≤
        OkuyamaWajimaFullFixedOuterIndex.okuyamaWajimaFullFixedMiddle
          K P hK hKP :=
    hUM.trans le_sup_left
  have hcomm :
      IsMulCommutative (U ⧸ K.subgroupOf U) :=
    quotient_kernel_subgroupOf_isMulCommutative
      K P hK hKP U hU hcommutativeQuotient
  let e :=
    QuotientGroup.quotientMulEquivOfEq
      (kernel_subgroupOf_eq_internalFixedPoints
        K P U hcentral)
  rw [isMulCommutative_iff] at hcomm ⊢
  intro a b
  apply e.symm.injective
  simpa only [map_mul] using hcomm (e.symm a) (e.symm b)

/-- Literal target-quotient form required by the automatic Isaacs 13.29
full-fixed theorem. -/
theorem fixed_target_quotient_isMulCommutative
    (U : Subgroup G)
    (hUM :
      U ≤ okuyamaWajimaProperBranchComplement K P hK hKP)
    (hcentral :
      U ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hfixedU :
      K ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ U)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup G) :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        (P : Subgroup G) (U ⊔ K)
          (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
            (P : Subgroup G) K U hcentral)
    letI :=
      OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
        (P : Subgroup G) K U
    IsMulCommutative
      (FixedPoints.subgroup P ↥(U ⊔ K : Subgroup G) ⧸
        IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := ↥(U ⊔ K : Subgroup G))
          (OkuyamaWajimaFullFixedCoordinates.sourceNormal K U)) := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup G) :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      (P : Subgroup G) (U ⊔ K)
        (OkuyamaWajimaFullFixedCoordinates.actingSubgroup_le_normalizer_source
          (P : Subgroup G) K U hcentral)
  letI :=
    OkuyamaWajimaFullFixedCoordinates.sourceNormalAction
      (P : Subgroup G) K U
  apply
    OkuyamaWajimaFullFixedCoordinates.fixedNormalQuotient_isMulCommutative
      (P : Subgroup G) K U hcentral hfixedU
  exact
    target_coordinate_quotient_isMulCommutative
      K P hK hKP U hUM hcentral hcommutativeQuotient

end OkuyamaWajimaFullFixedOuterCommutativity
end McKayConjecture
