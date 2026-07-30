/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaFullFixedBranch
import McKayConjecture.GroupTheory.OkuyamaWajimaComplement
import McKayConjecture.GroupTheory.OkuyamaWajimaCyclicQuotientSubgroup
import McKayConjecture.GroupTheory.OkuyamaWajimaQuotientIndex
import McKayConjecture.GroupTheory.QuotientEquivalenceTransport

/-!
# Coordinates for the full-fixed Okuyama--Wajima branch

In the full-fixed branch of the printed proof, the acting `p`-group is
`P`, the source group is `U ⊔ K`, and its normal subgroup is the internal
copy of `K`.  Full fixedness on `P / P'`, together with coprimeness, implies
that `U` centralizes `P`.  Consequently

* `P` acts by conjugation on `U ⊔ K`;
* `(U ⊔ K)^P` is canonically `U`;
* the fixed normal subgroup is canonically `C_K(P)` inside `U`; and
* `[U ⊔ K : K] = [U : C_K(P)]`.

This file formalizes every step after centralization.  The one unavailable
group-theoretic theorem is isolated as
`FullFixedCoprimeCentralizationInput`: it is precisely the coprime
Burnside-basis implication from full fixedness of `P / P'` to triviality
of the selected subgroup's action on `P`.

For the subgroup selected by
`OkuyamaWajimaCyclicQuotientSubgroup`, the ambient image is defined below.
The existing complement theorem
`fixedPoints_le_okuyamaWajimaAmbientComplement` supplies the hypothesis
that `C_K(P)` lies in the chosen `p`-complement.  The action-kernel
identity and `L ≤ U` then put `C_K(P)` inside the selected subgroup.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedCoordinates

variable {A : Type} [Group A]

/-- Conjugation by `P ≤ N_A(B)`, regarded as an action of `P` on `B`. -/
@[instance_reducible]
def normalizerConjugationAction
    (P B : Subgroup A)
    (hP : P ≤ Subgroup.normalizer (B : Set A)) :
    MulDistribMulAction P B :=
  MulDistribMulAction.compHom B
    (B.normalizerMonoidHom.comp (Subgroup.inclusion hP))

variable (P K U : Subgroup A) [K.Normal]

/-- If `U` centralizes `P`, then `P` normalizes the source product
`U ⊔ K`. -/
theorem actingSubgroup_le_normalizer_source
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A)) :
    P ≤ Subgroup.normalizer ((U ⊔ K : Subgroup A) : Set A) := by
  have hPU :
      P ≤ Subgroup.normalizer (U : Set A) :=
    (Subgroup.le_centralizer_iff.mp hcentral).trans
      (Subgroup.centralizer_le_normalizer (U : Set A))
  have hPK :
      P ≤ Subgroup.normalizer (K : Set A) :=
    Subgroup.le_normalizer_of_normal
  exact
    (le_inf hPU hPK).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup U K)

/-- Under the two printed containment conditions, the fixed elements of
`U ⊔ K` are exactly `U`. -/
theorem source_inf_centralizer_eq
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U) :
    (U ⊔ K) ⊓ Subgroup.centralizer (P : Set A) = U := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, k, hk, huk⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hx.1
    have huC :
        u ∈ Subgroup.centralizer (P : Set A) :=
      hcentral hu
    have hkEq : k = u⁻¹ * x := by
      rw [← huk]
      group
    have hkC :
        k ∈ Subgroup.centralizer (P : Set A) := by
      rw [hkEq]
      exact mul_mem (inv_mem huC) hx.2
    rw [← huk]
    exact U.mul_mem hu (hfixedU ⟨hk, hkC⟩)
  · exact le_inf le_sup_left hcentral

/-- The canonical identification `(U ⊔ K)^P ≃ U` for ambient
conjugation. -/
def sourceFixedPointsEquiv
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      normalizerConjugationAction P (U ⊔ K)
        (actingSubgroup_le_normalizer_source P K U hcentral)
    FixedPoints.subgroup P ↥(U ⊔ K : Subgroup A) ≃* U := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    normalizerConjugationAction P (U ⊔ K)
      (actingSubgroup_le_normalizer_source P K U hcentral)
  refine
    { toFun := fun x =>
        ⟨(x.1 : A), ?_⟩
      invFun := fun u =>
        ⟨⟨(u : A),
            (show U ≤ U ⊔ K from le_sup_left) u.2⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · have hxC :
        (x.1 : A) ∈
          Subgroup.centralizer (P : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hx :=
        congrArg Subtype.val (x.2 ⟨p, hp⟩)
      change p * (x.1 : A) * p⁻¹ = (x.1 : A) at hx
      calc
        p * (x.1 : A) =
            (p * (x.1 : A) * p⁻¹) * p := by group
        _ = (x.1 : A) * p := by rw [hx]
    have hx :
        (x.1 : A) ∈
          (U ⊔ K) ⊓
            Subgroup.centralizer (P : Set A) :=
      ⟨x.1.2, hxC⟩
    rw [source_inf_centralizer_eq
      P K U hcentral hfixedU] at hx
    exact hx
  · intro p
    apply Subtype.ext
    change (p : A) * (u : A) * (p : A)⁻¹ = (u : A)
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp (hcentral u.2)
        (p : A) p.2
    rw [hcomm]
    group
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro u
    apply Subtype.ext
    rfl
  · intro x y
    apply Subtype.ext
    rfl

/-- The internal copy of `K` in the source group `U ⊔ K`. -/
abbrev sourceNormal : Subgroup (U ⊔ K : Subgroup A) :=
  K.subgroupOf (U ⊔ K)

/-- The internal copy of the ambient normal subgroup is normal in the
source product. -/
theorem sourceNormal_normal :
    (sourceNormal K U).Normal :=
  (inferInstance : K.Normal).subgroupOf (U ⊔ K)

/-- Ambient conjugation by `P` on the internal copy of `K`. -/
@[instance_reducible]
def sourceNormalAction :
    MulDistribMulAction P (sourceNormal K U) := by
  let e : sourceNormal K U ≃* K :=
    Subgroup.subgroupOfEquivOfLe le_sup_right
  let aK : P →* MulAut K :=
    (MulAut.conjNormal (H := K)).comp P.subtype
  exact MulDistribMulAction.compHom (sourceNormal K U)
    ((MulAut.congr e).symm.toMonoidHom.comp aK)

/-- The internal normal-subgroup action is literal ambient
conjugation. -/
@[simp]
theorem sourceNormalAction_smul_coe
    (p : P) (k : sourceNormal K U) :
    letI := sourceNormalAction P K U
    (((p • k : sourceNormal K U) :
        (U ⊔ K : Subgroup A)) : A) =
      (p : A) * (k : A) * (p : A)⁻¹ := by
  letI := sourceNormalAction P K U
  rfl

/-- The actions on `K ≤ U ⊔ K` commute with the canonical inclusion. -/
theorem sourceNormalAction_compatible
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (p : P) (k : sourceNormal K U) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      normalizerConjugationAction P (U ⊔ K)
        (actingSubgroup_le_normalizer_source P K U hcentral)
    letI := sourceNormalAction P K U
    ((p • k : sourceNormal K U) :
        (U ⊔ K : Subgroup A)) =
      p • (k : (U ⊔ K : Subgroup A)) := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    normalizerConjugationAction P (U ⊔ K)
      (actingSubgroup_le_normalizer_source P K U hcentral)
  letI := sourceNormalAction P K U
  apply Subtype.ext
  rfl

/-- The copy of `C_K(P)` inside `U`. -/
abbrev internalFixedPoints :
    Subgroup U :=
  (K ⊓ Subgroup.centralizer (P : Set A)).subgroupOf U

/-- The literal fixed normal subgroup in Isaacs 13.29 is canonically the
copy of `C_K(P)` inside `U`. -/
def fixedNormalSubgroupEquivInternalFixedPoints
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      normalizerConjugationAction P (U ⊔ K)
        (actingSubgroup_le_normalizer_source P K U hcentral)
    letI := sourceNormalAction P K U
    McKayConjecture.IsaacsGlaubermanRestriction.fixedNormalSubgroup
        (S := P) (G := ↥(U ⊔ K : Subgroup A))
        (sourceNormal K U) ≃*
      internalFixedPoints P K U := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    normalizerConjugationAction P (U ⊔ K)
      (actingSubgroup_le_normalizer_source P K U hcentral)
  letI := sourceNormalAction P K U
  let e :=
    sourceFixedPointsEquiv P K U hcentral hfixedU
  refine
    { toFun := fun x =>
        ⟨e x.1, ?_⟩
      invFun := fun x =>
        ⟨e.symm x.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · exact ⟨x.2, hcentral (e x.1).2⟩
  · exact x.2.1
  · intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  · intro x
    apply Subtype.ext
    exact e.apply_symm_apply x.1
  · intro x y
    apply Subtype.ext
    exact e.map_mul x.1 y.1

/-- The fixed-normal-subgroup equivalence preserves the corresponding
subgroup indices. -/
theorem fixedNormalSubgroup_index_eq_internalFixedPoints_index
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      normalizerConjugationAction P (U ⊔ K)
        (actingSubgroup_le_normalizer_source P K U hcentral)
    letI := sourceNormalAction P K U
    (McKayConjecture.IsaacsGlaubermanRestriction.fixedNormalSubgroup
        (S := P) (G := ↥(U ⊔ K : Subgroup A))
        (sourceNormal K U)).index =
      (internalFixedPoints P K U).index := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    normalizerConjugationAction P (U ⊔ K)
      (actingSubgroup_le_normalizer_source P K U hcentral)
  letI := sourceNormalAction P K U
  let eG :=
    sourceFixedPointsEquiv P K U hcentral hfixedU
  let eN :=
    fixedNormalSubgroupEquivInternalFixedPoints
      P K U hcentral hfixedU
  letI :
      (internalFixedPoints P K U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((hcentral.trans
          (Subgroup.centralizer_le_normalizer
            (P : Set A))).trans
        (McKayConjecture.GroupTheory.normalizer_le_normalizer_inf_centralizer
          K P))
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact Nat.card_congr
    (McKayConjecture.GroupTheory.quotientMulEquivOfSubgroupEquiv
      eG eN (by ext x; rfl)).toEquiv

/-- Commutativity of `U / C_K(P)` transports to the literal target
quotient used by the generic full-fixed theorem. -/
theorem fixedNormalQuotient_isMulCommutative
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U)
    (hcomm :
      letI :
          (internalFixedPoints P K U).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer
          ((hcentral.trans
              (Subgroup.centralizer_le_normalizer
                (P : Set A))).trans
            (McKayConjecture.GroupTheory.normalizer_le_normalizer_inf_centralizer
              K P))
      IsMulCommutative
        (U ⧸ internalFixedPoints P K U)) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      normalizerConjugationAction P (U ⊔ K)
        (actingSubgroup_le_normalizer_source P K U hcentral)
    letI := sourceNormalAction P K U
    IsMulCommutative
      (FixedPoints.subgroup P ↥(U ⊔ K : Subgroup A) ⧸
        McKayConjecture.IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := ↥(U ⊔ K : Subgroup A))
          (sourceNormal K U)) := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    normalizerConjugationAction P (U ⊔ K)
      (actingSubgroup_le_normalizer_source P K U hcentral)
  letI := sourceNormalAction P K U
  let eG :=
    sourceFixedPointsEquiv P K U hcentral hfixedU
  let eN :=
    fixedNormalSubgroupEquivInternalFixedPoints
      P K U hcentral hfixedU
  letI :
      (internalFixedPoints P K U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((hcentral.trans
          (Subgroup.centralizer_le_normalizer
            (P : Set A))).trans
        (McKayConjecture.GroupTheory.normalizer_le_normalizer_inf_centralizer
          K P))
  let eQ :=
    McKayConjecture.GroupTheory.quotientMulEquivOfSubgroupEquiv
      eG eN (by ext x; rfl)
  rw [isMulCommutative_iff] at hcomm ⊢
  intro a b
  apply eQ.injective
  simpa only [map_mul] using hcomm (eQ a) (eQ b)

section FiniteCoordinates

variable [Finite A] {p : ℕ}

/-- The exact source/target index hypothesis of the generic full-fixed
theorem is automatic in the ambient coordinates. -/
theorem sourceNormal_index_eq_fixedNormalSubgroup_index
    (hP : IsPGroup p P)
    (hK : McKayConjecture.GroupTheory.IsPPrimeGroup p K)
    (hcentral :
      U ≤ Subgroup.centralizer (P : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U) :
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      normalizerConjugationAction P (U ⊔ K)
        (actingSubgroup_le_normalizer_source P K U hcentral)
    letI := sourceNormalAction P K U
    (sourceNormal K U).index =
      (McKayConjecture.IsaacsGlaubermanRestriction.fixedNormalSubgroup
        (S := P) (G := ↥(U ⊔ K : Subgroup A))
        (sourceNormal K U)).index := by
  letI :
      MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
    normalizerConjugationAction P (U ⊔ K)
      (actingSubgroup_le_normalizer_source P K U hcentral)
  letI := sourceNormalAction P K U
  calc
    (sourceNormal K U).index =
        (internalFixedPoints P K U).index :=
      McKayConjecture.GroupTheory.okuyamaWajima_kernel_index_eq_fixedPoints_index
        K P hP hK U
          (hcentral.trans
            (Subgroup.centralizer_le_normalizer (P : Set A)))
          hfixedU
    _ =
        (McKayConjecture.IsaacsGlaubermanRestriction.fixedNormalSubgroup
          (S := P) (G := ↥(U ⊔ K : Subgroup A))
          (sourceNormal K U)).index :=
      (fixedNormalSubgroup_index_eq_internalFixedPoints_index
        P K U hcentral hfixedU).symm

/-- The product `U ⊔ K` remains a `p'`-group when both factors are
`p'`-groups and `K` is normal. -/
theorem sourceGroup_isPPrime
    (hU :
      McKayConjecture.GroupTheory.IsPPrimeGroup p U)
    (hK :
      McKayConjecture.GroupTheory.IsPPrimeGroup p K) :
    McKayConjecture.GroupTheory.IsPPrimeGroup p
      (U ⊔ K : Subgroup A) :=
  (hU.mul_right hK).coprime_dvd_right
    (McKayConjecture.GroupTheory.card_sup_dvd_card_mul_card U K)

end FiniteCoordinates

section ComplementCoordinates

variable [Finite A]
variable {p : ℕ} [Fact p.Prime]

/-- The ambient Schur--Zassenhaus complement constructed for
Okuyama--Wajima is a `p'`-group. -/
theorem ambientComplement_isPPrime
    (S : Sylow p A)
    (K : Subgroup A) [K.Normal]
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup A)).Normal) :
    GroupTheory.IsPPrimeGroup p
      (GroupTheory.okuyamaWajimaAmbientComplement
        S K hK hKS) := by
  let H :=
    Subgroup.normalizer (((S : Subgroup A) : Set A))
  let D :=
    GroupTheory.okuyamaWajimaInternalFixedPoints
      K (S : Subgroup A)
  letI : D.Normal :=
    GroupTheory.internalFixedPoints_normal K (S : Subgroup A)
  let Pbar : Sylow p (H ⧸ D) :=
    GroupTheory.normalProductQuotientSylow D
      (GroupTheory.okuyamaWajimaSylowInNormalizer S)
  let Ubar : Subgroup (H ⧸ D) :=
    GroupTheory.okuyamaWajimaQuotientComplement
      S K hK hKS
  have hcomplement :
      (Pbar : Subgroup (H ⧸ D)).IsComplement' Ubar := by
    exact
      GroupTheory.okuyamaWajimaQuotientComplement_isComplement'
        S K hK hKS
  have hUbar :
      GroupTheory.IsPPrimeGroup p Ubar := by
    rw [GroupTheory.isPPrimeGroup_iff_not_dvd Fact.out]
    rw [← hcomplement.symm.index_eq_card]
    exact Pbar.not_dvd_index
  have hDambient :
      GroupTheory.IsPPrimeGroup p
        (GroupTheory.okuyamaWajimaFixedPoints
          K (S : Subgroup A)) :=
    (hK.to_subgroup
      ((GroupTheory.okuyamaWajimaFixedPoints
        K (S : Subgroup A)).subgroupOf K)).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (show
          GroupTheory.okuyamaWajimaFixedPoints
              K (S : Subgroup A) ≤ K from
          inf_le_left))
  have hD :
      GroupTheory.IsPPrimeGroup p D :=
    hDambient.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (show
          GroupTheory.okuyamaWajimaFixedPoints
              K (S : Subgroup A) ≤ H from
          inf_le_right.trans
            (Subgroup.centralizer_le_normalizer
              ((S : Subgroup A) : Set A)))).symm
  have hker :
      GroupTheory.IsPPrimeGroup p
        (QuotientGroup.mk' D).ker := by
    simpa only [QuotientGroup.ker_mk'] using hD
  have hlift :
      GroupTheory.IsPPrimeGroup p
        (GroupTheory.quotientComplementLift D Ubar) :=
    GroupTheory.IsPPrimeGroup.comap_of_surjective
      (QuotientGroup.mk' D)
      (QuotientGroup.mk'_surjective D)
      hker hUbar
  exact hlift.map H.subtype

end ComplementCoordinates

section CyclicQuotientSelection

variable (M P : Subgroup A)
variable
  (hMNormalizer :
    M ≤ Subgroup.normalizer (P : Set A))

/-- Conjugation in the selected complement action has its expected
ambient formula. -/
theorem selectedAction_smul_coe
    (m : M) (x : P) :
    letI : MulDistribMulAction M P :=
      normalizerConjugationAction M P hMNormalizer
    ((m • x : P) : A) =
      (m : A) * (x : A) * (m : A)⁻¹ := by
  letI : MulDistribMulAction M P :=
    normalizerConjugationAction M P hMNormalizer
  rfl

/-- The kernel of conjugation by `M ≤ N_A(P)` on `P` is the internal
copy of `C_M(P)`. -/
theorem selectedActionKernel_eq_centralizer_subgroupOf :
    letI : MulDistribMulAction M P :=
      normalizerConjugationAction M P hMNormalizer
    McKayConjecture.GroupTheory.okuyamaWajimaActionKernel M P =
      (Subgroup.centralizer (P : Set A)).subgroupOf M := by
  letI : MulDistribMulAction M P :=
    normalizerConjugationAction M P hMNormalizer
  ext m
  change
    MulDistribMulAction.toMulAut M P m = 1 ↔
      (m : A) ∈ Subgroup.centralizer (P : Set A)
  constructor
  · intro hm
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hfix :=
      congrArg
        (fun f : MulAut P => f ⟨x, hx⟩) hm
    have hfix' :=
      congrArg Subtype.val hfix
    change
      (m : A) * x * (m : A)⁻¹ = x at hfix'
    symm
    calc
      (m : A) * x =
          ((m : A) * x * (m : A)⁻¹) * (m : A) := by
            group
      _ = x * (m : A) := by rw [hfix']
  · intro hm
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change
      (m : A) * (x : A) * (m : A)⁻¹ =
        (x : A)
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp hm
        (x : A) x.2
    rw [← hcomm]
    group

variable {L : Subgroup M}
variable
  (d :
    @McKayConjecture.GroupTheory.OkuyamaWajimaCyclicQuotientSubgroup
      M P inferInstance inferInstance
      (normalizerConjugationAction M P hMNormalizer) L)

/-- The selected Gorenstein subgroup, mapped from `M` into the original
ambient group. -/
abbrev ambientSelectedSubgroup :
    Subgroup A := by
  letI : MulDistribMulAction M P :=
    normalizerConjugationAction M P hMNormalizer
  exact d.U.toSubgroup.map M.subtype

/-- The ambient selected subgroup is contained in the chosen
complement. -/
theorem ambientSelectedSubgroup_le_M :
    ambientSelectedSubgroup M P hMNormalizer d ≤ M :=
  by
    letI : MulDistribMulAction M P :=
      normalizerConjugationAction M P hMNormalizer
    exact
      (Subgroup.map_le_range M.subtype d.U.toSubgroup).trans_eq
        M.range_subtype

/-- The ambient selected subgroup normalizes `P`. -/
theorem ambientSelectedSubgroup_le_normalizer :
    ambientSelectedSubgroup M P hMNormalizer d ≤
      Subgroup.normalizer (P : Set A) :=
  (ambientSelectedSubgroup_le_M M P hMNormalizer d).trans
    hMNormalizer

/-- The ambient selected subgroup inherits the `p'` property from the
chosen complement. -/
theorem ambientSelectedSubgroup_isPPrime
    {p : ℕ}
    (hMPrime :
      McKayConjecture.GroupTheory.IsPPrimeGroup p M) :
    McKayConjecture.GroupTheory.IsPPrimeGroup p
      (ambientSelectedSubgroup M P hMNormalizer d) := by
  letI : MulDistribMulAction M P :=
    normalizerConjugationAction M P hMNormalizer
  exact
    (hMPrime.to_subgroup d.U.toSubgroup).map M.subtype

/-- The sole residual group-theoretic input in the full-fixed coordinate
step.

For a `p'`-group acting on a finite `p`-group, coprime
Burnside-basis theory says that full fixedness on `P / P'` makes the
selected subgroup act trivially on `P`. -/
def FullFixedCoprimeCentralizationInput
    {p : ℕ}
    (_hP : IsPGroup p P)
    (_hM :
      McKayConjecture.GroupTheory.IsPPrimeGroup p M)
    (_hfull :
      letI : MulDistribMulAction M P :=
        normalizerConjugationAction M P hMNormalizer
      d.fixedPoints = ⊤) :
    Prop :=
  letI : MulDistribMulAction M P :=
    normalizerConjugationAction M P hMNormalizer
  ∀ (u : d.U.toSubgroup) (x : P), (u.1 : M) • x = x

/-- The isolated Burnside-basis input says exactly that the ambient
selected subgroup centralizes `P`. -/
theorem ambientSelectedSubgroup_le_centralizer
    {p : ℕ}
    (hP : IsPGroup p P)
    (hMPrime :
      McKayConjecture.GroupTheory.IsPPrimeGroup p M)
    (hfull :
      letI : MulDistribMulAction M P :=
        normalizerConjugationAction M P hMNormalizer
      d.fixedPoints = ⊤)
    (hBurnside :
      FullFixedCoprimeCentralizationInput
        M P hMNormalizer d hP hMPrime hfull) :
    ambientSelectedSubgroup M P hMNormalizer d ≤
      Subgroup.centralizer (P : Set A) := by
  letI : MulDistribMulAction M P :=
    normalizerConjugationAction M P hMNormalizer
  rintro _ ⟨u, hu, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hfix :=
    congrArg Subtype.val
      (hBurnside ⟨u, hu⟩ ⟨x, hx⟩)
  change
    (u : A) * x * (u : A)⁻¹ = x at hfix
  symm
  calc
    (u : A) * x =
        ((u : A) * x * (u : A)⁻¹) * (u : A) := by
          group
    _ = x * (u : A) := by rw [hfix]

/-- If `C_K(P)` lies in the chosen complement, the action-kernel
identity and `L ≤ U` put it inside the selected Gorenstein subgroup. -/
theorem fixedPoints_le_ambientSelectedSubgroup
    (K : Subgroup A)
    (hfixedM :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ M)
    (hL :
      L =
        letI : MulDistribMulAction M P :=
          normalizerConjugationAction M P hMNormalizer
        McKayConjecture.GroupTheory.okuyamaWajimaActionKernel M P) :
    K ⊓ Subgroup.centralizer (P : Set A) ≤
      ambientSelectedSubgroup M P hMNormalizer d := by
  letI : MulDistribMulAction M P :=
    normalizerConjugationAction M P hMNormalizer
  intro x hx
  let xM : M := ⟨x, hfixedM hx⟩
  have hxKernel :
      xM ∈
        McKayConjecture.GroupTheory.okuyamaWajimaActionKernel M P := by
    rw [selectedActionKernel_eq_centralizer_subgroupOf
      M P hMNormalizer]
    exact hx.2
  have hxU :
      xM ∈ d.U.toSubgroup :=
    d.L_le_U (hL.symm ▸ hxKernel)
  exact ⟨xM, hxU, rfl⟩

/-- Source-faithful specialization of the fixed-group equivalence to the
subgroup selected by the Gorenstein step. -/
def selectedFullFixedSourceFixedPointsEquiv
    {p : ℕ}
    (K : Subgroup A) [K.Normal]
    (hP : IsPGroup p P)
    (hMPrime :
      McKayConjecture.GroupTheory.IsPPrimeGroup p M)
    (hfull :
      letI : MulDistribMulAction M P :=
        normalizerConjugationAction M P hMNormalizer
      d.fixedPoints = ⊤)
    (hBurnside :
      FullFixedCoprimeCentralizationInput
        M P hMNormalizer d hP hMPrime hfull)
    (hfixedM :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ M)
    (hL :
      L =
        letI : MulDistribMulAction M P :=
          normalizerConjugationAction M P hMNormalizer
        McKayConjecture.GroupTheory.okuyamaWajimaActionKernel M P) :
    let U := ambientSelectedSubgroup M P hMNormalizer d
    let hcentral :=
      ambientSelectedSubgroup_le_centralizer
        M P hMNormalizer d hP hMPrime hfull hBurnside
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      normalizerConjugationAction P (U ⊔ K)
        (actingSubgroup_le_normalizer_source P K U hcentral)
    FixedPoints.subgroup P ↥(U ⊔ K : Subgroup A) ≃* U := by
  let U := ambientSelectedSubgroup M P hMNormalizer d
  have hcentral :
      U ≤ Subgroup.centralizer (P : Set A) :=
    ambientSelectedSubgroup_le_centralizer
      M P hMNormalizer d hP hMPrime hfull hBurnside
  have hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U :=
    fixedPoints_le_ambientSelectedSubgroup
      M P hMNormalizer d K hfixedM hL
  exact sourceFixedPointsEquiv P K U hcentral hfixedU

/-- Source-faithful specialization of the full-fixed index equality to
the subgroup selected by the Gorenstein step. -/
theorem selectedFullFixed_index_eq
    [Finite A]
    {p : ℕ}
    (K : Subgroup A) [K.Normal]
    (hP : IsPGroup p P)
    (hK :
      McKayConjecture.GroupTheory.IsPPrimeGroup p K)
    (hMPrime :
      McKayConjecture.GroupTheory.IsPPrimeGroup p M)
    (hfull :
      letI : MulDistribMulAction M P :=
        normalizerConjugationAction M P hMNormalizer
      d.fixedPoints = ⊤)
    (hBurnside :
      FullFixedCoprimeCentralizationInput
        M P hMNormalizer d hP hMPrime hfull)
    (hfixedM :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ M)
    (hL :
      L =
        letI : MulDistribMulAction M P :=
          normalizerConjugationAction M P hMNormalizer
        McKayConjecture.GroupTheory.okuyamaWajimaActionKernel M P) :
    let U := ambientSelectedSubgroup M P hMNormalizer d
    let hcentral :=
      ambientSelectedSubgroup_le_centralizer
        M P hMNormalizer d hP hMPrime hfull hBurnside
    letI :
        MulDistribMulAction P ↥(U ⊔ K : Subgroup A) :=
      normalizerConjugationAction P (U ⊔ K)
        (actingSubgroup_le_normalizer_source P K U hcentral)
    letI := sourceNormalAction P K U
    (sourceNormal K U).index =
      (McKayConjecture.IsaacsGlaubermanRestriction.fixedNormalSubgroup
        (S := P) (G := ↥(U ⊔ K : Subgroup A))
        (sourceNormal K U)).index := by
  let U := ambientSelectedSubgroup M P hMNormalizer d
  have hcentral :
      U ≤ Subgroup.centralizer (P : Set A) :=
    ambientSelectedSubgroup_le_centralizer
      M P hMNormalizer d hP hMPrime hfull hBurnside
  have hfixedU :
      K ⊓ Subgroup.centralizer (P : Set A) ≤ U :=
    fixedPoints_le_ambientSelectedSubgroup
      M P hMNormalizer d K hfixedM hL
  exact
    sourceNormal_index_eq_fixedNormalSubgroup_index
      P K U hP hK hcentral hfixedU

end CyclicQuotientSelection

end OkuyamaWajimaFullFixedCoordinates
end McKayConjecture
