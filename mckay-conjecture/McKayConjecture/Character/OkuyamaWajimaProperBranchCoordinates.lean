/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaProperBranchRecursion
import McKayConjecture.GroupTheory.OkuyamaWajimaComplement
import McKayConjecture.GroupTheory.OkuyamaWajimaPrimeLocal

/-!
# Exact group coordinates for the proper Okuyama--Wajima branch

Let `K ◁ G` be a normal `p′`-subgroup, let `P` be a Sylow `p`-subgroup,
and assume that `K ⊔ P` is normal.  The lifted Schur--Zassenhaus subgroup

`M = okuyamaWajimaAmbientComplement P K hK hKP`

lies in `N_G(P)`, has `p′`-order, and contains `C_K(P)`.  Give `M` its
conjugation action on `P`.  If the Gorenstein construction selects the
proper fixed-point preimage `Q ≤ P`, normality of its selected subgroup
inside `M` makes `Q` stable under all of `M`.

This file proves the exact source coordinates for

`H = Q M K`.

In particular:

* `M ≤ N_G(Q)`;
* the canonical copy of `Q` is Sylow in `H`;
* `P ∩ H = Q`; and
* the literal set product `P H` is all of `G`.

No normality of `H` is assumed or proved.  The last statement is established
elementwise from the normal-product/complement decomposition, reordering
only elements of the normal subgroup `K`.
-/

noncomputable section

namespace McKayConjecture

open GroupTheory
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

section ComplementPrimeAway

variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)

/-- The lifted Okuyama--Wajima complement has order prime to `p`.

The quotient complement has cardinality equal to the index of the quotient
Sylow subgroup, hence is a `p′`-group.  Its full preimage has `p′` kernel
`C_K(P)`, and the ambient image is isomorphic to that full preimage. -/
theorem okuyamaWajimaAmbientComplement_isPPrimeGroup
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal) :
    IsPPrimeGroup p
      (okuyamaWajimaAmbientComplement P K hK hKP) := by
  let N := Subgroup.normalizer ((P : Subgroup G) : Set G)
  let D :=
    okuyamaWajimaInternalFixedPoints K (P : Subgroup G)
  letI : D.Normal :=
    internalFixedPoints_normal K (P : Subgroup G)
  let Pbar : Sylow p (N ⧸ D) :=
    normalProductQuotientSylow D
      (okuyamaWajimaSylowInNormalizer P)
  let Ubar : Subgroup (N ⧸ D) :=
    okuyamaWajimaQuotientComplement P K hK hKP
  have hcomplement : (Pbar : Subgroup (N ⧸ D)).IsComplement' Ubar := by
    simpa only [N, D, Pbar, Ubar] using
      okuyamaWajimaQuotientComplement_isComplement'
        P K hK hKP
  have hUbar : IsPPrimeGroup p Ubar := by
    rw [isPPrimeGroup_iff_not_dvd (G := Ubar) Fact.out]
    rw [← hcomplement.symm.index_eq_card]
    exact Pbar.not_dvd_index
  have hDambient :
      IsPPrimeGroup p
        (okuyamaWajimaFixedPoints K (P : Subgroup G)) := by
    let Dk :=
      (okuyamaWajimaFixedPoints
        K (P : Subgroup G)).subgroupOf K
    have hDk : IsPPrimeGroup p Dk :=
      hK.to_subgroup Dk
    exact
      hDk.of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (show
            okuyamaWajimaFixedPoints K (P : Subgroup G) ≤ K
            from inf_le_left))
  have hD : IsPPrimeGroup p D := by
    exact
      hDambient.of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (show
            okuyamaWajimaFixedPoints K (P : Subgroup G) ≤ N
            from
              inf_le_right.trans
                (Subgroup.centralizer_le_normalizer
                  ((P : Subgroup G) : Set G)))).symm
  have hLift :
      IsPPrimeGroup p
        (okuyamaWajimaComplement P K hK hKP) := by
    change
      IsPPrimeGroup p
        (Ubar.comap (QuotientGroup.mk' D))
    exact
      IsPPrimeGroup.comap_of_surjective
        (QuotientGroup.mk' D)
        (QuotientGroup.mk'_surjective D)
        (by
          simpa only [QuotientGroup.ker_mk'] using hD)
        hUbar
  exact
    hLift.of_equiv
      (okuyamaWajimaComplementEquivAmbientComplement
        P K hK hKP)

end ComplementPrimeAway

section ConjugationAction

variable (P M : Subgroup G)
variable
  (hM : M ≤ Subgroup.normalizer (P : Set G))

/-- Conjugation by a subgroup of `N_G(P)` on `P`. -/
@[instance_reducible]
def normalizingSubgroupConjugationAction :
    MulDistribMulAction M P :=
  MulDistribMulAction.compHom P
    (P.normalizerMonoidHom.comp (Subgroup.inclusion hM))

@[simp]
theorem normalizingSubgroupConjugationAction_smul_coe
    (m : M) (x : P) :
    letI := normalizingSubgroupConjugationAction P M hM
    ((m • x : P) : G) =
      (m : G) * (x : G) * (m : G)⁻¹ := by
  rfl

end ConjugationAction

section ProperCoordinates

variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

abbrev okuyamaWajimaProperBranchComplement :
    Subgroup G :=
  okuyamaWajimaAmbientComplement P K hK hKP

local instance properBranchComplementConjugationAction :
    MulDistribMulAction
      (okuyamaWajimaProperBranchComplement K P hK hKP)
      P :=
  normalizingSubgroupConjugationAction
    (P : Subgroup G)
    (okuyamaWajimaProperBranchComplement K P hK hKP)
    (okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP)

variable
  {L :
    Subgroup
      (okuyamaWajimaProperBranchComplement K P hK hKP)}

abbrev okuyamaWajimaProperBranchSelectedAmbientQ
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L) :
    Subgroup G :=
  okuyamaWajimaProperBranchQ P d.fixedPointPreimage

abbrev okuyamaWajimaProperBranchSelectedH
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L) :
    Subgroup G :=
  okuyamaWajimaProperBranchH
    K P d.fixedPointPreimage
      (okuyamaWajimaProperBranchComplement K P hK hKP)

/-- Stability of the Gorenstein fixed-point preimage under the whole
complement, expressed in ambient normalizer coordinates. -/
theorem properBranchComplement_le_selectedQ_normalizer
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L) :
    okuyamaWajimaProperBranchComplement K P hK hKP ≤
      Subgroup.normalizer
        (okuyamaWajimaProperBranchSelectedAmbientQ
          K P hK hKP d : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro m hm x hx
  obtain ⟨q, hq, rfl⟩ := hx
  let m' :
      okuyamaWajimaProperBranchComplement K P hK hKP :=
    ⟨m, hm⟩
  refine
    ⟨m' • q, d.smul_mem_fixedPointPreimage m' hq, ?_⟩
  exact
    normalizingSubgroupConjugationAction_smul_coe
      (P : Subgroup G)
      (okuyamaWajimaProperBranchComplement K P hK hKP)
      (okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP)
      m' q

/-- The selected ambient subgroup `Q` is a `p`-group. -/
theorem properBranchSelectedQ_isPGroup
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L) :
    IsPGroup p
      (okuyamaWajimaProperBranchSelectedAmbientQ
        K P hK hKP d) := by
  exact
    (P.isPGroup'.to_subgroup d.fixedPointPreimage).map
      (P : Subgroup G).subtype

/-- The canonical copy of the selected `Q` is Sylow in `H = Q M K`. -/
def okuyamaWajimaProperBranchSelectedSylowInH
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L) :
    Sylow p
      (okuyamaWajimaProperBranchSelectedH
        K P hK hKP d) := by
  let Q :=
    okuyamaWajimaProperBranchSelectedAmbientQ
      K P hK hKP d
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let H : Subgroup G := (Q ⊔ M) ⊔ K
  let H₀ : Subgroup G := K ⊔ (Q ⊔ M)
  have hQH : Q ≤ H :=
    le_sup_left.trans le_sup_left
  have hQinternal :
      IsPGroup p (Q.subgroupOf H) :=
    (properBranchSelectedQ_isPGroup
      K P hK hKP d).of_equiv
        (Subgroup.subgroupOfEquivOfLe hQH).symm
  let S₀ : Sylow p H₀ :=
    okuyamaWajimaSylowInPrimeAwayLocalProduct
      K Q M
      (properBranchSelectedQ_isPGroup
        K P hK hKP d)
      hK
      (okuyamaWajimaAmbientComplement_isPPrimeGroup
        K P hK hKP)
      (properBranchComplement_le_selectedQ_normalizer
        K P hK hKP d)
  have hnot₀ :
      ¬p ∣ (Q.subgroupOf H₀).index :=
    S₀.not_dvd_index
  have hH₀ : H₀ = H :=
    sup_comm K (Q ⊔ M)
  have hnot :
      ¬p ∣ (Q.subgroupOf H).index := by
    change ¬p ∣ Q.relIndex H₀ at hnot₀
    change ¬p ∣ Q.relIndex H
    rwa [hH₀] at hnot₀
  exact hQinternal.toSylow hnot

@[simp, norm_cast]
theorem coe_okuyamaWajimaProperBranchSelectedSylowInH
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L) :
    (okuyamaWajimaProperBranchSelectedSylowInH
        K P hK hKP d :
      Subgroup
        (okuyamaWajimaProperBranchSelectedH
          K P hK hKP d)) =
      (okuyamaWajimaProperBranchSelectedAmbientQ
        K P hK hKP d).subgroupOf
          (okuyamaWajimaProperBranchSelectedH
            K P hK hKP d) := by
  rfl

/-- The exact source intersection `P ∩ H = Q`.

The intersection is a `p`-subgroup of `H`, contains `Q`, and `Q` is Sylow
in `H`; Sylow maximality therefore forces equality. -/
theorem sylow_inf_properBranchSelectedH_eq_selectedQ
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L) :
    (P : Subgroup G) ⊓
        okuyamaWajimaProperBranchSelectedH
          K P hK hKP d =
      okuyamaWajimaProperBranchSelectedAmbientQ
        K P hK hKP d := by
  let Q :=
    okuyamaWajimaProperBranchSelectedAmbientQ
      K P hK hKP d
  let H :=
    okuyamaWajimaProperBranchSelectedH
      K P hK hKP d
  let R : Subgroup G := (P : Subgroup G) ⊓ H
  have hQH : Q ≤ H :=
    okuyamaWajimaProperBranchQ_le_H
      K P d.fixedPointPreimage
        (okuyamaWajimaProperBranchComplement K P hK hKP)
  have hQP : Q ≤ (P : Subgroup G) :=
    okuyamaWajimaProperBranchAmbientQ_le_P
      (P : Subgroup G) d.fixedPointPreimage
  have hQR : Q ≤ R :=
    le_inf hQP hQH
  have hR : IsPGroup p R := by
    let Ri : Subgroup P := R.subgroupOf (P : Subgroup G)
    have hRi : IsPGroup p Ri :=
      P.isPGroup'.to_subgroup Ri
    exact
      hRi.of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (show R ≤ (P : Subgroup G) from inf_le_left))
  let S : Sylow p H :=
    okuyamaWajimaProperBranchSelectedSylowInH
      K P hK hKP d
  let Ri : Subgroup H := R.subgroupOf H
  have hRi : IsPGroup p Ri :=
    hR.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (show R ≤ H from inf_le_right)).symm
  have hSleRi : (S : Subgroup H) ≤ Ri := by
    rw [show
      (S : Subgroup H) =
          Q.subgroupOf H by
        exact
          coe_okuyamaWajimaProperBranchSelectedSylowInH
            K P hK hKP d]
    exact Subgroup.subgroupOf_mono H hQR
  have hRiEq : Ri = (S : Subgroup H) :=
    S.is_maximal' hRi hSleRi
  have hmap :=
    congrArg (Subgroup.map H.subtype) hRiEq
  rw [Subgroup.map_subgroupOf_eq_of_le
      (show R ≤ H from inf_le_right),
    show
      (S : Subgroup H) =
          Q.subgroupOf H by
        exact
          coe_okuyamaWajimaProperBranchSelectedSylowInH
            K P hK hKP d,
    Subgroup.map_subgroupOf_eq_of_le hQH] at hmap
  exact hmap

/-- The literal source product `P H` is all of `G`.

The complement theorem first writes an arbitrary element as an element of
`K P` times an element of `M K`.  Normality of `K` then writes the first
factor in the order `P K`; the remaining `K`, `M`, and `K` factors all
belong to `H`. -/
theorem sylow_mul_properBranchSelectedH_eq_top
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L) :
    ((P : Subgroup G) : Set G) *
        (okuyamaWajimaProperBranchSelectedH
          K P hK hKP d : Set G) =
      (⊤ : Subgroup G) := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let H :=
    okuyamaWajimaProperBranchSelectedH
      K P hK hKP d
  apply Set.Subset.antisymm
  · intro x _hx
    trivial
  · intro g _hg
    have htop :
        (K ⊔ (P : Subgroup G)) ⊔ (M ⊔ K) =
          (⊤ : Subgroup G) := by
      simpa only [M] using
        normalProduct_sup_ambientComplement_sup_kernel_eq_top
          P K hK hKP
    have hgJoin :
        g ∈ (K ⊔ (P : Subgroup G)) ⊔ (M ⊔ K) := by
      rw [htop]
      trivial
    letI : (K ⊔ (P : Subgroup G)).Normal := hKP
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hgJoin
    have ha' : a ∈ (P : Subgroup G) ⊔ K := by
      simpa only [sup_comm] using ha
    obtain ⟨x, hxP, k, hkK, hxk⟩ :=
      Subgroup.mem_sup_of_normal_right.mp ha'
    have hkH : k ∈ H := by
      exact
        (okuyamaWajimaProperBranchK_le_H
          K P d.fixedPointPreimage M) hkK
    have hbH : b ∈ H := by
      exact
        (sup_le
          (okuyamaWajimaProperBranchM_le_H
            K P d.fixedPointPreimage M)
          (okuyamaWajimaProperBranchK_le_H
            K P d.fixedPointPreimage M)) hb
    refine ⟨x, hxP, k * b, H.mul_mem hkH hbH, ?_⟩
    rw [← hab, ← hxk]
    group

/-- The fully derived, source-correct proper-branch group scope for the
Gorenstein-selected subgroup and the canonical ambient complement. -/
def okuyamaWajimaProperBranchGroupScopeFromComplement
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup
        (okuyamaWajimaProperBranchComplement K P hK hKP)
        P L)
    (hproper : d.fixedPoints < ⊤) :
    OkuyamaWajimaProperBranchGroupScope
      K P d.fixedPointPreimage
        (okuyamaWajimaProperBranchComplement K P hK hKP) :=
  okuyamaWajimaProperBranchGroupScopeOfCyclicQuotient
    K P d hproper
    (okuyamaWajimaProperBranchComplement K P hK hKP)
    (properBranchComplement_le_selectedQ_normalizer
      K P hK hKP d)
    (sylow_inf_properBranchSelectedH_eq_selectedQ
      K P hK hKP d)
    (okuyamaWajimaProperBranchSelectedSylowInH
      K P hK hKP d)
    (coe_okuyamaWajimaProperBranchSelectedSylowInH
      K P hK hKP d)
    (sylow_mul_properBranchSelectedH_eq_top
      K P hK hKP d)

end ProperCoordinates

end McKayConjecture
