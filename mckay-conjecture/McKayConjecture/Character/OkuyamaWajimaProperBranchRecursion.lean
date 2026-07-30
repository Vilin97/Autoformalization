/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NavarroGeneralLocalGlobalExtension
import McKayConjecture.Character.OkuyamaWajimaGlaubermanTransitivity
import McKayConjecture.GroupTheory.SubgroupProductIndex

/-!
# The recursive proper branch in the printed Okuyama--Wajima proof

This file packages the proper-fixed-point branch on pages 803--804 of
Okuyama--Wajima.  If

* `P` is the Sylow `p`-subgroup;
* `Q ◁ P` is the proper nontrivial subgroup selected by the Gorenstein
  fixed-point construction;
* `M` is the chosen `p`-complement in `N_G(P)`; and
* `K` is the normal `p'`-kernel,

the smaller subgroup problem is posed on

`H = Q M K`,

while the smaller quotient problem is posed on

`N_G(Q) / Q`.

The implementation deliberately keeps all subgroup changes canonical.
The normalizer computed inside `H` is identified with the corresponding
ambient intersection, rather than asserted to be definitionally equal to
it.  Likewise, the characters in the two recursive problems are packaged
as character triples on the relevant subtype groups.

The existing strong Glauberman transitivity theorem supplies the important
character compatibility:

* the first-stage character is the ordinary `Q`-correspondent and is
  `N_G(Q)`-invariant; and
* its `(P / Q)`-correspondent is the ordinary `P`-correspondent.

Only the two genuine recursive conclusions remain visible in the final
extension theorem.

1. the induction conclusion for `N_G(Q) / Q`;
2. the induction conclusion for `H`.

The elementary index divisibilities are derived from the group scope,
without assuming that `H` is normal.  The source set-product equality
`G = P H` identifies `[G : H]` with `[P : Q]`.  Since
`P ≤ N_G(Q)`, the same coset calculation identifies

`[N_G(Q) : N_H(Q)] = [G : H]`.

The existing general Navarro API then proves both ascent equivalences,
replacing the invocation of Isaacs, Corollary 11.31 in the printed proof.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open CliffordCorrespondence
open GroupTheory
open scoped Pointwise

section SubgroupCoordinates

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]
variable (M : Subgroup G)

/-- The proper-branch subgroup `Q`, in the original ambient group. -/
abbrev okuyamaWajimaProperBranchQ :
    Subgroup G :=
  okuyamaWajimaProperBranchAmbientQ (P : Subgroup G) Q

/-- The subgroup `H = Q M K` used for the second recursive call. -/
abbrev okuyamaWajimaProperBranchH :
    Subgroup G :=
  (okuyamaWajimaProperBranchQ P Q ⊔ M) ⊔ K

/-- The intermediate fixed-point kernel `J = C_K(Q)`. -/
abbrev okuyamaWajimaProperBranchJ :
    Subgroup G :=
  coprimeFixedPoints K (okuyamaWajimaProperBranchQ P Q)

/-- The ambient normalizer `N_G(Q)`. -/
abbrev okuyamaWajimaProperBranchQNormalizer :
    Subgroup G :=
  Subgroup.normalizer
    (okuyamaWajimaProperBranchQ P Q : Set G)

/-- The copy of `Q` inside `N_G(Q)`, used as the kernel of the first
recursive quotient. -/
abbrev okuyamaWajimaProperBranchQInNormalizer :
    Subgroup (okuyamaWajimaProperBranchQNormalizer P Q) :=
  (okuyamaWajimaProperBranchQ P Q).subgroupOf
    (okuyamaWajimaProperBranchQNormalizer P Q)

/-- The first smaller ambient group, in its literal quotient coordinates. -/
abbrev okuyamaWajimaProperBranchNormalizerQuotient :=
  okuyamaWajimaProperBranchQNormalizer P Q ⧸
    okuyamaWajimaProperBranchQInNormalizer P Q

/-- The ambient image of `N_H(Q)`, represented as the exact intersection
`H ∩ N_G(Q)`. -/
abbrev okuyamaWajimaProperBranchHNormalizerImage :
    Subgroup G :=
  okuyamaWajimaProperBranchH K P Q M ⊓
    okuyamaWajimaProperBranchQNormalizer P Q

/-- The image of `N_H(Q)` regarded as an intermediate subgroup of
`N_G(Q)`. -/
abbrev okuyamaWajimaProperBranchHNormalizerInQNormalizer :
    Subgroup (okuyamaWajimaProperBranchQNormalizer P Q) :=
  (okuyamaWajimaProperBranchHNormalizerImage K P Q M).subgroupOf
    (okuyamaWajimaProperBranchQNormalizer P Q)

omit [Finite G] [Fact p.Prime] [K.Normal] [Q.Normal] in
/-- The ambient copy of `Q` lies in `H = Q M K`. -/
theorem okuyamaWajimaProperBranchQ_le_H :
    okuyamaWajimaProperBranchQ P Q ≤
      okuyamaWajimaProperBranchH K P Q M :=
  le_sup_left.trans le_sup_left

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- Normality of `Q` inside `P` puts the ambient Sylow subgroup inside
`N_G(Q)`. -/
theorem okuyamaWajimaProperBranchP_le_QNormalizer :
    (P : Subgroup G) ≤
      okuyamaWajimaProperBranchQNormalizer P Q := by
  have hQP :
      okuyamaWajimaProperBranchQ P Q ≤
        (P : Subgroup G) :=
    okuyamaWajimaProperBranchAmbientQ_le_P
      (P : Subgroup G) Q
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hQP]
  have hcopy :
      (okuyamaWajimaProperBranchQ P Q).subgroupOf
          (P : Subgroup G) =
        Q := by
    ext x
    constructor
    · rintro ⟨q, hq, hqx⟩
      have hqxeq : q = x := by
        apply Subtype.ext
        exact hqx
      simpa [hqxeq] using hq
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hcopy]
  infer_instance

/-- `P`, regarded as a Sylow subgroup of `N_G(Q)`. -/
def okuyamaWajimaProperBranchSylowInQNormalizer :
    Sylow p (okuyamaWajimaProperBranchQNormalizer P Q) :=
  P.subtype
    (okuyamaWajimaProperBranchP_le_QNormalizer P Q)

/-- The Sylow subgroup `P / Q` of the first recursive quotient
`N_G(Q) / Q`. -/
def okuyamaWajimaProperBranchQuotientSylow :
    Sylow p
      (okuyamaWajimaProperBranchNormalizerQuotient P Q) :=
  (okuyamaWajimaProperBranchSylowInQNormalizer P Q).mapQuotient
    (okuyamaWajimaProperBranchQInNormalizer P Q)

omit [Finite G] [Fact p.Prime] [Q.Normal] in
/-- The normal `p'`-kernel lies in `H = Q M K`. -/
theorem okuyamaWajimaProperBranchK_le_H :
    K ≤ okuyamaWajimaProperBranchH K P Q M :=
  le_sup_right

omit [Finite G] [Fact p.Prime] [K.Normal] [Q.Normal] in
/-- The complement lies in `H = Q M K`. -/
theorem okuyamaWajimaProperBranchM_le_H :
    M ≤ okuyamaWajimaProperBranchH K P Q M :=
  le_sup_right.trans le_sup_left

omit [Finite G] [Fact p.Prime] [Q.Normal] in
/-- The intermediate fixed-point kernel lies in `H`. -/
theorem okuyamaWajimaProperBranchJ_le_H :
    okuyamaWajimaProperBranchJ K P Q ≤
      okuyamaWajimaProperBranchH K P Q M :=
  inf_le_left.trans
    (okuyamaWajimaProperBranchK_le_H K P Q M)

omit [Finite G] [Fact p.Prime] [K.Normal] [Q.Normal] in
/-- The fixed-point kernel centralizes `Q`, hence lies in `N_G(Q)`. -/
theorem okuyamaWajimaProperBranchJ_le_QNormalizer :
    okuyamaWajimaProperBranchJ K P Q ≤
      okuyamaWajimaProperBranchQNormalizer P Q :=
  inf_le_right.trans
    (Subgroup.centralizer_le_normalizer
      (okuyamaWajimaProperBranchQ P Q : Set G))

omit [Finite G] [Fact p.Prime] [Q.Normal] in
/-- The fixed-point kernel lies in the exact intermediate copy of
`N_H(Q) ≤ N_G(Q)`. -/
theorem okuyamaWajimaProperBranchJ_le_HNormalizerImage :
    okuyamaWajimaProperBranchJ K P Q ≤
      okuyamaWajimaProperBranchHNormalizerImage K P Q M :=
  le_inf
    (okuyamaWajimaProperBranchJ_le_H K P Q M)
    (okuyamaWajimaProperBranchJ_le_QNormalizer K P Q)

omit [Finite G] [Fact p.Prime] [K.Normal] [Q.Normal] in
/-- The normalizer computed internally in `H` is the canonical subgroup-of
copy of the ambient normalizer. -/
theorem okuyamaWajimaProperBranch_normalizerInH_eq :
    Subgroup.normalizer
        (((okuyamaWajimaProperBranchQ P Q).subgroupOf
          (okuyamaWajimaProperBranchH K P Q M) :
            Subgroup (okuyamaWajimaProperBranchH K P Q M)) :
          Set (okuyamaWajimaProperBranchH K P Q M)) =
      (okuyamaWajimaProperBranchQNormalizer P Q).subgroupOf
        (okuyamaWajimaProperBranchH K P Q M) := by
  exact
    (Subgroup.subgroupOf_normalizer_eq
      (okuyamaWajimaProperBranchQ_le_H K P Q M)).symm

omit [Finite G] [Fact p.Prime] [K.Normal] [Q.Normal] in
/-- Canonical equivalence from the normalizer computed internally in `H`
to its ambient intersection image.

This is the coordinate change used for `N_H(Q)`; no equality between the
two subtype groups is assumed. -/
def okuyamaWajimaProperBranchNormalizerInHEquivImage :
    Subgroup.normalizer
        (((okuyamaWajimaProperBranchQ P Q).subgroupOf
          (okuyamaWajimaProperBranchH K P Q M) :
            Subgroup (okuyamaWajimaProperBranchH K P Q M)) :
          Set (okuyamaWajimaProperBranchH K P Q M)) ≃*
      okuyamaWajimaProperBranchHNormalizerImage K P Q M where
  toFun x :=
    ⟨((x :
        okuyamaWajimaProperBranchH K P Q M) : G),
      ⟨x.1.2, by
        have hx :
            x.1 ∈
              (okuyamaWajimaProperBranchQNormalizer P Q).subgroupOf
                (okuyamaWajimaProperBranchH K P Q M) := by
          rw [← okuyamaWajimaProperBranch_normalizerInH_eq
            K P Q M]
          exact x.2
        exact hx⟩⟩
  invFun y :=
    ⟨⟨(y : G), y.2.1⟩, by
      rw [okuyamaWajimaProperBranch_normalizerInH_eq
        K P Q M]
      exact y.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

omit [Finite G] [Fact p.Prime] [K.Normal] [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchNormalizerInHEquivImage_apply_coe
    (x :
      Subgroup.normalizer
        (((okuyamaWajimaProperBranchQ P Q).subgroupOf
          (okuyamaWajimaProperBranchH K P Q M) :
            Subgroup (okuyamaWajimaProperBranchH K P Q M)) :
          Set (okuyamaWajimaProperBranchH K P Q M))) :
    ((okuyamaWajimaProperBranchNormalizerInHEquivImage
      K P Q M x :
        okuyamaWajimaProperBranchHNormalizerImage K P Q M) : G) =
      ((x : okuyamaWajimaProperBranchH K P Q M) : G) :=
  rfl

omit [Fact p.Prime] [K.Normal] [Q.Normal] in
/-- A nontrivial internal subgroup `Q ≤ P` has a nontrivial ambient copy. -/
theorem okuyamaWajimaProperBranchQ_ne_bot_of_internal
    (hQ : Q ≠ ⊥) :
    okuyamaWajimaProperBranchQ P Q ≠ ⊥ := by
  intro hambient
  have hle :
      Q ≤ (P : Subgroup G).subtype.ker := by
    exact
      (Subgroup.map_eq_bot_iff Q).mp hambient
  rw [Subgroup.ker_subtype] at hle
  exact hQ (bot_unique hle)

omit [Fact p.Prime] [K.Normal] [Q.Normal] in
/-- A proper internal subgroup `Q < P` has an ambient copy strictly below
the ambient Sylow subgroup. -/
theorem okuyamaWajimaProperBranchQ_lt_sylow_of_internal
    (hQ : Q < ⊤) :
    okuyamaWajimaProperBranchQ P Q < (P : Subgroup G) := by
  have hmap :
      Q.map (P : Subgroup G).subtype <
        (⊤ : Subgroup P).map (P : Subgroup G).subtype :=
    (Subgroup.map_lt_map_iff_of_injective
      (P : Subgroup G).subtype_injective).mpr hQ
  simpa only [okuyamaWajimaProperBranchQ,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hmap

/-- A formalization-friendly bundle of the proper-branch subgroup facts
needed by the two recursive calls and prime-power ascent. -/
structure OkuyamaWajimaProperBranchGroupScope where
  /-- `Q` is nontrivial. -/
  q_ne_bot :
    okuyamaWajimaProperBranchQ P Q ≠ ⊥
  /-- `Q` is proper in `P`. -/
  q_lt_sylow :
    okuyamaWajimaProperBranchQ P Q < (P : Subgroup G)
  /-- The complement normalizes `Q`. -/
  complement_le_normalizer :
    M ≤ okuyamaWajimaProperBranchQNormalizer P Q
  /-- The source-theoretic intersection `P ∩ H = Q`. -/
  sylow_inf_H_eq :
    (P : Subgroup G) ⊓
        okuyamaWajimaProperBranchH K P Q M =
      okuyamaWajimaProperBranchQ P Q
  /-- The chosen copy of `Q` is Sylow in the recursive group `H`. -/
  sylowInH :
    Sylow p (okuyamaWajimaProperBranchH K P Q M)
  /-- The recursive Sylow subgroup is literally the internal copy of
  the selected ambient subgroup `Q`. -/
  coe_sylowInH :
    (sylowInH : Subgroup
        (okuyamaWajimaProperBranchH K P Q M)) =
      (okuyamaWajimaProperBranchQ P Q).subgroupOf
        (okuyamaWajimaProperBranchH K P Q M)
  /-- The exact source product coordinate `G = P H`, stated as a set
  product so that no normality of `H` is smuggled into the argument. -/
  sylow_mul_H_eq_top :
    ((P : Subgroup G) : Set G) *
        (okuyamaWajimaProperBranchH K P Q M : Set G) =
      (⊤ : Subgroup G)

namespace OkuyamaWajimaProperBranchGroupScope

variable {K P Q M}

/-- Build the ambient recursive scope from the corresponding internal
proper/nontrivial statements on `Q ≤ P`. -/
def of_internal
    (hQnontrivial : Q ≠ ⊥)
    (hQproper : Q < ⊤)
    (hM :
      M ≤ okuyamaWajimaProperBranchQNormalizer P Q)
    (hinter :
      (P : Subgroup G) ⊓
          okuyamaWajimaProperBranchH K P Q M =
        okuyamaWajimaProperBranchQ P Q)
    (sylowH :
      Sylow p (okuyamaWajimaProperBranchH K P Q M))
    (hsylowH :
      (sylowH : Subgroup
          (okuyamaWajimaProperBranchH K P Q M)) =
        (okuyamaWajimaProperBranchQ P Q).subgroupOf
          (okuyamaWajimaProperBranchH K P Q M))
    (hproduct :
      ((P : Subgroup G) : Set G) *
          (okuyamaWajimaProperBranchH K P Q M : Set G) =
        (⊤ : Subgroup G)) :
    OkuyamaWajimaProperBranchGroupScope K P Q M where
  q_ne_bot :=
    okuyamaWajimaProperBranchQ_ne_bot_of_internal
      P Q hQnontrivial
  q_lt_sylow :=
    okuyamaWajimaProperBranchQ_lt_sylow_of_internal
      P Q hQproper
  complement_le_normalizer := hM
  sylow_inf_H_eq := hinter
  sylowInH := sylowH
  coe_sylowInH := hsylowH
  sylow_mul_H_eq_top := hproduct

omit [Fact p.Prime] in
/-- The proper-branch subgroup `H` is genuinely proper. -/
theorem H_lt_top
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    okuyamaWajimaProperBranchH K P Q M < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hPQ :
      (P : Subgroup G) =
        okuyamaWajimaProperBranchQ P Q := by
    calc
      (P : Subgroup G) =
          (P : Subgroup G) ⊓
            okuyamaWajimaProperBranchH K P Q M := by
        rw [htop, inf_top_eq]
      _ = okuyamaWajimaProperBranchQ P Q :=
        scope.sylow_inf_H_eq
  exact scope.q_lt_sylow.ne hPQ.symm

/-- Therefore the recursive call on `H` is available to strong induction
on the ambient group order. -/
theorem H_card_lt
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    Nat.card (okuyamaWajimaProperBranchH K P Q M) <
      Nat.card G := by
  obtain ⟨x, _hxG, hxH⟩ :=
    SetLike.exists_of_lt scope.H_lt_top
  exact Finite.card_subtype_lt hxH

/-- The copy of a nontrivial `Q` inside its normalizer is nontrivial. -/
theorem qInNormalizer_ne_bot
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    okuyamaWajimaProperBranchQInNormalizer P Q ≠ ⊥ := by
  intro hbot
  have hmap :=
    congrArg
      (Subgroup.map
        (okuyamaWajimaProperBranchQNormalizer P Q).subtype)
      hbot
  rw [Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer,
    Subgroup.map_bot] at hmap
  exact scope.q_ne_bot hmap

/-- The quotient `N_G(Q) / Q` has smaller order than `N_G(Q)`. -/
theorem normalizerQuotient_card_lt_normalizer
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    Nat.card
        (okuyamaWajimaProperBranchNormalizerQuotient P Q) <
      Nat.card (okuyamaWajimaProperBranchQNormalizer P Q) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (okuyamaWajimaProperBranchQInNormalizer P Q)]
  exact
    lt_mul_of_one_lt_right Nat.card_pos
      ((okuyamaWajimaProperBranchQInNormalizer P Q).one_lt_card_iff_ne_bot.mpr
        scope.qInNormalizer_ne_bot)

/-- Consequently `N_G(Q) / Q` is a valid strictly smaller induction
argument even when `N_G(Q)` itself is all of `G`. -/
theorem normalizerQuotient_card_lt
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    Nat.card
        (okuyamaWajimaProperBranchNormalizerQuotient P Q) <
      Nat.card G :=
  scope.normalizerQuotient_card_lt_normalizer.trans_le
    (okuyamaWajimaProperBranchQNormalizer P Q).card_le_card_group

/-- Both recursive ambient groups satisfy the strict-cardinality side
condition of strong induction. -/
theorem recursive_cardinalities_lt
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    Nat.card
          (okuyamaWajimaProperBranchNormalizerQuotient P Q) <
        Nat.card G ∧
      Nat.card (okuyamaWajimaProperBranchH K P Q M) <
        Nat.card G :=
  ⟨scope.normalizerQuotient_card_lt, scope.H_card_lt⟩

/-- Mapping the recursive Sylow subgroup back to `G` recovers the chosen
ambient copy of `Q`. -/
@[simp]
theorem ambientSubgroup_sylowInH
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    Sylow.ambientSubgroup scope.sylowInH =
      okuyamaWajimaProperBranchQ P Q := by
  rw [Sylow.ambientSubgroup, scope.coe_sylowInH]
  exact
    Subgroup.map_subgroupOf_eq_of_le
      (okuyamaWajimaProperBranchQ_le_H K P Q M)

/-- The set-product coset equivalence gives the exact equality between
the two indices occurring in prime-power ascent.  No normality of `H` is
required. -/
theorem normalizerIndex_eq_H_index
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    (okuyamaWajimaProperBranchHNormalizerInQNormalizer
      K P Q M).index =
      (okuyamaWajimaProperBranchH K P Q M).index := by
  let H := okuyamaWajimaProperBranchH K P Q M
  let NQ := okuyamaWajimaProperBranchQNormalizer P Q
  have hproduct :
      (NQ : Set G) * (H : Set G) =
        (⊤ : Subgroup G) := by
    apply Set.Subset.antisymm
    · intro x _hx
      trivial
    · rw [← scope.sylow_mul_H_eq_top]
      exact
        Set.mul_subset_mul
          (SetLike.coe_mono
            (okuyamaWajimaProperBranchP_le_QNormalizer
              P Q))
          (by rfl)
  have hindex :
      (okuyamaWajimaProperBranchH K P Q M).index =
        (okuyamaWajimaProperBranchH K P Q M).relIndex
          (okuyamaWajimaProperBranchQNormalizer P Q) :=
    index_eq_relIndex_of_mul_eq_top H NQ hproduct
  change
    (okuyamaWajimaProperBranchHNormalizerImage
        K P Q M).relIndex
        (okuyamaWajimaProperBranchQNormalizer P Q) =
      (okuyamaWajimaProperBranchH K P Q M).index
  rw [Subgroup.inf_relIndex_right]
  exact hindex.symm

/-- The source product/intersection coordinates identify
`[G : H] = [P : Q]`; hence the ambient index is a power of `p`. -/
theorem ambientIndex_dvd_prime_power
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    ∃ n : ℕ,
      (okuyamaWajimaProperBranchH K P Q M).index ∣
        p ^ n := by
  let H := okuyamaWajimaProperBranchH K P Q M
  have hInternal :
      H.subgroupOf (P : Subgroup G) = Q := by
    ext x
    have hmem :=
      congrArg
        (fun S : Subgroup G => ((x : G) ∈ S))
        scope.sylow_inf_H_eq
    change ((x : G) ∈ H) ↔ x ∈ Q
    have hmem' :
        ((x : G) ∈ H) =
          ((x : G) ∈
            okuyamaWajimaProperBranchQ P Q) := by
      simpa only [Subgroup.mem_inf, x.2, true_and] using hmem
    rw [hmem']
    constructor
    · rintro ⟨q, hq, hqx⟩
      have hqxeq : q = x := by
        apply Subtype.ext
        exact hqx
      simpa [hqxeq] using hq
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hindex :
      H.index = Q.index := by
    calc
      H.index = H.relIndex (P : Subgroup G) :=
        index_eq_relIndex_of_mul_eq_top
          H (P : Subgroup G) scope.sylow_mul_H_eq_top
      _ = Q.index := by
        rw [Subgroup.relIndex, hInternal]
  obtain ⟨n, hn⟩ :=
    IsPGroup.iff_card.mp
      (P.isPGroup'.to_quotient Q)
  refine ⟨n, ?_⟩
  rw [hindex, Subgroup.index_eq_card, hn]

/-- The recursive group has the printed product form
`H = K N_H(Q)`, stated internally as a supremum equal to top. -/
theorem kernel_sup_normalizerInH_eq_top
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    K.subgroupOf (okuyamaWajimaProperBranchH K P Q M) ⊔
        Subgroup.normalizer
          ((scope.sylowInH : Subgroup
            (okuyamaWajimaProperBranchH K P Q M)) :
              Set (okuyamaWajimaProperBranchH K P Q M)) =
      ⊤ := by
  let H := okuyamaWajimaProperBranchH K P Q M
  let QA := okuyamaWajimaProperBranchQ P Q
  let NQ := okuyamaWajimaProperBranchQNormalizer P Q
  have hQMH : QA ⊔ M ≤ H :=
    le_sup_left
  have hKH : K ≤ H :=
    okuyamaWajimaProperBranchK_le_H K P Q M
  have hQMNormalizer :
      (QA ⊔ M).subgroupOf H ≤
        Subgroup.normalizer
          (((QA.subgroupOf H : Subgroup H)) : Set H) := by
    rw [okuyamaWajimaProperBranch_normalizerInH_eq
      K P Q M]
    intro x hx
    exact
      (sup_le Subgroup.le_normalizer
        scope.complement_le_normalizer) hx
  have hgen :
      (QA ⊔ M).subgroupOf H ⊔ K.subgroupOf H =
        ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQMH hKH]
    exact Subgroup.subgroupOf_self _
  rw [scope.coe_sylowInH]
  apply top_unique
  rw [← hgen]
  exact sup_le
    (hQMNormalizer.trans le_sup_right)
    le_sup_left

end OkuyamaWajimaProperBranchGroupScope

section GorensteinSelectedSubgroup

variable {Act : Type} [Group Act] [MulDistribMulAction Act P]
variable {L : Subgroup Act}

/-- The Gorenstein output supplies the two strictness fields of the
proper-branch group scope without any additional character theory.

The remaining arguments are exactly the ambient complement,
intersection, recursive-Sylow, and set-product coordinates. -/
def okuyamaWajimaProperBranchGroupScopeOfCyclicQuotient
    (d :
      OkuyamaWajimaCyclicQuotientSubgroup Act P L)
    (hproper : d.fixedPoints < ⊤)
    (M : Subgroup G)
    (hM :
      M ≤
        okuyamaWajimaProperBranchQNormalizer
          P d.fixedPointPreimage)
    (hinter :
      (P : Subgroup G) ⊓
          okuyamaWajimaProperBranchH
            K P d.fixedPointPreimage M =
        okuyamaWajimaProperBranchQ
          P d.fixedPointPreimage)
    (sylowH :
      Sylow p
        (okuyamaWajimaProperBranchH
          K P d.fixedPointPreimage M))
    (hsylowH :
      (sylowH : Subgroup
          (okuyamaWajimaProperBranchH
            K P d.fixedPointPreimage M)) =
        (okuyamaWajimaProperBranchQ
          P d.fixedPointPreimage).subgroupOf
            (okuyamaWajimaProperBranchH
              K P d.fixedPointPreimage M))
    (hproduct :
      ((P : Subgroup G) : Set G) *
          (okuyamaWajimaProperBranchH
            K P d.fixedPointPreimage M : Set G) =
        (⊤ : Subgroup G)) :
    OkuyamaWajimaProperBranchGroupScope
      K P d.fixedPointPreimage M :=
    OkuyamaWajimaProperBranchGroupScope.of_internal
    d.bot_lt_fixedPointPreimage.ne'
    (d.fixedPointPreimage_lt_top hproper)
    hM hinter sylowH hsylowH hproduct

end GorensteinSelectedSubgroup

end SubgroupCoordinates

/-! ## The three characters and their canonical triples -/

section CharacterCoordinates

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]
variable (M : Subgroup G)

local instance properBranchRecursionPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
variable
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
variable
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ P Q) p)
variable
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- The intermediate character `psi ∈ Irr(C_K(Q))`. -/
abbrev okuyamaWajimaProperBranchPsi :
    PPrimeIrreducibleCharacter
      (okuyamaWajimaProperBranchJ K P Q) p :=
  gQ.characterEquiv
    (okuyamaWajimaProperBranchAmbientQInvariantCharacter
      K (P : Subgroup G) Q theta)

/-- The final character `phi ∈ Irr(C_K(P))`. -/
abbrev okuyamaWajimaProperBranchPhi :
    PPrimeIrreducibleCharacter
      (coprimeFixedPoints K (P : Subgroup G)) p :=
  gP.characterEquiv theta

/-- The globally invariant source character as a character triple on `G`. -/
def okuyamaWajimaProperBranchThetaTriple :
    CharacterTriple G := by
  have hinertia :
      IrreducibleCharacter.inertia K theta.1.1 = ⊤ := by
    apply top_unique
    intro g _hg
    rw [IrreducibleCharacter.mem_inertia_iff]
    exact hinvariant g
  exact
    CharacterTriple.ofInertiaTop
      K theta.1.1 hinertia

/-- The intermediate correspondent as a character triple on `N_G(Q)`.

This definition uses the ordinary ambient Glauberman correspondence, so its
distinguished character is literally the canonical copy of `psi`. -/
def okuyamaWajimaProperBranchPsiNormalizerTriple :
    CharacterTriple
      (okuyamaWajimaProperBranchQNormalizer P Q) :=
  invariantOkuyamaWajimaTargetTriple
    K (okuyamaWajimaProperBranchQ P Q)
    (okuyamaWajimaProperBranchQNormalizer P Q)
    le_rfl
    (okuyamaWajimaProperBranchJ_le_QNormalizer K P Q)
    gQ
    (okuyamaWajimaProperBranchAmbientQInvariantCharacter
      K (P : Subgroup G) Q theta)
    hinvariant

/-- The full `P`-correspondent as a character triple on `N_G(P)`. -/
def okuyamaWajimaProperBranchPhiNormalizerTriple :
    CharacterTriple
      (Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
  invariantOkuyamaWajimaTargetTriple
    K (P : Subgroup G)
    (Subgroup.normalizer ((P : Subgroup G) : Set G))
    le_rfl
    (inf_le_right.trans
      (Subgroup.centralizer_le_normalizer
        ((P : Subgroup G) : Set G)))
    gP theta hinvariant

omit [Fact p.Prime] [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchThetaTriple_normalSubgroup :
    (okuyamaWajimaProperBranchThetaTriple
      K P theta hinvariant).normalSubgroup = K :=
  rfl

omit [Fact p.Prime] [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchThetaTriple_character :
    (okuyamaWajimaProperBranchThetaTriple
      K P theta hinvariant).character = theta.1.1 :=
  rfl

omit [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchPsiNormalizerTriple_normalSubgroup :
    (okuyamaWajimaProperBranchPsiNormalizerTriple
      K P Q theta hinvariant gQ).normalSubgroup =
      (okuyamaWajimaProperBranchJ K P Q).subgroupOf
        (okuyamaWajimaProperBranchQNormalizer P Q) :=
  rfl

omit [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchPsiNormalizerTriple_character :
    (okuyamaWajimaProperBranchPsiNormalizerTriple
      K P Q theta hinvariant gQ).character =
      (okuyamaWajimaProperBranchPsi
        K P Q theta gQ).1.comap
          (Subgroup.subgroupOfEquivOfLe
            (okuyamaWajimaProperBranchJ_le_QNormalizer K P Q)) :=
  rfl

omit [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchPhiNormalizerTriple_normalSubgroup :
    (okuyamaWajimaProperBranchPhiNormalizerTriple
      K P theta hinvariant gP).normalSubgroup =
      (coprimeFixedPoints K (P : Subgroup G)).subgroupOf
        (Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
  rfl

omit [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchPhiNormalizerTriple_character :
    (okuyamaWajimaProperBranchPhiNormalizerTriple
      K P theta hinvariant gP).character =
      (okuyamaWajimaProperBranchPhi
        K P theta gP).1.comap
          (Subgroup.subgroupOfEquivOfLe
            (inf_le_right.trans
              (Subgroup.centralizer_le_normalizer
                ((P : Subgroup G) : Set G)))) :=
  rfl

omit [Q.Normal] in
/-- The source kernel lies in the proper-branch subgroup `H`. -/
theorem okuyamaWajimaProperBranchThetaKernel_le_H :
    (okuyamaWajimaProperBranchThetaTriple
        K P theta hinvariant).normalSubgroup ≤
      okuyamaWajimaProperBranchH K P Q M := by
  change K ≤ okuyamaWajimaProperBranchH K P Q M
  exact okuyamaWajimaProperBranchK_le_H K P Q M

/-- The intermediate fixed-point kernel lies in the canonical copy of
`N_H(Q)` inside `N_G(Q)`. -/
theorem okuyamaWajimaProperBranchPsiKernel_le_HNormalizer :
    (okuyamaWajimaProperBranchPsiNormalizerTriple
        K P Q theta hinvariant gQ).normalSubgroup ≤
      okuyamaWajimaProperBranchHNormalizerInQNormalizer
        K P Q M := by
  intro x hx
  change
    ((x :
        okuyamaWajimaProperBranchQNormalizer P Q) : G) ∈
      okuyamaWajimaProperBranchHNormalizerImage K P Q M
  exact
    okuyamaWajimaProperBranchJ_le_HNormalizerImage
      K P Q M hx

/-- The restricted source triple for the recursive problem on
`H = Q M K`. -/
def okuyamaWajimaProperBranchThetaHTriple :
    CharacterTriple (okuyamaWajimaProperBranchH K P Q M) :=
  (okuyamaWajimaProperBranchThetaTriple
      K P theta hinvariant).restrictTo
    (okuyamaWajimaProperBranchH K P Q M)
    (okuyamaWajimaProperBranchThetaKernel_le_H
      K P Q M theta hinvariant)

/-- The restricted intermediate triple for `N_H(Q)`, represented inside
`N_G(Q)` by the exact intersection coordinate. -/
def okuyamaWajimaProperBranchPsiHNormalizerTriple :
    CharacterTriple
      (okuyamaWajimaProperBranchHNormalizerInQNormalizer
        K P Q M) :=
  (okuyamaWajimaProperBranchPsiNormalizerTriple
      K P Q theta hinvariant gQ).restrictTo
    (okuyamaWajimaProperBranchHNormalizerInQNormalizer
      K P Q M)
    (okuyamaWajimaProperBranchPsiKernel_le_HNormalizer
      K P Q M theta hinvariant gQ)

/-! ### Exact extension propositions in the printed chain -/

/-- `phi` extends to `N_G(P)`. -/
abbrev OkuyamaWajimaProperBranchPhiExtendsToPNormalizer : Prop :=
  (okuyamaWajimaProperBranchPhiNormalizerTriple
    K P theta hinvariant gP).HasExtension

/-- `psi` extends to `N_G(Q)`. -/
abbrev OkuyamaWajimaProperBranchPsiExtendsToQNormalizer : Prop :=
  (okuyamaWajimaProperBranchPsiNormalizerTriple
    K P Q theta hinvariant gQ).HasExtension

/-- `psi` extends to `N_H(Q)`. -/
abbrev OkuyamaWajimaProperBranchPsiExtendsToHNormalizer : Prop :=
  (okuyamaWajimaProperBranchPsiHNormalizerTriple
    K P Q M theta hinvariant gQ).HasExtension

/-- `theta` extends to `H = Q M K`. -/
abbrev OkuyamaWajimaProperBranchThetaExtendsToH : Prop :=
  (okuyamaWajimaProperBranchThetaHTriple
    K P Q M theta hinvariant).HasExtension

/-- `theta` extends to `G`. -/
abbrev OkuyamaWajimaProperBranchThetaExtendsToG : Prop :=
  (okuyamaWajimaProperBranchThetaTriple
    K P theta hinvariant).HasExtension

omit [Q.Normal] in
/-- External-subgroup form of extension of `psi` to `N_G(Q)`. -/
theorem okuyamaWajimaProperBranchPsi_extendsToQNormalizer_iff :
    OkuyamaWajimaProperBranchPsiExtendsToQNormalizer
        K P Q theta hinvariant gQ ↔
      ∃ eta :
          IrreducibleCharacter
            (okuyamaWajimaProperBranchQNormalizer P Q),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion
            (okuyamaWajimaProperBranchJ_le_QNormalizer
              K P Q))
          (okuyamaWajimaProperBranchPsi
            K P Q theta gQ).1 eta := by
  symm
  exact
    exists_extensionAlong_inclusion_iff_subgroupOf
      (okuyamaWajimaProperBranchJ K P Q)
      (okuyamaWajimaProperBranchQNormalizer P Q)
      (okuyamaWajimaProperBranchJ_le_QNormalizer
        K P Q)
      (okuyamaWajimaProperBranchPsi
        K P Q theta gQ).1

omit [Q.Normal] in
/-- External-subgroup form of extension of `phi` to `N_G(P)`. -/
theorem okuyamaWajimaProperBranchPhi_extendsToPNormalizer_iff :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP ↔
      ∃ eta :
          IrreducibleCharacter
            (Subgroup.normalizer
              ((P : Subgroup G) : Set G)),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion
            (inf_le_right.trans
              (Subgroup.centralizer_le_normalizer
                ((P : Subgroup G) : Set G))))
          (okuyamaWajimaProperBranchPhi
            K P theta gP).1 eta := by
  symm
  exact
    exists_extensionAlong_inclusion_iff_subgroupOf
      (coprimeFixedPoints K (P : Subgroup G))
      (Subgroup.normalizer
        ((P : Subgroup G) : Set G))
      (inf_le_right.trans
        (Subgroup.centralizer_le_normalizer
          ((P : Subgroup G) : Set G)))
      (okuyamaWajimaProperBranchPhi
        K P theta gP).1

omit [Q.Normal] in
/-- Direct extension-along-inclusion form of the restricted source problem
on `H`. -/
theorem okuyamaWajimaProperBranchTheta_extendsToH_iff :
    OkuyamaWajimaProperBranchThetaExtendsToH
        K P Q M theta hinvariant ↔
      ∃ eta :
          IrreducibleCharacter
            (okuyamaWajimaProperBranchH K P Q M),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion
            (okuyamaWajimaProperBranchThetaKernel_le_H
              K P Q M theta hinvariant))
          theta.1.1 eta := by
  exact
    CharacterTriple.restrictTo_hasExtension_iff_exists_extensionAlong_inclusion
      (okuyamaWajimaProperBranchThetaTriple
        K P theta hinvariant)
      (okuyamaWajimaProperBranchH K P Q M)
      (okuyamaWajimaProperBranchThetaKernel_le_H
        K P Q M theta hinvariant)

/-- Direct extension-along-inclusion form of the intermediate problem on
the canonical `N_H(Q)` coordinate inside `N_G(Q)`. -/
theorem okuyamaWajimaProperBranchPsi_extendsToHNormalizer_iff :
    OkuyamaWajimaProperBranchPsiExtendsToHNormalizer
        K P Q M theta hinvariant gQ ↔
      ∃ eta :
          IrreducibleCharacter
            (okuyamaWajimaProperBranchHNormalizerInQNormalizer
              K P Q M),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion
            (okuyamaWajimaProperBranchPsiKernel_le_HNormalizer
              K P Q M theta hinvariant gQ))
          (okuyamaWajimaProperBranchPsiNormalizerTriple
            K P Q theta hinvariant gQ).character eta := by
  exact
    CharacterTriple.restrictTo_hasExtension_iff_exists_extensionAlong_inclusion
      (okuyamaWajimaProperBranchPsiNormalizerTriple
        K P Q theta hinvariant gQ)
      (okuyamaWajimaProperBranchHNormalizerInQNormalizer
        K P Q M)
      (okuyamaWajimaProperBranchPsiKernel_le_HNormalizer
        K P Q M theta hinvariant gQ)

/-! ### Glauberman compatibility for the quotient recursive problem -/

omit [Q.Normal] in
/-- The transported action-level first-stage correspondent is the exact
ordinary character `psi` used in the recursive triples. -/
theorem okuyamaWajimaProperBranchAmbientQCorrespondent_eq_psi
    (dQ :
      StrongActionGlaubermanCorrespondence Q K p) :
    okuyamaWajimaProperBranchAmbientQCorrespondent
        K (P : Subgroup G) Q dQ theta =
      okuyamaWajimaProperBranchPsi K P Q theta gQ :=
  okuyamaWajimaProperBranchAmbientQCorrespondent_eq
    K (P : Subgroup G) Q dQ gQ theta

/-- The two-stage `Q`, then `P / Q`, correspondent is the exact ordinary
`P`-correspondent `phi`. -/
theorem okuyamaWajimaProperBranchAmbientIteratedCorrespondent_eq_phi
    (hK : IsPPrimeGroup p K)
    (dQ :
      StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p) :
    okuyamaWajimaProperBranchAmbientIteratedCorrespondent
        K (P : Subgroup G) Q dQ dQuot theta =
      okuyamaWajimaProperBranchPhi K P theta gP :=
  okuyamaWajimaProperBranchAmbientIteratedCorrespondent_eq
    K (P : Subgroup G) Q P.isPGroup' hK
      dQ dQuot gP theta

include hinvariant in
omit [Q.Normal] in
/-- The intermediate character `psi` is invariant under the full ambient
normalizer `N_G(Q)`. -/
theorem okuyamaWajimaProperBranchPsi_invariant_QNormalizer
    (g :
      okuyamaWajimaProperBranchQNormalizer P Q) :
    coprimeFixedPointsNormalizerAction K
        (okuyamaWajimaProperBranchQ P Q) g •
        (okuyamaWajimaProperBranchPsi
          K P Q theta gQ).1 =
      (okuyamaWajimaProperBranchPsi
        K P Q theta gQ).1 := by
  exact
    okuyamaWajimaProperBranchQCorrespondent_invariant_normalizer
      K (P : Subgroup G) Q gQ theta
      (okuyamaWajimaProperBranchNormalizerInvariant_of_ambientInvariant
        K (P : Subgroup G) Q theta hinvariant)
      g

/-- The two-stage character has the defining nonzero-modulo-`p`
restriction multiplicity from `K` to `C_K(P)`. -/
theorem okuyamaWajimaProperBranchPhi_multiplicity_isPPrime
    (hK : IsPPrimeGroup p K)
    (dQ :
      StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p) :
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion K (P : Subgroup G))
        (okuyamaWajimaProperBranchPhi K P theta gP).1
        theta.1.1 := by
  rw [← okuyamaWajimaProperBranchAmbientIteratedCorrespondent_eq_phi
    K P Q theta gP hK dQ dQuot]
  exact
    okuyamaWajimaProperBranchAmbientIterated_multiplicity_isPPrime
      K (P : Subgroup G) Q dQ dQuot theta

end CharacterCoordinates

/-! ## Prime-power ascent and the two induction hypotheses -/

section RecursiveExtensionChain

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]
variable (M : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
variable
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
variable
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ P Q) p)
variable
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- The exact elementary index data used in place of Isaacs,
Corollary 11.31.

The first index is computed inside `N_G(Q)`, using the canonical
intersection copy of `N_H(Q)`.  The second is the ordinary index of
`H = Q M K` in `G`. -/
structure OkuyamaWajimaProperBranchPrimePowerIndexData where
  /-- Exponent witnessing that `[N_G(Q) : N_H(Q)]` divides a `p`-power. -/
  normalizerExponent : ℕ
  /-- The normalizer index divides that `p`-power. -/
  normalizerIndex_dvd :
    (okuyamaWajimaProperBranchHNormalizerInQNormalizer
        K P Q M).index ∣
      p ^ normalizerExponent
  /-- Exponent witnessing that `[G : H]` divides a `p`-power. -/
  ambientExponent : ℕ
  /-- The ambient index divides that `p`-power. -/
  ambientIndex_dvd :
    (okuyamaWajimaProperBranchH K P Q M).index ∣
      p ^ ambientExponent

/-- Construct both prime-power ascent certificates from the
formalization-friendly group scope.

The ambient divisibility comes from the equality
`[G : H] = [P : Q]`.  The same set-product coset argument transports
that exponent to the normalizer index. -/
noncomputable def
    OkuyamaWajimaProperBranchGroupScope.primePowerIndexData
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    OkuyamaWajimaProperBranchPrimePowerIndexData
      K P Q M := by
  let n :=
    Classical.choose scope.ambientIndex_dvd_prime_power
  have hn :
      (okuyamaWajimaProperBranchH K P Q M).index ∣
        p ^ n :=
    Classical.choose_spec scope.ambientIndex_dvd_prime_power
  exact
    { normalizerExponent := n
      normalizerIndex_dvd := by
        rw [scope.normalizerIndex_eq_H_index]
        exact hn
      ambientExponent := n
      ambientIndex_dvd := hn }

/-- The exact result expected from applying the induction hypothesis to
the smaller quotient `N_G(Q) / Q`, after transporting its source and
normalizer characters through the canonical quotient coordinates.

The strict-cardinality certificate for this recursive call is proved
separately by
`OkuyamaWajimaProperBranchGroupScope.normalizerQuotient_card_lt`. -/
def OkuyamaWajimaProperBranchQuotientInductionHypothesis : Prop :=
  OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
      K P theta hinvariant gP ↔
    OkuyamaWajimaProperBranchPsiExtendsToQNormalizer
      K P Q theta hinvariant gQ

/-- The exact result expected from applying the induction hypothesis to
the smaller subgroup `H = Q M K`.

Its left side is extension to the internal normalizer of `Q` in `H`,
represented as the exact intersection subgroup inside `N_G(Q)`. -/
def OkuyamaWajimaProperBranchSubgroupInductionHypothesis : Prop :=
  OkuyamaWajimaProperBranchPsiExtendsToHNormalizer
      K P Q M theta hinvariant gQ ↔
    OkuyamaWajimaProperBranchThetaExtendsToH
      K P Q M theta hinvariant

omit [Q.Normal] in
/-- The kernel of the intermediate character triple is a `p'`-group. -/
theorem okuyamaWajimaProperBranchPsiTriple_kernel_isPPrime
    (hK : IsPPrimeGroup p K) :
    IsPPrimeGroup p
      (okuyamaWajimaProperBranchPsiNormalizerTriple
        K P Q theta hinvariant gQ).normalSubgroup := by
  let J := okuyamaWajimaProperBranchJ K P Q
  have hJ :
      IsPPrimeGroup p J := by
    exact
      (hK.to_subgroup (J.subgroupOf K)).of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (show J ≤ K from inf_le_left))
  exact
    hJ.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (okuyamaWajimaProperBranchJ_le_QNormalizer
          K P Q)).symm

omit [Q.Normal] in
/-- The distinguished intermediate character has `p'`-degree. -/
theorem okuyamaWajimaProperBranchPsiTriple_character_isPPrimeDegree :
    (okuyamaWajimaProperBranchPsiNormalizerTriple
      K P Q theta hinvariant gQ).character.IsPPrimeDegree p := by
  change
    ((okuyamaWajimaProperBranchPsi
      K P Q theta gQ).1.comap
        (Subgroup.subgroupOfEquivOfLe
          (okuyamaWajimaProperBranchJ_le_QNormalizer
            K P Q))).IsPPrimeDegree p
  simpa [IrreducibleCharacter.IsPPrimeDegree] using
    (okuyamaWajimaProperBranchPsi
      K P Q theta gQ).2

/-- Navarro prime-power ascent proves
`Ext_{N_G(Q)}(psi) ↔ Ext_{N_H(Q)}(psi)`. -/
theorem okuyamaWajimaProperBranchPsi_ascent_iff
    (hK : IsPPrimeGroup p K)
    (indexData :
      OkuyamaWajimaProperBranchPrimePowerIndexData
        K P Q M) :
    OkuyamaWajimaProperBranchPsiExtendsToQNormalizer
        K P Q theta hinvariant gQ ↔
      OkuyamaWajimaProperBranchPsiExtendsToHNormalizer
        K P Q M theta hinvariant gQ := by
  let T :=
    okuyamaWajimaProperBranchPsiNormalizerTriple
      K P Q theta hinvariant gQ
  let B :=
    okuyamaWajimaProperBranchHNormalizerInQNormalizer
      K P Q M
  have hNB :
      T.normalSubgroup ≤ B :=
    okuyamaWajimaProperBranchPsiKernel_le_HNormalizer
      K P Q M theta hinvariant gQ
  have hnav :=
    T.hasExtension_iff_restrictTo_of_index_dvd_prime_power
      B hNB
      (okuyamaWajimaProperBranchPsiTriple_kernel_isPPrime
        K P Q theta hinvariant gQ hK)
      (okuyamaWajimaProperBranchPsiTriple_character_isPPrimeDegree
        K P Q theta hinvariant gQ)
      indexData.normalizerIndex_dvd
  exact hnav

/-- Navarro prime-power ascent proves
`Ext_G(theta) ↔ Ext_H(theta)`. -/
theorem okuyamaWajimaProperBranchTheta_ascent_iff
    (hK : IsPPrimeGroup p K)
    (indexData :
      OkuyamaWajimaProperBranchPrimePowerIndexData
        K P Q M) :
    OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant ↔
      OkuyamaWajimaProperBranchThetaExtendsToH
        K P Q M theta hinvariant := by
  let T :=
    okuyamaWajimaProperBranchThetaTriple
      K P theta hinvariant
  let H :=
    okuyamaWajimaProperBranchH K P Q M
  have hKH :
      T.normalSubgroup ≤ H :=
    okuyamaWajimaProperBranchThetaKernel_le_H
      K P Q M theta hinvariant
  have hnav :=
    T.hasExtension_iff_restrictTo_of_index_dvd_prime_power
      H hKH hK theta.1.2
      indexData.ambientIndex_dvd
  exact hnav

/-- The complete proper-branch extension chain.

This is the source order

`Ext_N(phi) ↔ Ext_{N_G(Q)}(psi) ↔ Ext_{N_H(Q)}(psi)
  ↔ Ext_H(theta) ↔ Ext_G(theta)`.

This lower-level form accepts the already-constructed prime-power index
data. -/
theorem okuyamaWajimaProperBranch_extension_iff_of_indexData
    (hK : IsPPrimeGroup p K)
    (indexData :
      OkuyamaWajimaProperBranchPrimePowerIndexData
        K P Q M)
    (quotientIH :
      OkuyamaWajimaProperBranchQuotientInductionHypothesis
        K P Q theta hinvariant gQ gP)
    (subgroupIH :
      OkuyamaWajimaProperBranchSubgroupInductionHypothesis
        K P Q M theta hinvariant gQ) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP ↔
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant := by
  exact
    quotientIH.trans
      ((okuyamaWajimaProperBranchPsi_ascent_iff
          K P Q M theta hinvariant gQ hK indexData).trans
        (subgroupIH.trans
          (okuyamaWajimaProperBranchTheta_ascent_iff
            K P Q M theta hinvariant hK indexData).symm))

/-- The complete proper-branch extension chain from the group scope and
the two genuine induction conclusions.  Both prime-power ascent inputs
are derived internally. -/
theorem okuyamaWajimaProperBranch_extension_iff
    (hK : IsPPrimeGroup p K)
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M)
    (quotientIH :
      OkuyamaWajimaProperBranchQuotientInductionHypothesis
        K P Q theta hinvariant gQ gP)
    (subgroupIH :
      OkuyamaWajimaProperBranchSubgroupInductionHypothesis
        K P Q M theta hinvariant gQ) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP ↔
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant :=
  okuyamaWajimaProperBranch_extension_iff_of_indexData
    K P Q M theta hinvariant gQ gP hK
      scope.primePowerIndexData quotientIH subgroupIH

/-- A bundled exact recursive scope: the subgroup coordinates and both
smaller induction conclusions.

The same group scope both certifies the strict cardinality decreases and
supplies the two prime-power ascent inputs. -/
structure OkuyamaWajimaProperBranchRecursiveInput where
  /-- The subgroup, normality, generation, and strictness coordinates. -/
  groupScope :
    OkuyamaWajimaProperBranchGroupScope K P Q M
  /-- Induction on `N_G(Q) / Q`. -/
  quotientIH :
    OkuyamaWajimaProperBranchQuotientInductionHypothesis
      K P Q theta hinvariant gQ gP
  /-- Induction on `H = Q M K`. -/
  subgroupIH :
    OkuyamaWajimaProperBranchSubgroupInductionHypothesis
      K P Q M theta hinvariant gQ

/-- Bundled form of the complete proper-branch chain. -/
theorem OkuyamaWajimaProperBranchRecursiveInput.extension_iff
    (input :
      OkuyamaWajimaProperBranchRecursiveInput
        K P Q M theta hinvariant gQ gP)
    (hK : IsPPrimeGroup p K) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP ↔
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant :=
  okuyamaWajimaProperBranch_extension_iff
    K P Q M theta hinvariant gQ gP hK
      input.groupScope input.quotientIH input.subgroupIH

end RecursiveExtensionChain

end McKayConjecture
