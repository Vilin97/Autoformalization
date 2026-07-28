/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverSylowThreeExtraspecial

/-!
# Centralizers and normalizer actions at three in `6.A₆`

For an arbitrary Sylow `3`-subgroup `P` of the canonical universal cover,
projection maps `P` onto a Sylow `3`-subgroup of `A₆`.  Its restricted
kernel and its intrinsic center both have order three, so they coincide.

Since Sylow `3`-subgroups of `A₆` are self-centralizing, this kernel
identification then shows

`C_{6.A₆}(P) = Z(6.A₆)`.

Thus the kernel of the normalizer action on `P` has order six, while its
range has order thirty-six.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixUniversalCoverThreeCentralizerFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

private abbrev alternatingSixUniversalCoverExtension :=
  alternatingSixUniversalCentralExtension.toCentralExtension

/-! ### Projection of an arbitrary Sylow subgroup -/

/-- The image in `A₆` of an arbitrary Sylow `3`-subgroup of its universal
cover. -/
def alternatingSixUniversalCoverSylowThreeTarget
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Sylow 3 AlternatingSix :=
  P.mapSurjective alternatingSixUniversalCoverExtension.surjective

@[simp]
theorem alternatingSixUniversalCoverSylowThreeTarget_coe
    (P : Sylow 3 AlternatingSixUniversalCover) :
    (alternatingSixUniversalCoverSylowThreeTarget P :
        Subgroup AlternatingSix) =
      (P : Subgroup AlternatingSixUniversalCover).map
        alternatingSixUniversalCoverExtension.projection :=
  rfl

/-- Projection restricted from an arbitrary cover Sylow subgroup to its
target image. -/
def alternatingSixUniversalCoverSylowThreeProjectionOf
    (P : Sylow 3 AlternatingSixUniversalCover) :
    P →* alternatingSixUniversalCoverSylowThreeTarget P where
  toFun x :=
    ⟨alternatingSixUniversalCoverExtension.projection (x : AlternatingSixUniversalCover),
      by
        change
          alternatingSixUniversalCoverExtension.projection
              (x : AlternatingSixUniversalCover) ∈
            (P : Subgroup AlternatingSixUniversalCover).map
              alternatingSixUniversalCoverExtension.projection
        exact ⟨x, x.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one alternatingSixUniversalCoverExtension.projection
  map_mul' x y := by
    apply Subtype.ext
    exact
      map_mul alternatingSixUniversalCoverExtension.projection
        (x : AlternatingSixUniversalCover)
        (y : AlternatingSixUniversalCover)

@[simp]
theorem alternatingSixUniversalCoverSylowThreeProjectionOf_apply_coe
    (P : Sylow 3 AlternatingSixUniversalCover) (x : P) :
    ((alternatingSixUniversalCoverSylowThreeProjectionOf P x :
        alternatingSixUniversalCoverSylowThreeTarget P) :
      AlternatingSix) =
        alternatingSixUniversalCoverExtension.projection
          (x : AlternatingSixUniversalCover) :=
  rfl

/-- The restricted Sylow projection is surjective. -/
theorem alternatingSixUniversalCoverSylowThreeProjectionOf_surjective
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Function.Surjective
      (alternatingSixUniversalCoverSylowThreeProjectionOf P) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.property
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- The restricted projection kernel is central in the Sylow subgroup. -/
theorem alternatingSixUniversalCoverSylowThreeProjectionOf_ker_le_center
    (P : Sylow 3 AlternatingSixUniversalCover) :
    (alternatingSixUniversalCoverSylowThreeProjectionOf P).ker ≤
      Subgroup.center P := by
  intro x hx
  have hxKernel :
      (x : AlternatingSixUniversalCover) ∈
        alternatingSixUniversalCoverExtension.projection.ker := by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  have hxCenter :
      (x : AlternatingSixUniversalCover) ∈
        Subgroup.center AlternatingSixUniversalCover :=
    alternatingSixUniversalCoverExtension.ker_le_center hxKernel
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp hxCenter
      (y : AlternatingSixUniversalCover)

/-- The restricted kernel has order three. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowThreeProjectionOf_ker
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Nat.card
        (alternatingSixUniversalCoverSylowThreeProjectionOf P).ker =
      3 := by
  let f :=
    alternatingSixUniversalCoverSylowThreeProjectionOf P
  have hrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (alternatingSixUniversalCoverSylowThreeProjectionOf_surjective P)
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card P := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ = Nat.card P :=
        f.ker.card_mul_index
  change Nat.card f.ker = 3
  rw [hrange, Subgroup.card_top,
    natCard_sylowThree_alternatingSix,
    natCard_sylowThree_alternatingSixUniversalCover] at hcard
  omega

/-- For every cover Sylow subgroup, its intrinsic center is exactly the
kernel of projection onto its image in `A₆`. -/
theorem alternatingSixUniversalCoverSylowThreeProjectionOf_ker_eq_center
    (P : Sylow 3 AlternatingSixUniversalCover) :
    (alternatingSixUniversalCoverSylowThreeProjectionOf P).ker =
      Subgroup.center P := by
  apply Subgroup.eq_of_le_of_card_ge
    (alternatingSixUniversalCoverSylowThreeProjectionOf_ker_le_center P)
  rw [natCard_center_sylowThree_alternatingSixUniversalCover,
    natCard_alternatingSixUniversalCoverSylowThreeProjectionOf_ker]

/-- The restricted kernel is also exactly the intersection of the ambient
center with the Sylow subgroup. -/
theorem alternatingSixUniversalCoverSylowThreeProjectionOf_ker_eq_ambientCenter
    (P : Sylow 3 AlternatingSixUniversalCover) :
    (alternatingSixUniversalCoverSylowThreeProjectionOf P).ker =
      (Subgroup.center AlternatingSixUniversalCover).subgroupOf
        (P : Subgroup AlternatingSixUniversalCover) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    rw [← alternatingSixUniversalCentralExtension_ker_eq_center,
      MonoidHom.mem_ker]
    exact congrArg Subtype.val hx
  · intro hx
    apply Subtype.ext
    change
      alternatingSixUniversalCoverExtension.projection
          (x : AlternatingSixUniversalCover) =
        1
    rw [← alternatingSixUniversalCentralExtension_ker_eq_center]
      at hx
    exact MonoidHom.mem_ker.mp hx

/-- The intrinsic Sylow center is the intersection with the ambient
order-six center. -/
theorem center_sylowThree_alternatingSixUniversalCover_eq_ambientCenter
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Subgroup.center P =
      (Subgroup.center AlternatingSixUniversalCover).subgroupOf
        (P : Subgroup AlternatingSixUniversalCover) := by
  calc
    Subgroup.center P =
        (alternatingSixUniversalCoverSylowThreeProjectionOf P).ker :=
      (alternatingSixUniversalCoverSylowThreeProjectionOf_ker_eq_center
        P).symm
    _ =
        (Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (P : Subgroup AlternatingSixUniversalCover) :=
      alternatingSixUniversalCoverSylowThreeProjectionOf_ker_eq_ambientCenter
        P

/-- For the originally fixed Sylow subgroup, the pre-existing restricted
projection kernel is its intrinsic center. -/
theorem alternatingSixUniversalCoverSylowThreeProjection_ker_eq_intrinsicCenter :
    (alternatingSixUniversalCoverSylowProjection 3).ker =
      Subgroup.center (alternatingSixUniversalCoverSylow 3) := by
  rw [alternatingSixUniversalCoverSylowProjection_ker]
  exact
    (center_sylowThree_alternatingSixUniversalCover_eq_ambientCenter
      (alternatingSixUniversalCoverSylow 3)).symm

/-! ### The ambient centralizer -/

/-- Every Sylow `3`-subgroup of the universal cover has ambient centralizer
equal to the order-six center of the cover. -/
theorem centralizer_sylowThree_alternatingSixUniversalCover_eq_center
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Subgroup.centralizer
        ((P : Subgroup AlternatingSixUniversalCover) :
          Set AlternatingSixUniversalCover) =
      Subgroup.center AlternatingSixUniversalCover := by
  apply le_antisymm
  · intro g hg
    have hgCentralizes :
        ∀ x : AlternatingSixUniversalCover,
          x ∈ (P : Subgroup AlternatingSixUniversalCover) →
            x * g = g * x := by
      rw [Subgroup.mem_centralizer_iff] at hg
      exact hg
    have hgImageCentralizes :
        alternatingSixUniversalCoverExtension.projection g ∈
          Subgroup.centralizer
            ((alternatingSixUniversalCoverSylowThreeTarget P :
                Subgroup AlternatingSix) :
              Set AlternatingSix) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      change
        y * alternatingSixUniversalCoverExtension.projection g =
          alternatingSixUniversalCoverExtension.projection g * y
      change
        y ∈
          (P : Subgroup AlternatingSixUniversalCover).map
            alternatingSixUniversalCoverExtension.projection at hy
      obtain ⟨x, hx, rfl⟩ := hy
      simpa only [map_mul] using
        congrArg alternatingSixUniversalCoverExtension.projection
          (hgCentralizes x hx)
    have hgImageInTarget :
        alternatingSixUniversalCoverExtension.projection g ∈
          (alternatingSixUniversalCoverSylowThreeTarget P :
            Subgroup AlternatingSix) := by
      rw [← centralizer_sylowThree_alternatingSix_eq
        (alternatingSixUniversalCoverSylowThreeTarget P)]
      exact hgImageCentralizes
    change
      alternatingSixUniversalCoverExtension.projection g ∈
        (P : Subgroup AlternatingSixUniversalCover).map
          alternatingSixUniversalCoverExtension.projection
        at hgImageInTarget
    obtain ⟨p, hp, hpProjection⟩ := hgImageInTarget
    let pP : P := ⟨p, hp⟩
    let k : AlternatingSixUniversalCover := g * p⁻¹
    have hkKernel :
        k ∈ alternatingSixUniversalCoverExtension.projection.ker := by
      rw [MonoidHom.mem_ker]
      change
        alternatingSixUniversalCoverExtension.projection (g * p⁻¹) =
          1
      rw [map_mul, map_inv, hpProjection]
      exact mul_inv_cancel _
    have hkCenter :
        k ∈ Subgroup.center AlternatingSixUniversalCover :=
      alternatingSixUniversalCoverExtension.ker_le_center hkKernel
    have hpFactor : p = k⁻¹ * g := by
      change p = (g * p⁻¹)⁻¹ * g
      group
    have hpCenter : pP ∈ Subgroup.center P := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      apply Subtype.ext
      change
        (y : AlternatingSixUniversalCover) * p =
          p * (y : AlternatingSixUniversalCover)
      rw [hpFactor]
      have hyk :
          (y : AlternatingSixUniversalCover) * k⁻¹ =
            k⁻¹ * (y : AlternatingSixUniversalCover) :=
        (Subgroup.mem_center_iff.mp
          ((Subgroup.center AlternatingSixUniversalCover).inv_mem
            hkCenter)
          (y : AlternatingSixUniversalCover))
      calc
        (y : AlternatingSixUniversalCover) * (k⁻¹ * g) =
            ((y : AlternatingSixUniversalCover) * k⁻¹) * g := by
          rw [mul_assoc]
        _ = (k⁻¹ * (y : AlternatingSixUniversalCover)) * g := by
          rw [hyk]
        _ = k⁻¹ *
              ((y : AlternatingSixUniversalCover) * g) := by
          rw [mul_assoc]
        _ = k⁻¹ *
              (g * (y : AlternatingSixUniversalCover)) := by
          rw [hgCentralizes y y.property]
        _ = (k⁻¹ * g) *
              (y : AlternatingSixUniversalCover) := by
          rw [mul_assoc]
    have hpRestrictedKernel :
        pP ∈
          (alternatingSixUniversalCoverSylowThreeProjectionOf P).ker := by
      rw [alternatingSixUniversalCoverSylowThreeProjectionOf_ker_eq_center]
      exact hpCenter
    have hpProjectionOne :
        alternatingSixUniversalCoverExtension.projection p = 1 := by
      have hpOne :=
        MonoidHom.mem_ker.mp hpRestrictedKernel
      exact congrArg Subtype.val hpOne
    have hgProjectionOne :
        alternatingSixUniversalCoverExtension.projection g = 1 := by
      rw [← hpProjection, hpProjectionOne]
    rw [← alternatingSixUniversalCentralExtension_ker_eq_center,
      MonoidHom.mem_ker]
    exact hgProjectionOne
  · exact
      Subgroup.center_le_centralizer
        ((P : Subgroup AlternatingSixUniversalCover) :
          Set AlternatingSixUniversalCover)

/-- The ambient centralizer of every cover Sylow `3`-subgroup has order
six. -/
@[simp]
theorem natCard_centralizer_sylowThree_alternatingSixUniversalCover
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Nat.card
        (Subgroup.centralizer
          ((P : Subgroup AlternatingSixUniversalCover) :
            Set AlternatingSixUniversalCover)) =
      6 := by
  rw [centralizer_sylowThree_alternatingSixUniversalCover_eq_center,
    alternatingSixHopfKernelHasOrderSix.center]

/-! ### Exact normalizer action -/

/-- The central extension induces a bijection on Sylow `3`-subgroups, so
there are exactly ten in the universal cover. -/
@[simp]
theorem natCard_sylowThree_subgroups_alternatingSixUniversalCover :
    Nat.card (Sylow 3 AlternatingSixUniversalCover) = 10 := by
  calc
    Nat.card (Sylow 3 AlternatingSixUniversalCover) =
        Nat.card (Sylow 3 AlternatingSix) :=
      Nat.card_congr
        (alternatingSixUniversalCoverExtension.sylowMapEquiv)
    _ = 10 :=
      natCard_sylowThree_subgroups_alternatingSix

/-- Every Sylow `3`-normalizer in the canonical universal cover has order
two hundred sixteen. -/
@[simp]
theorem natCard_normalizer_sylowThree_alternatingSixUniversalCover
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Nat.card
        (Subgroup.normalizer
          ((P : Subgroup AlternatingSixUniversalCover) :
            Set AlternatingSixUniversalCover)) =
      216 := by
  let S :=
    alternatingSixUniversalCoverSylowThreeTarget P
  have hP :
      P =
        alternatingSixUniversalCoverExtension.sylowLift S := by
    apply
      (alternatingSixUniversalCoverExtension.eq_sylowLift_iff_mapSurjective_eq
        S P).mpr
    rfl
  have hcard :=
    alternatingSixUniversalCoverExtension.sylowNormalizer_card_eq S
  have hkernel :
      Nat.card alternatingSixUniversalCoverExtension.projection.ker =
        6 := by
    rw [alternatingSixUniversalCentralExtension_ker_eq_center,
      alternatingSixHopfKernelHasOrderSix.center]
  have htarget :
      Nat.card
          (Subgroup.normalizer
            (S : Set AlternatingSix)) =
        36 :=
    natCard_normalizer_sylowThree_alternatingSix S
  rw [← hP] at hcard
  change
    Nat.card
        (Subgroup.normalizer
          (P : Set AlternatingSixUniversalCover)) =
      Nat.card alternatingSixUniversalCoverExtension.projection.ker *
        Nat.card (Subgroup.normalizer (S : Set AlternatingSix))
      at hcard
  rw [hkernel, htarget] at hcard
  norm_num at hcard ⊢
  exact hcard

/-- The kernel of the normalizer action is precisely the ambient center,
viewed inside the normalizer. -/
theorem sylowThree_alternatingSixUniversalCover_normalizerMonoidHom_ker_eq_center
    (P : Sylow 3 AlternatingSixUniversalCover) :
    (P : Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.ker =
      (Subgroup.center AlternatingSixUniversalCover).subgroupOf
        (Subgroup.normalizer
          ((P : Subgroup AlternatingSixUniversalCover) :
            Set AlternatingSixUniversalCover)) := by
  rw [Subgroup.normalizerMonoidHom_ker,
    centralizer_sylowThree_alternatingSixUniversalCover_eq_center]

/-- The kernel of the normalizer action has order six. -/
@[simp]
theorem natCard_sylowThree_alternatingSixUniversalCover_normalizerMonoidHom_ker
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Nat.card
        (P : Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.ker =
      6 := by
  rw [
    sylowThree_alternatingSixUniversalCover_normalizerMonoidHom_ker_eq_center]
  calc
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSixUniversalCover) :
              Set AlternatingSixUniversalCover))) =
        Nat.card (Subgroup.center AlternatingSixUniversalCover) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.center_le_normalizer
            ((P : Subgroup AlternatingSixUniversalCover) :
              Set AlternatingSixUniversalCover))).toEquiv
    _ = 6 :=
      alternatingSixHopfKernelHasOrderSix.center

/-- Conjugation by the Sylow normalizer acts through a group of order
thirty-six. -/
@[simp]
theorem natCard_sylowThree_alternatingSixUniversalCover_normalizerActionRange
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Nat.card
        (P : Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range =
      36 := by
  let f :=
    (P : Subgroup AlternatingSixUniversalCover).normalizerMonoidHom
  have hproduct :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSixUniversalCover) :
              Set AlternatingSixUniversalCover)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.normalizer
              ((P : Subgroup AlternatingSixUniversalCover) :
                Set AlternatingSixUniversalCover)) :=
        f.ker.card_mul_index
  change Nat.card f.range = 36
  rw [
    natCard_sylowThree_alternatingSixUniversalCover_normalizerMonoidHom_ker,
    natCard_normalizer_sylowThree_alternatingSixUniversalCover] at hproduct
  omega

/-- The normalizer modulo the ambient center is exactly the induced
automorphism group of the Sylow subgroup. -/
def alternatingSixUniversalCoverSylowThreeNormalizerQuotientCenterEquivActionRange
    (P : Sylow 3 AlternatingSixUniversalCover) :
    (Subgroup.normalizer
          ((P : Subgroup AlternatingSixUniversalCover) :
            Set AlternatingSixUniversalCover)) ⧸
        (Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSixUniversalCover) :
              Set AlternatingSixUniversalCover)) ≃*
      (P : Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range := by
  let f :=
    (P : Subgroup AlternatingSixUniversalCover).normalizerMonoidHom
  exact
    (QuotientGroup.quotientMulEquivOfEq
        (sylowThree_alternatingSixUniversalCover_normalizerMonoidHom_ker_eq_center
          P).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq
          (MonoidHom.ker_rangeRestrict f).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          f.rangeRestrict f.rangeRestrict_surjective))

end GroupTheory
end McKayConjecture
