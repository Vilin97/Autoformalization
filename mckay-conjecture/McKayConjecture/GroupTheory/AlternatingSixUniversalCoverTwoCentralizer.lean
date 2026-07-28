/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverSylowTwoQuaternion

/-!
# The two-local centralizer and normalizer action in `6.A₆`

Projection always maps the centralizer of the fixed cover Sylow subgroup
into the centralizer of its target image.  Its kernel is the full order-six
center, while the target centralizer has order two.  Consequently the cover
centralizer initially has order either six or twelve.  The explicit
generalized-quaternion identification of the cover Sylow subgroup shows
that its inner automorphisms already have order eight.  This selects
centralizer order six and normalizer-action order eight.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixUniversalCoverTwoCentralizerFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Projection restricted from the centralizer of the fixed cover Sylow
subgroup to the centralizer of its target image.  Unlike the corresponding
five-local map, its construction does not require injectivity on the Sylow
subgroup. -/
def alternatingSixUniversalCoverSylowTwoCentralizerProjection :
    Subgroup.centralizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover) →*
      Subgroup.centralizer
        (alternatingSixUniversalCoverTargetSylow 2 :
          Set AlternatingSix) where
  toFun x :=
    ⟨alternatingSixUniversalCentralExtension.toCentralExtension.projection
        (x : AlternatingSixUniversalCover),
      by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨z, hz⟩ :=
          alternatingSixUniversalCoverSylowProjection_surjective 2
            ⟨y, hy⟩
        have hx :=
          x.property
            (z : AlternatingSixUniversalCover)
            z.property
        have hxMap :=
          congrArg
            alternatingSixUniversalCentralExtension.toCentralExtension.projection
            hx
        have hzCoe :
            alternatingSixUniversalCentralExtension.toCentralExtension.projection
                (z : AlternatingSixUniversalCover) =
              y :=
          congrArg Subtype.val hz
        rw [← hzCoe]
        simpa only [map_mul] using hxMap⟩
  map_one' := by
    apply Subtype.ext
    exact
      alternatingSixUniversalCentralExtension.toCentralExtension.projection.map_one
  map_mul' x y := by
    apply Subtype.ext
    exact
      alternatingSixUniversalCentralExtension.toCentralExtension.projection.map_mul
        x y

@[simp]
theorem alternatingSixUniversalCoverSylowTwoCentralizerProjection_apply_coe
    (x :
      Subgroup.centralizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover)) :
    ((alternatingSixUniversalCoverSylowTwoCentralizerProjection x :
        Subgroup.centralizer
          (alternatingSixUniversalCoverTargetSylow 2 :
            Set AlternatingSix)) :
      AlternatingSix) =
        alternatingSixUniversalCentralExtension.toCentralExtension.projection
          (x : AlternatingSixUniversalCover) :=
  rfl

/-- The kernel is the full center, viewed in the Sylow centralizer. -/
@[simp]
theorem alternatingSixUniversalCoverSylowTwoCentralizerProjection_ker :
    alternatingSixUniversalCoverSylowTwoCentralizerProjection.ker =
      (Subgroup.center AlternatingSixUniversalCover).subgroupOf
        (Subgroup.centralizer
          (alternatingSixUniversalCoverSylow 2 :
            Set AlternatingSixUniversalCover)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hxProjection :
        alternatingSixUniversalCentralExtension.toCentralExtension.projection
              (x : AlternatingSixUniversalCover) =
            1 :=
      congrArg Subtype.val hx
    have hxKernel :
        (x : AlternatingSixUniversalCover) ∈
          alternatingSixUniversalCentralExtension.toCentralExtension.projection.ker :=
      MonoidHom.mem_ker.mpr hxProjection
    rw [
      alternatingSixUniversalCentralExtension_ker_eq_center]
      at hxKernel
    exact hxKernel
  · intro hxCenter
    apply Subtype.ext
    change
      alternatingSixUniversalCentralExtension.toCentralExtension.projection
            (x : AlternatingSixUniversalCover) =
          1
    apply MonoidHom.mem_ker.mp
    rw [
      alternatingSixUniversalCentralExtension_ker_eq_center]
    exact hxCenter

/-- The restricted centralizer projection has kernel of order six. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowTwoCentralizerProjection_ker :
    Nat.card
        alternatingSixUniversalCoverSylowTwoCentralizerProjection.ker =
      6 := by
  rw [
    alternatingSixUniversalCoverSylowTwoCentralizerProjection_ker]
  calc
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.centralizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover))) =
        Nat.card
          (Subgroup.center
            AlternatingSixUniversalCover) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.center_le_centralizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover))).toEquiv
    _ = 6 :=
      alternatingSixHopfKernelHasOrderSix.center

/-- The range of the restricted centralizer projection has order dividing
two. -/
theorem natCard_alternatingSixUniversalCoverSylowTwoCentralizerProjection_range_dvd_two :
    Nat.card
        alternatingSixUniversalCoverSylowTwoCentralizerProjection.range ∣
      2 := by
  let S :=
    alternatingSixUniversalCoverTargetSylow 2
  have hdvd :
      Nat.card
          alternatingSixUniversalCoverSylowTwoCentralizerProjection.range ∣
        Nat.card
          (Subgroup.centralizer
            (S :
              Set AlternatingSix)) :=
    alternatingSixUniversalCoverSylowTwoCentralizerProjection.range.card_subgroup_dvd_card
  have htarget :
      Nat.card
          (Subgroup.centralizer
            (S : Set AlternatingSix)) =
        2 := by
    change
      Nat.card
          (Subgroup.centralizer
            ((S : Subgroup AlternatingSix) :
              Set AlternatingSix)) =
        2
    exact
      natCard_centralizer_sylowTwo_alternatingSix S
  rw [htarget] at hdvd
  exact hdvd

/-- The restricted centralizer projection has range of order one or two. -/
theorem natCard_alternatingSixUniversalCoverSylowTwoCentralizerProjection_range_cases :
    Nat.card
          alternatingSixUniversalCoverSylowTwoCentralizerProjection.range =
        1 ∨
      Nat.card
          alternatingSixUniversalCoverSylowTwoCentralizerProjection.range =
        2 := by
  exact
    (Nat.dvd_prime Nat.prime_two).mp
      natCard_alternatingSixUniversalCoverSylowTwoCentralizerProjection_range_dvd_two

/-- The cover Sylow centralizer has order six or twelve. -/
theorem natCard_centralizer_alternatingSixUniversalCoverSylowTwo_cases :
    Nat.card
          (Subgroup.centralizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover)) =
        6 ∨
      Nat.card
          (Subgroup.centralizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover)) =
        12 := by
  let f :=
    alternatingSixUniversalCoverSylowTwoCentralizerProjection
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.centralizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.centralizer
              (alternatingSixUniversalCoverSylow 2 :
                Set AlternatingSixUniversalCover)) :=
        f.ker.card_mul_index
  have hker : Nat.card f.ker = 6 :=
    natCard_alternatingSixUniversalCoverSylowTwoCentralizerProjection_ker
  have hrange :
      Nat.card f.range = 1 ∨ Nat.card f.range = 2 :=
    natCard_alternatingSixUniversalCoverSylowTwoCentralizerProjection_range_cases
  rcases hrange with hrange | hrange
  · left
    rw [hker, hrange] at hcard
    omega
  · right
    rw [hker, hrange] at hcard
    omega

/-- The cover normalizer action has order four or eight. -/
theorem natCard_alternatingSixUniversalCoverSylowTwo_normalizerMonoidHom_range_cases :
    Nat.card
          (alternatingSixUniversalCoverSylow 2 :
            Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range =
        4 ∨
      Nat.card
          (alternatingSixUniversalCoverSylow 2 :
            Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range =
        8 := by
  let P :=
    (alternatingSixUniversalCoverSylow 2 :
      Subgroup AlternatingSixUniversalCover)
  let f := P.normalizerMonoidHom
  have hker :
      Nat.card f.ker =
        Nat.card
          (Subgroup.centralizer
            (P : Set AlternatingSixUniversalCover)) := by
    rw [Subgroup.normalizerMonoidHom_ker]
    exact
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.centralizer_le_normalizer
            (P : Set AlternatingSixUniversalCover))).toEquiv
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.normalizer
            (P : Set AlternatingSixUniversalCover)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.normalizer
              (P : Set AlternatingSixUniversalCover)) :=
        f.ker.card_mul_index
  have hcentralizer :
      Nat.card
            (Subgroup.centralizer
              (P : Set AlternatingSixUniversalCover)) =
          6 ∨
        Nat.card
            (Subgroup.centralizer
              (P : Set AlternatingSixUniversalCover)) =
          12 :=
    natCard_centralizer_alternatingSixUniversalCoverSylowTwo_cases
  have hnormalizer :
      Nat.card
          (Subgroup.normalizer
            (P : Set AlternatingSixUniversalCover)) =
        48 := by
    change
      Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover)) =
        48
    exact
      natCard_normalizer_alternatingSixUniversalCoverSylowTwo
  change
    Nat.card f.range = 4 ∨
      Nat.card f.range = 8
  rcases hcentralizer with hcentralizer | hcentralizer
  · right
    rw [hker, hcentralizer, hnormalizer] at hcard
    omega
  · left
    rw [hker, hcentralizer, hnormalizer] at hcard
    omega

/-- Selecting the classical order-six centralizer is equivalent to the
normalizer inducing eight automorphisms. -/
theorem natCard_centralizer_eq_six_iff_normalizerMonoidHom_range_eq_eight :
    Nat.card
          (Subgroup.centralizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover)) =
        6 ↔
      Nat.card
          (alternatingSixUniversalCoverSylow 2 :
            Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range =
        8 := by
  let P :=
    (alternatingSixUniversalCoverSylow 2 :
      Subgroup AlternatingSixUniversalCover)
  let f := P.normalizerMonoidHom
  have hker :
      Nat.card f.ker =
        Nat.card
          (Subgroup.centralizer
            (P : Set AlternatingSixUniversalCover)) := by
    rw [Subgroup.normalizerMonoidHom_ker]
    exact
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.centralizer_le_normalizer
            (P : Set AlternatingSixUniversalCover))).toEquiv
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        48 := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card
            (Subgroup.normalizer
              (P : Set AlternatingSixUniversalCover)) := by
        calc
          Nat.card f.ker * Nat.card f.range =
              Nat.card f.ker * f.ker.index := by
            rw [Subgroup.index_ker]
          _ =
              Nat.card
                (Subgroup.normalizer
                  (P : Set AlternatingSixUniversalCover)) :=
            f.ker.card_mul_index
      _ = 48 := by
        change
          Nat.card
              (Subgroup.normalizer
                (alternatingSixUniversalCoverSylow 2 :
                  Set AlternatingSixUniversalCover)) =
            48
        exact
          natCard_normalizer_alternatingSixUniversalCoverSylowTwo
  change
    Nat.card
          (Subgroup.centralizer
            (P : Set AlternatingSixUniversalCover)) =
        6 ↔
      Nat.card f.range = 8
  constructor
  · intro hcentralizer
    rw [hker, hcentralizer] at hcard
    omega
  · intro hrange
    rw [hker, hrange] at hcard
    omega

/-! ### Selecting the exact generalized-quaternion alternative -/

/-- The central kernel of the Sylow projection is the intrinsic center of
the generalized-quaternion Sylow subgroup. -/
theorem alternatingSixUniversalCoverSylowTwoProjection_ker_eq_center :
    (alternatingSixUniversalCoverSylowProjection 2).ker =
      Subgroup.center (alternatingSixUniversalCoverSylow 2) := by
  apply
    Subgroup.eq_of_le_of_card_ge
      (alternatingSixUniversalCoverSylowProjection_ker_le_center 2)
  rw [natCard_center_sylowTwo_alternatingSixUniversalCover,
    natCard_alternatingSixUniversalCoverSylowTwoProjection_ker]

/-- Quotienting the fixed cover Sylow subgroup by its intrinsic center
recovers the target Sylow subgroup in `A₆`. -/
def alternatingSixUniversalCoverSylowTwoQuotientCenterEquivTarget :
    (alternatingSixUniversalCoverSylow 2) ⧸
        Subgroup.center (alternatingSixUniversalCoverSylow 2) ≃*
      alternatingSixUniversalCoverTargetSylow 2 :=
  (QuotientGroup.quotientMulEquivOfEq
      alternatingSixUniversalCoverSylowTwoProjection_ker_eq_center.symm).trans
    alternatingSixUniversalCoverSylowTwoQuotientEquivTarget

/-- The central quotient of the generalized-quaternion Sylow subgroup is
the dihedral group of order eight. -/
def alternatingSixUniversalCoverSylowTwoQuotientCenterEquivDihedralFour :
    (alternatingSixUniversalCoverSylow 2) ⧸
        Subgroup.center (alternatingSixUniversalCoverSylow 2) ≃*
      DihedralGroup 4 :=
  alternatingSixUniversalCoverSylowTwoQuotientCenterEquivTarget.trans
    alternatingSixUniversalCoverTargetSylowTwoEquivDihedralFour

/-- Conjugation by elements of the fixed Sylow subgroup, regarded as a
subaction of the full normalizer action. -/
def alternatingSixUniversalCoverSylowTwoInnerAction :
    (alternatingSixUniversalCoverSylow 2 :
        Subgroup AlternatingSixUniversalCover) →*
      MulAut
        (alternatingSixUniversalCoverSylow 2 :
          Subgroup AlternatingSixUniversalCover) :=
  (alternatingSixUniversalCoverSylow 2 :
      Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.comp
    (Subgroup.inclusion
      (alternatingSixUniversalCoverSylow 2 :
        Subgroup AlternatingSixUniversalCover).le_normalizer)

/-- The kernel of the inner action is the intrinsic center. -/
@[simp]
theorem alternatingSixUniversalCoverSylowTwoInnerAction_ker :
    alternatingSixUniversalCoverSylowTwoInnerAction.ker =
      Subgroup.center
        (alternatingSixUniversalCoverSylow 2 :
          Subgroup AlternatingSixUniversalCover) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hx y
    have happ := DFunLike.congr_fun hx y
    have hval := congrArg Subtype.val happ
    change
      (x : AlternatingSixUniversalCover) *
            (y : AlternatingSixUniversalCover) *
            (x : AlternatingSixUniversalCover)⁻¹ =
          (y : AlternatingSixUniversalCover)
      at hval
    apply Subtype.ext
    change
      (y : AlternatingSixUniversalCover) *
          (x : AlternatingSixUniversalCover) =
        (x : AlternatingSixUniversalCover) *
          (y : AlternatingSixUniversalCover)
    have hmul :=
      congrArg
        (fun g : AlternatingSixUniversalCover =>
          g * (x : AlternatingSixUniversalCover))
        hval
    have hxy :
        (x : AlternatingSixUniversalCover) *
            (y : AlternatingSixUniversalCover) =
          (y : AlternatingSixUniversalCover) *
            (x : AlternatingSixUniversalCover) := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
    exact hxy.symm
  · intro hx
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change
      (x : AlternatingSixUniversalCover) *
            (y : AlternatingSixUniversalCover) *
            (x : AlternatingSixUniversalCover)⁻¹ =
          (y : AlternatingSixUniversalCover)
    have hcommute :=
      congrArg Subtype.val (hx y)
    change
      (y : AlternatingSixUniversalCover) *
          (x : AlternatingSixUniversalCover) =
        (x : AlternatingSixUniversalCover) *
          (y : AlternatingSixUniversalCover)
      at hcommute
    calc
      (x : AlternatingSixUniversalCover) *
            (y : AlternatingSixUniversalCover) *
            (x : AlternatingSixUniversalCover)⁻¹ =
          ((y : AlternatingSixUniversalCover) *
            (x : AlternatingSixUniversalCover)) *
            (x : AlternatingSixUniversalCover)⁻¹ :=
        congrArg
          (fun g : AlternatingSixUniversalCover =>
            g * (x : AlternatingSixUniversalCover)⁻¹)
          hcommute.symm
      _ = (y : AlternatingSixUniversalCover) := by group

/-- The inner automorphism group of the fixed cover Sylow subgroup has
order eight. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowTwoInnerAction_range :
    Nat.card alternatingSixUniversalCoverSylowTwoInnerAction.range = 8 := by
  let P :=
    (alternatingSixUniversalCoverSylow 2 :
      Subgroup AlternatingSixUniversalCover)
  let f := alternatingSixUniversalCoverSylowTwoInnerAction
  have hker : Nat.card f.ker = 2 := by
    change
      Nat.card alternatingSixUniversalCoverSylowTwoInnerAction.ker = 2
    rw [alternatingSixUniversalCoverSylowTwoInnerAction_ker,
      natCard_center_sylowTwo_alternatingSixUniversalCover]
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card P := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ = Nat.card P :=
        f.ker.card_mul_index
  have hP : Nat.card P = 16 := by
    change
      Nat.card (alternatingSixUniversalCoverSylow 2) = 16
    exact natCard_alternatingSixUniversalCoverSylowTwo_exact
  change Nat.card f.range = 8
  rw [hker, hP] at hcard
  omega

/-- Every inner automorphism induced by the Sylow subgroup belongs to the
full normalizer-action range. -/
theorem alternatingSixUniversalCoverSylowTwoInnerAction_range_le_normalizer_range :
    alternatingSixUniversalCoverSylowTwoInnerAction.range ≤
      (alternatingSixUniversalCoverSylow 2 :
        Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range := by
  rintro φ ⟨x, rfl⟩
  exact
    ⟨Subgroup.inclusion
        (alternatingSixUniversalCoverSylow 2 :
          Subgroup AlternatingSixUniversalCover).le_normalizer x,
      rfl⟩

/-- The full normalizer induces exactly eight automorphisms on the fixed
Sylow subgroup. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowTwo_normalizerMonoidHom_range :
    Nat.card
        (alternatingSixUniversalCoverSylow 2 :
          Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range =
      8 := by
  have hlower :
      Nat.card alternatingSixUniversalCoverSylowTwoInnerAction.range ≤
        Nat.card
          (alternatingSixUniversalCoverSylow 2 :
            Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range :=
    Nat.card_le_card_of_injective
      (Subgroup.inclusion
        alternatingSixUniversalCoverSylowTwoInnerAction_range_le_normalizer_range)
      (Subgroup.inclusion_injective
        alternatingSixUniversalCoverSylowTwoInnerAction_range_le_normalizer_range)
  rw [natCard_alternatingSixUniversalCoverSylowTwoInnerAction_range]
    at hlower
  rcases
      natCard_alternatingSixUniversalCoverSylowTwo_normalizerMonoidHom_range_cases
    with hfour | height
  · rw [hfour] at hlower
    omega
  · exact height

/-- The centralizer of the fixed cover Sylow `2`-subgroup has exact order
six. -/
@[simp]
theorem natCard_centralizer_alternatingSixUniversalCoverSylowTwo :
    Nat.card
        (Subgroup.centralizer
          (alternatingSixUniversalCoverSylow 2 :
            Set AlternatingSixUniversalCover)) =
      6 :=
  natCard_centralizer_eq_six_iff_normalizerMonoidHom_range_eq_eight.mpr
    natCard_alternatingSixUniversalCoverSylowTwo_normalizerMonoidHom_range

/-- The fixed Sylow centralizer is exactly the center of the universal
cover. -/
theorem centralizer_alternatingSixUniversalCoverSylowTwo_eq_center :
    Subgroup.centralizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover) =
      Subgroup.center AlternatingSixUniversalCover := by
  symm
  apply
    Subgroup.eq_of_le_of_card_ge
      (Subgroup.center_le_centralizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover))
  rw [natCard_centralizer_alternatingSixUniversalCoverSylowTwo,
    alternatingSixHopfKernelHasOrderSix.center]

/-- The restricted centralizer projection is trivial. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowTwoCentralizerProjection_range :
    Nat.card
        alternatingSixUniversalCoverSylowTwoCentralizerProjection.range =
      1 := by
  let f :=
    alternatingSixUniversalCoverSylowTwoCentralizerProjection
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.centralizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.centralizer
              (alternatingSixUniversalCoverSylow 2 :
                Set AlternatingSixUniversalCover)) :=
        f.ker.card_mul_index
  change Nat.card f.range = 1
  rw [
    natCard_alternatingSixUniversalCoverSylowTwoCentralizerProjection_ker,
    natCard_centralizer_alternatingSixUniversalCoverSylowTwo]
    at hcard
  omega

/-- The Sylow centralizer has relative index eight in its normalizer. -/
theorem relIndex_centralizer_alternatingSixUniversalCoverSylowTwo_normalizer :
    (Subgroup.centralizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover)).relIndex
      (Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover)) =
      8 := by
  let P :=
    (alternatingSixUniversalCoverSylow 2 :
      Subgroup AlternatingSixUniversalCover)
  change
    ((Subgroup.centralizer
      (P : Set AlternatingSixUniversalCover)).subgroupOf
          (Subgroup.normalizer
            (P : Set AlternatingSixUniversalCover))).index =
      8
  rw [← P.normalizerMonoidHom_ker,
    Subgroup.index_ker]
  change
    Nat.card
        (alternatingSixUniversalCoverSylow 2 :
          Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range =
      8
  exact
    natCard_alternatingSixUniversalCoverSylowTwo_normalizerMonoidHom_range

end GroupTheory
end McKayConjecture
