/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverThreeCentralizer
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverThreeLocalStructure

/-!
# The proved quotient model of the three-normalizer in `6.A₆`

Let `P` be the fixed Sylow `3`-subgroup of the canonical universal cover
and let `N = N_{6.A₆}(P)`.  The currently proved structure of `N` is:

* `|N| = 216`;
* `Z(N)` is exactly the ambient order-six center;
* `N / Z(N)` is the order-thirty-six image of conjugation on `P`; and
* the same quotient is the concrete Sylow normalizer in `A₆`.

In particular, the action image and the target normalizer are equivalent.
This is the strongest model presently justified by the Lean development.
No complement to the center, direct-product decomposition, or semidirect
splitting of `N` is asserted here.  Such a splitting would be additional
group-theoretic data and cannot be recovered from the cardinalities and
quotient equivalences alone.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixUniversalCoverThreeNormalizerModelFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The actual fixed Sylow-three normalizer in the canonical universal
cover. -/
abbrev AlternatingSixUniversalCoverThreeNormalizer :=
  Subgroup.normalizer
    (alternatingSixUniversalCoverSylow 3 :
      Set AlternatingSixUniversalCover)

/-- The concrete corresponding Sylow-three normalizer in `A₆`. -/
abbrev AlternatingSixThreeTargetNormalizer :=
  Subgroup.normalizer
    (alternatingSixUniversalCoverTargetSylow 3 :
      Set AlternatingSix)

/-- The image of the fixed cover normalizer in the automorphism group of
its Sylow subgroup. -/
abbrev AlternatingSixUniversalCoverThreeNormalizerActionRange :=
  (alternatingSixUniversalCoverSylow 3 :
      Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range

/-- The intrinsic center of the fixed normalizer is precisely the ambient
center, viewed inside the normalizer. -/
theorem center_alternatingSixUniversalCoverThreeNormalizer_eq_ambientCenter :
    Subgroup.center AlternatingSixUniversalCoverThreeNormalizer =
      (Subgroup.center AlternatingSixUniversalCover).subgroupOf
        AlternatingSixUniversalCoverThreeNormalizer := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxCentralizesSylow :
        (x : AlternatingSixUniversalCover) ∈
          Subgroup.centralizer
            (alternatingSixUniversalCoverSylow 3 :
              Set AlternatingSixUniversalCover) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let yN : AlternatingSixUniversalCoverThreeNormalizer :=
        ⟨y,
          (alternatingSixUniversalCoverSylow 3 :
              Subgroup AlternatingSixUniversalCover).le_normalizer hy⟩
      have hxy :=
        Subgroup.mem_center_iff.mp hx yN
      exact congrArg Subtype.val hxy
    change
      (x : AlternatingSixUniversalCover) ∈
        Subgroup.centralizer
          (((alternatingSixUniversalCoverSylow 3 :
              Sylow 3 AlternatingSixUniversalCover) :
            Subgroup AlternatingSixUniversalCover) :
            Set AlternatingSixUniversalCover)
      at hxCentralizesSylow
    rw [
      centralizer_sylowThree_alternatingSixUniversalCover_eq_center
        (alternatingSixUniversalCoverSylow 3)]
      at hxCentralizesSylow
    exact hxCentralizesSylow
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hx
        (y : AlternatingSixUniversalCover)

/-- The center of the fixed Sylow-three normalizer has order six. -/
@[simp]
theorem natCard_center_alternatingSixUniversalCoverThreeNormalizer :
    Nat.card
        (Subgroup.center
          AlternatingSixUniversalCoverThreeNormalizer) =
      6 := by
  rw [
    center_alternatingSixUniversalCoverThreeNormalizer_eq_ambientCenter]
  calc
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          AlternatingSixUniversalCoverThreeNormalizer) =
        Nat.card (Subgroup.center AlternatingSixUniversalCover) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.center_le_normalizer
            (alternatingSixUniversalCoverSylow 3 :
              Set AlternatingSixUniversalCover))).toEquiv
    _ = 6 :=
      alternatingSixHopfKernelHasOrderSix.center

/-- The kernel of the fixed normalizer action is its intrinsic center. -/
theorem alternatingSixUniversalCoverThreeNormalizer_action_ker_eq_center :
    (alternatingSixUniversalCoverSylow 3 :
        Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.ker =
      Subgroup.center AlternatingSixUniversalCoverThreeNormalizer := by
  calc
    (alternatingSixUniversalCoverSylow 3 :
        Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.ker =
        (Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.normalizer
            ((alternatingSixUniversalCoverSylow 3 :
                Subgroup AlternatingSixUniversalCover) :
              Set AlternatingSixUniversalCover)) :=
      sylowThree_alternatingSixUniversalCover_normalizerMonoidHom_ker_eq_center
        (alternatingSixUniversalCoverSylow 3)
    _ = Subgroup.center
          AlternatingSixUniversalCoverThreeNormalizer :=
      center_alternatingSixUniversalCoverThreeNormalizer_eq_ambientCenter.symm

/-- The kernel of the fixed normalizer projection to `A₆` is its intrinsic
center. -/
theorem alternatingSixUniversalCoverThreeNormalizer_projection_ker_eq_center :
    (CentralExtension.projection
      alternatingSixUniversalCoverSylowThreeNormalizerCentralExtension).ker =
      Subgroup.center AlternatingSixUniversalCoverThreeNormalizer := by
  apply Subgroup.eq_of_le_of_card_ge
    (CentralExtension.ker_le_center
      alternatingSixUniversalCoverSylowThreeNormalizerCentralExtension)
  rw [
    natCard_center_alternatingSixUniversalCoverThreeNormalizer,
    natCard_alternatingSixUniversalCoverSylowThreeNormalizerProjection_ker]

/-- Quotienting the fixed normalizer by its intrinsic center gives the
normalizer action image. -/
def alternatingSixUniversalCoverThreeNormalizerQuotientCenterEquivActionRange :
    AlternatingSixUniversalCoverThreeNormalizer ⧸
        Subgroup.center
          AlternatingSixUniversalCoverThreeNormalizer ≃*
      AlternatingSixUniversalCoverThreeNormalizerActionRange := by
  let f :=
    (alternatingSixUniversalCoverSylow 3 :
      Subgroup AlternatingSixUniversalCover).normalizerMonoidHom
  exact
    (QuotientGroup.quotientMulEquivOfEq
        alternatingSixUniversalCoverThreeNormalizer_action_ker_eq_center.symm).trans
      ((QuotientGroup.quotientMulEquivOfEq
          (MonoidHom.ker_rangeRestrict f).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          f.rangeRestrict f.rangeRestrict_surjective))

/-- Quotienting the fixed normalizer by its intrinsic center also gives
the concrete corresponding normalizer in `A₆`. -/
def alternatingSixUniversalCoverThreeNormalizerQuotientCenterEquivTarget :
    AlternatingSixUniversalCoverThreeNormalizer ⧸
        Subgroup.center
          AlternatingSixUniversalCoverThreeNormalizer ≃*
      AlternatingSixThreeTargetNormalizer :=
  (QuotientGroup.quotientMulEquivOfEq
      alternatingSixUniversalCoverThreeNormalizer_projection_ker_eq_center.symm).trans
    alternatingSixUniversalCoverSylowThreeNormalizerQuotientEquiv

/-- The proved action-range model is equivalent to the concrete
Sylow-three normalizer in `A₆`. -/
def alternatingSixUniversalCoverThreeNormalizerActionRangeEquivTarget :
    AlternatingSixUniversalCoverThreeNormalizerActionRange ≃*
      AlternatingSixThreeTargetNormalizer :=
  alternatingSixUniversalCoverThreeNormalizerQuotientCenterEquivActionRange.symm.trans
    alternatingSixUniversalCoverThreeNormalizerQuotientCenterEquivTarget

/-- Both quotient models have order thirty-six. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverThreeNormalizerActionRange :
    Nat.card
        AlternatingSixUniversalCoverThreeNormalizerActionRange =
      36 :=
  natCard_sylowThree_alternatingSixUniversalCover_normalizerActionRange
    (alternatingSixUniversalCoverSylow 3)

end GroupTheory
end McKayConjecture
