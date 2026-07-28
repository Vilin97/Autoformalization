/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixHopfKernelProof
import McKayConjecture.GroupTheory.AlternatingSixSylowThreeNormalizer
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer

/-!
# Three-local structure of the universal cover of `A₆`

The order-six Schur-multiplier calculation and the exact target normalizer
calculation determine the following unconditional local data for the
canonical universal cover:

* its fixed Sylow `3`-subgroup has order twenty-seven;
* projection onto its elementary-abelian target has central cyclic kernel
  of order three;
* the lifted normalizer has order two hundred sixteen; and
* quotienting that normalizer by its order-six central projection kernel
  recovers the order-thirty-six normalizer in `A₆`.

Determining the multiplication in the order-twenty-seven Sylow subgroup
(classically, it is extraspecial) is deliberately left separate from these
cardinality and quotient facts.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixUniversalCoverThreeFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The fixed Sylow `3`-subgroup of the canonical cover is the canonical
central-extension lift of its target image. -/
theorem alternatingSixUniversalCoverSylowThree_eq_sylowLift :
    alternatingSixUniversalCoverSylow 3 =
      alternatingSixUniversalCentralExtension.toCentralExtension.sylowLift
        (alternatingSixUniversalCoverTargetSylow 3) := by
  apply
    (CentralExtension.eq_sylowLift_iff_mapSurjective_eq
      alternatingSixUniversalCentralExtension.toCentralExtension
        (alternatingSixUniversalCoverTargetSylow 3)
        (alternatingSixUniversalCoverSylow 3)).mpr
  rfl

/-- The fixed Sylow `3`-subgroup of the canonical cover has order
twenty-seven. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowThree_exact :
    Nat.card (alternatingSixUniversalCoverSylow 3) = 27 :=
  alternatingSixHopfKernelHasOrderSix.sylowThree

/-- Its target image is elementary abelian of order nine. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverTargetSylowThree :
    Nat.card (alternatingSixUniversalCoverTargetSylow 3) = 9 :=
  natCard_sylowThree_alternatingSix
    (alternatingSixUniversalCoverTargetSylow 3)

/-- The central kernel of the restricted Sylow projection has order three. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowThreeProjection_ker :
    Nat.card (alternatingSixUniversalCoverSylowProjection 3).ker = 3 := by
  rw [natCard_alternatingSixUniversalCoverSylowProjection_ker,
    alternatingSixHopfKernelHasOrderSix.center]
  have hfactor :
      Nat.factorization 6 3 = 1 := by
    conv_lhs =>
      rw [show 6 = 2 * 3 by norm_num]
    rw [Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      Nat.prime_two.factorization,
      Nat.prime_three.factorization]
    norm_num [Finsupp.single_apply]
  rw [hfactor]
  norm_num

/-- The intersection of the order-six center with the fixed Sylow
`3`-subgroup has order three. -/
@[simp]
theorem natCard_center_subgroupOf_alternatingSixUniversalCoverSylowThree :
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (alternatingSixUniversalCoverSylow 3)) =
      3 := by
  rw [← alternatingSixUniversalCoverSylowProjection_ker,
    natCard_alternatingSixUniversalCoverSylowThreeProjection_ker]

/-- The central kernel inside the fixed Sylow `3`-subgroup is cyclic. -/
theorem alternatingSixUniversalCoverSylowThreeProjection_ker_isCyclic :
    IsCyclic
      (alternatingSixUniversalCoverSylowProjection 3).ker :=
  isCyclic_of_prime_card
    natCard_alternatingSixUniversalCoverSylowThreeProjection_ker

/-- Quotienting the fixed cover Sylow subgroup by its central order-three
kernel recovers its target Sylow subgroup in `A₆`. -/
def alternatingSixUniversalCoverSylowThreeQuotientEquivTarget :
    (alternatingSixUniversalCoverSylow 3) ⧸
        (alternatingSixUniversalCoverSylowProjection 3).ker ≃*
      alternatingSixUniversalCoverTargetSylow 3 :=
  QuotientGroup.quotientKerEquivOfSurjective
    (alternatingSixUniversalCoverSylowProjection 3)
    (alternatingSixUniversalCoverSylowProjection_surjective 3)

/-- The fixed cover Sylow `3`-subgroup is not cyclic, since its quotient
onto the target elementary-abelian Sylow subgroup is not cyclic. -/
theorem alternatingSixUniversalCoverSylowThree_not_isCyclic :
    ¬IsCyclic (alternatingSixUniversalCoverSylow 3) := by
  intro hcyclic
  have htarget :
      IsCyclic
        (alternatingSixUniversalCoverTargetSylow 3) := by
    letI :
        IsCyclic (alternatingSixUniversalCoverSylow 3) :=
      hcyclic
    exact
      isCyclic_of_surjective
        (alternatingSixUniversalCoverSylowProjection 3)
        (alternatingSixUniversalCoverSylowProjection_surjective 3)
  exact
    sylowThree_alternatingSix_not_isCyclic
      (alternatingSixUniversalCoverTargetSylow 3)
      htarget

/-! ### The lifted normalizer -/

/-- The fixed Sylow `3`-normalizer in the canonical cover has order
two hundred sixteen. -/
@[simp]
theorem natCard_normalizer_alternatingSixUniversalCoverSylowThree :
    Nat.card
        (Subgroup.normalizer
          (alternatingSixUniversalCoverSylow 3 :
            Set AlternatingSixUniversalCover)) =
      216 := by
  have h :=
    CentralExtension.sylowNormalizer_card_eq
      alternatingSixUniversalCentralExtension.toCentralExtension
        (alternatingSixUniversalCoverTargetSylow 3)
  have htarget :
      Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverTargetSylow 3 :
              Set AlternatingSix)) =
        36 :=
    natCard_normalizer_sylowThree_alternatingSix
      (alternatingSixUniversalCoverTargetSylow 3)
  rw [← alternatingSixUniversalCoverSylowThree_eq_sylowLift,
    alternatingSixUniversalCentralExtension_ker_eq_center,
    alternatingSixHopfKernelHasOrderSix.center,
    htarget] at h
  norm_num at h ⊢
  exact h

/-- The center, viewed inside the fixed cover Sylow `3`-normalizer, has
order six. -/
@[simp]
theorem natCard_center_subgroupOf_alternatingSixUniversalCoverSylowThreeNormalizer :
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 3 :
              Set AlternatingSixUniversalCover))) =
      6 := by
  calc
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 3 :
              Set AlternatingSixUniversalCover))) =
        Nat.card (Subgroup.center AlternatingSixUniversalCover) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.center_le_normalizer
            (alternatingSixUniversalCoverSylow 3 :
              Set AlternatingSixUniversalCover))).toEquiv
    _ = 6 :=
      alternatingSixHopfKernelHasOrderSix.center

/-- Projection restricts to a central extension from the fixed cover
Sylow `3`-normalizer onto the corresponding normalizer in `A₆`. -/
def alternatingSixUniversalCoverSylowThreeNormalizerCentralExtension :
    CentralExtension
      (Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 3 :
          Set AlternatingSixUniversalCover))
      (Subgroup.normalizer
        (alternatingSixUniversalCoverTargetSylow 3 :
          Set AlternatingSix)) := by
  rw [alternatingSixUniversalCoverSylowThree_eq_sylowLift]
  exact
    alternatingSixUniversalCentralExtension.toCentralExtension
      |>.sylowNormalizerCentralExtension
        (alternatingSixUniversalCoverTargetSylow 3)

/-- The restricted normalizer projection has a central kernel of order six. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowThreeNormalizerProjection_ker :
    Nat.card
        (CentralExtension.projection
          alternatingSixUniversalCoverSylowThreeNormalizerCentralExtension).ker =
      6 := by
  let C :=
    alternatingSixUniversalCoverSylowThreeNormalizerCentralExtension
  let f := C.projection
  have hrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr C.surjective
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 3 :
              Set AlternatingSixUniversalCover)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.normalizer
              (alternatingSixUniversalCoverSylow 3 :
                Set AlternatingSixUniversalCover)) :=
        f.ker.card_mul_index
  have htarget :
      Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverTargetSylow 3 :
              Set AlternatingSix)) =
        36 :=
    natCard_normalizer_sylowThree_alternatingSix
      (alternatingSixUniversalCoverTargetSylow 3)
  have hsource :
      Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 3 :
              Set AlternatingSixUniversalCover)) =
        216 :=
    natCard_normalizer_alternatingSixUniversalCoverSylowThree
  change Nat.card f.ker = 6
  rw [hrange, Subgroup.card_top, htarget, hsource] at hcard
  omega

/-- Quotienting the cover normalizer by its central projection kernel
recovers the order-thirty-six Sylow normalizer in `A₆`. -/
def alternatingSixUniversalCoverSylowThreeNormalizerQuotientEquiv :
    (Subgroup.normalizer
          (alternatingSixUniversalCoverSylow 3 :
            Set AlternatingSixUniversalCover)) ⧸
        (CentralExtension.projection
          alternatingSixUniversalCoverSylowThreeNormalizerCentralExtension).ker ≃*
      Subgroup.normalizer
        (alternatingSixUniversalCoverTargetSylow 3 :
          Set AlternatingSix) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (CentralExtension.projection
      alternatingSixUniversalCoverSylowThreeNormalizerCentralExtension)
    (CentralExtension.surjective
      alternatingSixUniversalCoverSylowThreeNormalizerCentralExtension)

/-- The fixed Sylow `3`-subgroup has relative index eight in its cover
normalizer. -/
theorem relIndex_alternatingSixUniversalCoverSylowThree_normalizer :
    (alternatingSixUniversalCoverSylow 3 :
        Subgroup AlternatingSixUniversalCover).relIndex
      (Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 3 :
          Set AlternatingSixUniversalCover)) =
      8 := by
  let P :=
    alternatingSixUniversalCoverSylow 3
  let N :=
    Subgroup.normalizer
      (P : Set AlternatingSixUniversalCover)
  change
    (P : Subgroup AlternatingSixUniversalCover).relIndex N = 8
  have hcardSubgroup :
      Nat.card
          ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N) =
        27 := by
    calc
      Nat.card
          ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N) =
          Nat.card P :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (P : Subgroup AlternatingSixUniversalCover).le_normalizer).toEquiv
      _ = 27 :=
        natCard_alternatingSixUniversalCoverSylowThree_exact
  have hcard :=
    ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N).card_mul_index
  change
    Nat.card
        ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N) *
        (P : Subgroup AlternatingSixUniversalCover).relIndex N =
      Nat.card N at hcard
  have hnormalizer :
      Nat.card N = 216 :=
    natCard_normalizer_alternatingSixUniversalCoverSylowThree
  rw [hcardSubgroup, hnormalizer] at hcard
  omega

/-- The fixed cover Sylow `3`-normalizer is proper. -/
theorem normalizer_alternatingSixUniversalCoverSylowThree_ne_top :
    Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 3 :
          Set AlternatingSixUniversalCover) ≠
      ⊤ := by
  intro htop
  have hcard :=
    natCard_normalizer_alternatingSixUniversalCoverSylowThree
  rw [htop, Subgroup.card_top,
    alternatingSixHopfKernelHasOrderSix.cover] at hcard
  omega

end GroupTheory
end McKayConjecture
