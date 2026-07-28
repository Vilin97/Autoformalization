/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixHopfKernelProof
import McKayConjecture.GroupTheory.AlternatingSixSylowTwoNormalizer
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer

/-!
# Two-local structure of the universal cover of `A₆`

The order-six Schur-multiplier computation and the exact target normalizer
calculation determine the following unconditional local data for the
canonical universal cover:

* its fixed Sylow `2`-subgroup has order sixteen;
* projection onto its dihedral target has central cyclic kernel of order two;
* the lifted normalizer has order forty-eight; and
* quotienting that normalizer by its order-six central projection kernel
  recovers the self-normalizing dihedral subgroup in `A₆`.

Identifying the multiplication in the order-sixteen Sylow subgroup
(classically, it is generalized quaternion) is kept separate from these
cardinality and quotient facts.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixUniversalCoverTwoFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The fixed Sylow `2`-subgroup of the canonical cover is the canonical
central-extension lift of its target image. -/
theorem alternatingSixUniversalCoverSylowTwo_eq_sylowLift :
    alternatingSixUniversalCoverSylow 2 =
      alternatingSixUniversalCentralExtension.toCentralExtension.sylowLift
        (alternatingSixUniversalCoverTargetSylow 2) := by
  apply
    (CentralExtension.eq_sylowLift_iff_mapSurjective_eq
      alternatingSixUniversalCentralExtension.toCentralExtension
        (alternatingSixUniversalCoverTargetSylow 2)
        (alternatingSixUniversalCoverSylow 2)).mpr
  rfl

/-- The fixed Sylow `2`-subgroup of the canonical cover has order
sixteen. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowTwo_exact :
    Nat.card (alternatingSixUniversalCoverSylow 2) = 16 :=
  alternatingSixHopfKernelHasOrderSix.sylowTwo

/-- Its target image is dihedral of order eight. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverTargetSylowTwo :
    Nat.card (alternatingSixUniversalCoverTargetSylow 2) = 8 :=
  natCard_sylowTwo_alternatingSix
    (alternatingSixUniversalCoverTargetSylow 2)

/-- The target image is explicitly isomorphic to `D₈`. -/
def alternatingSixUniversalCoverTargetSylowTwoEquivDihedralFour :
    alternatingSixUniversalCoverTargetSylow 2 ≃*
      DihedralGroup 4 :=
  alternatingSixSylowTwoEquivDihedralFour
    (alternatingSixUniversalCoverTargetSylow 2)

/-- The central kernel of the restricted Sylow projection has order two. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowTwoProjection_ker :
    Nat.card (alternatingSixUniversalCoverSylowProjection 2).ker = 2 := by
  rw [natCard_alternatingSixUniversalCoverSylowProjection_ker,
    alternatingSixHopfKernelHasOrderSix.center]
  have hfactor :
      Nat.factorization 6 2 = 1 := by
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
`2`-subgroup has order two. -/
@[simp]
theorem natCard_center_subgroupOf_alternatingSixUniversalCoverSylowTwo :
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (alternatingSixUniversalCoverSylow 2)) =
      2 := by
  rw [← alternatingSixUniversalCoverSylowProjection_ker,
    natCard_alternatingSixUniversalCoverSylowTwoProjection_ker]

/-- The central kernel inside the fixed Sylow `2`-subgroup is cyclic. -/
theorem alternatingSixUniversalCoverSylowTwoProjection_ker_isCyclic :
    IsCyclic
      (alternatingSixUniversalCoverSylowProjection 2).ker :=
  isCyclic_of_prime_card
    natCard_alternatingSixUniversalCoverSylowTwoProjection_ker

/-- Quotienting the fixed cover Sylow subgroup by its central order-two
kernel recovers its dihedral target Sylow subgroup in `A₆`. -/
def alternatingSixUniversalCoverSylowTwoQuotientEquivTarget :
    (alternatingSixUniversalCoverSylow 2) ⧸
        (alternatingSixUniversalCoverSylowProjection 2).ker ≃*
      alternatingSixUniversalCoverTargetSylow 2 :=
  QuotientGroup.quotientKerEquivOfSurjective
    (alternatingSixUniversalCoverSylowProjection 2)
    (alternatingSixUniversalCoverSylowProjection_surjective 2)

/-- The fixed cover Sylow `2`-subgroup is not cyclic, since its quotient
onto the target dihedral Sylow subgroup is not cyclic. -/
theorem alternatingSixUniversalCoverSylowTwo_not_isCyclic :
    ¬IsCyclic (alternatingSixUniversalCoverSylow 2) := by
  intro hcyclic
  have htarget :
      IsCyclic
        (alternatingSixUniversalCoverTargetSylow 2) := by
    letI :
        IsCyclic (alternatingSixUniversalCoverSylow 2) :=
      hcyclic
    exact
      isCyclic_of_surjective
        (alternatingSixUniversalCoverSylowProjection 2)
        (alternatingSixUniversalCoverSylowProjection_surjective 2)
  exact
    sylowTwo_alternatingSix_not_isCyclic
      (alternatingSixUniversalCoverTargetSylow 2)
      htarget

/-! ### The lifted normalizer -/

/-- The fixed Sylow `2`-normalizer in the canonical cover has order
forty-eight. -/
@[simp]
theorem natCard_normalizer_alternatingSixUniversalCoverSylowTwo :
    Nat.card
        (Subgroup.normalizer
          (alternatingSixUniversalCoverSylow 2 :
            Set AlternatingSixUniversalCover)) =
      48 := by
  have h :=
    CentralExtension.sylowNormalizer_card_eq
      alternatingSixUniversalCentralExtension.toCentralExtension
        (alternatingSixUniversalCoverTargetSylow 2)
  have htarget :
      Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverTargetSylow 2 :
              Set AlternatingSix)) =
        8 :=
    natCard_normalizer_sylowTwo_alternatingSix
      (alternatingSixUniversalCoverTargetSylow 2)
  rw [← alternatingSixUniversalCoverSylowTwo_eq_sylowLift,
    alternatingSixUniversalCentralExtension_ker_eq_center,
    alternatingSixHopfKernelHasOrderSix.center,
    htarget] at h
  norm_num at h ⊢
  exact h

/-- The center, viewed inside the fixed cover Sylow `2`-normalizer, has
order six. -/
@[simp]
theorem natCard_center_subgroupOf_alternatingSixUniversalCoverSylowTwoNormalizer :
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover))) =
      6 := by
  calc
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover))) =
        Nat.card (Subgroup.center AlternatingSixUniversalCover) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.center_le_normalizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover))).toEquiv
    _ = 6 :=
      alternatingSixHopfKernelHasOrderSix.center

/-- Projection restricts to a central extension from the fixed cover
Sylow `2`-normalizer onto the corresponding normalizer in `A₆`. -/
def alternatingSixUniversalCoverSylowTwoNormalizerCentralExtension :
    CentralExtension
      (Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover))
      (Subgroup.normalizer
        (alternatingSixUniversalCoverTargetSylow 2 :
          Set AlternatingSix)) := by
  rw [alternatingSixUniversalCoverSylowTwo_eq_sylowLift]
  exact
    alternatingSixUniversalCentralExtension.toCentralExtension
      |>.sylowNormalizerCentralExtension
        (alternatingSixUniversalCoverTargetSylow 2)

/-- The restricted normalizer projection has a central kernel of order
six. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowTwoNormalizerProjection_ker :
    Nat.card
        (CentralExtension.projection
          alternatingSixUniversalCoverSylowTwoNormalizerCentralExtension).ker =
      6 := by
  let C :=
    alternatingSixUniversalCoverSylowTwoNormalizerCentralExtension
  let f := C.projection
  have hrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr C.surjective
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.normalizer
              (alternatingSixUniversalCoverSylow 2 :
                Set AlternatingSixUniversalCover)) :=
        f.ker.card_mul_index
  have htarget :
      Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverTargetSylow 2 :
              Set AlternatingSix)) =
        8 :=
    natCard_normalizer_sylowTwo_alternatingSix
      (alternatingSixUniversalCoverTargetSylow 2)
  have hsource :
      Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover)) =
        48 :=
    natCard_normalizer_alternatingSixUniversalCoverSylowTwo
  change Nat.card f.ker = 6
  rw [hrange, Subgroup.card_top, htarget, hsource] at hcard
  omega

/-- Quotienting the cover normalizer by its central projection kernel
recovers the order-eight Sylow normalizer in `A₆`. -/
def alternatingSixUniversalCoverSylowTwoNormalizerQuotientEquiv :
    (Subgroup.normalizer
          (alternatingSixUniversalCoverSylow 2 :
            Set AlternatingSixUniversalCover)) ⧸
        (CentralExtension.projection
          alternatingSixUniversalCoverSylowTwoNormalizerCentralExtension).ker ≃*
      Subgroup.normalizer
        (alternatingSixUniversalCoverTargetSylow 2 :
          Set AlternatingSix) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (CentralExtension.projection
      alternatingSixUniversalCoverSylowTwoNormalizerCentralExtension)
    (CentralExtension.surjective
      alternatingSixUniversalCoverSylowTwoNormalizerCentralExtension)

/-- The fixed Sylow `2`-subgroup has relative index three in its cover
normalizer. -/
theorem relIndex_alternatingSixUniversalCoverSylowTwo_normalizer :
    (alternatingSixUniversalCoverSylow 2 :
        Subgroup AlternatingSixUniversalCover).relIndex
      (Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover)) =
      3 := by
  let P :=
    alternatingSixUniversalCoverSylow 2
  let N :=
    Subgroup.normalizer
      (P : Set AlternatingSixUniversalCover)
  change
    (P : Subgroup AlternatingSixUniversalCover).relIndex N = 3
  have hcardSubgroup :
      Nat.card
          ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N) =
        16 := by
    calc
      Nat.card
          ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N) =
          Nat.card P :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (P : Subgroup AlternatingSixUniversalCover).le_normalizer).toEquiv
      _ = 16 :=
        natCard_alternatingSixUniversalCoverSylowTwo_exact
  have hcard :=
    ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N).card_mul_index
  change
    Nat.card
        ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N) *
        (P : Subgroup AlternatingSixUniversalCover).relIndex N =
      Nat.card N at hcard
  have hnormalizer :
      Nat.card N = 48 :=
    natCard_normalizer_alternatingSixUniversalCoverSylowTwo
  rw [hcardSubgroup, hnormalizer] at hcard
  omega

/-- The quotient of the cover normalizer by its normal Sylow subgroup has
order three. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowTwoNormalizerQuotientSylow :
    Nat.card
        ((Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 2 :
              Set AlternatingSixUniversalCover)) ⧸
          ((alternatingSixUniversalCoverSylow 2 :
              Subgroup AlternatingSixUniversalCover).subgroupOf
            (Subgroup.normalizer
              (alternatingSixUniversalCoverSylow 2 :
                Set AlternatingSixUniversalCover)))) =
      3 := by
  change
    (alternatingSixUniversalCoverSylow 2 :
        Subgroup AlternatingSixUniversalCover).relIndex
      (Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover)) =
      3
  exact
    relIndex_alternatingSixUniversalCoverSylowTwo_normalizer

/-- The fixed cover Sylow `2`-normalizer is proper. -/
theorem normalizer_alternatingSixUniversalCoverSylowTwo_ne_top :
    Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 2 :
          Set AlternatingSixUniversalCover) ≠
      ⊤ := by
  intro htop
  have hcard :=
    natCard_normalizer_alternatingSixUniversalCoverSylowTwo
  rw [htop, Subgroup.card_top,
    alternatingSixHopfKernelHasOrderSix.cover] at hcard
  omega

end GroupTheory
end McKayConjecture
