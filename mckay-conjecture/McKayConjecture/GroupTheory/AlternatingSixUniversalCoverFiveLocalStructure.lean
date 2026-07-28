/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixHopfKernelProof
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizerAction

/-!
# Exact five-local structure of the universal cover of `A₆`

The explicit Schur-cover calculation proves that the center of the canonical
free-presentation universal cover has order six.  This file records the
resulting unconditional five-local consequences in the fixed-cover notation
used by the inductive McKay reduction:

* the cover has order `2160`;
* its fixed Sylow `5`-subgroup has order five and is cyclic;
* projection identifies that Sylow subgroup with its image in `A₆`; and
* its normalizer has order sixty, with a cyclic order-thirty centralizer
  of index two.

These are the complete group-theoretic inputs to the remaining
character-table calculation at `p = 5`.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixUniversalCoverFiveFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The center of the canonical universal cover of `A₆` has order six. -/
@[simp]
theorem natCard_center_alternatingSixUniversalCover :
    Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6 :=
  alternatingSixHopfKernelHasOrderSix.center

/-- The canonical universal cover of `A₆` has order `2160`. -/
@[simp]
theorem natCard_alternatingSixUniversalCover_exact :
    Nat.card AlternatingSixUniversalCover = 2160 :=
  alternatingSixHopfKernelHasOrderSix.cover

/-- The center of the canonical cover is cyclic of order six. -/
theorem center_alternatingSixUniversalCover_isCyclic :
    IsCyclic (Subgroup.center AlternatingSixUniversalCover) :=
  alternatingSixHopfKernelHasOrderSix.centerIsCyclic

/-- The fixed Sylow `5`-subgroup of the canonical cover has order five. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowFive_exact :
    Nat.card (alternatingSixUniversalCoverSylow 5) = 5 :=
  alternatingSixHopfKernelHasOrderSix.sylowFive

/-- Projection identifies the fixed cover Sylow `5`-subgroup with its
target image in `A₆`. -/
def alternatingSixUniversalCoverSylowFiveEquivTarget :
    alternatingSixUniversalCoverSylow 5 ≃*
      alternatingSixUniversalCoverTargetSylow 5 :=
  alternatingSixHopfKernelHasOrderSix.sylowFiveEquivTarget

/-- The fixed Sylow `5`-subgroup of the canonical cover is cyclic. -/
theorem alternatingSixUniversalCoverSylowFive_isCyclic :
    IsCyclic (alternatingSixUniversalCoverSylow 5) :=
  alternatingSixHopfKernelHasOrderSix.sylowFiveIsCyclic

/-- Projection from the central-extension Sylow lift to its image in `A₆`
is injective at five. -/
theorem alternatingSixUniversalCoverSylowLiftProjectionFive_injective :
    Function.Injective
      (alternatingSixUniversalCentralExtension.toCentralExtension
        |>.sylowLiftProjection
          (alternatingSixUniversalCoverTargetSylow 5)) := by
  let E :=
    alternatingSixUniversalCentralExtension.toCentralExtension
  let S :=
    alternatingSixUniversalCoverTargetSylow 5
  letI : Fintype (E.sylowLift S) :=
    Fintype.ofFinite (E.sylowLift S)
  letI : Fintype S :=
    Fintype.ofFinite S
  by_contra hnot
  have hlt :=
    Fintype.card_lt_of_surjective_not_injective
      (E.sylowLiftProjection S)
      (E.sylowLiftProjection_surjective S)
      hnot
  have hltNat :
      Nat.card S < Nat.card (E.sylowLift S) := by
    simpa only [Nat.card_eq_fintype_card] using hlt
  have hsource :
      Nat.card (E.sylowLift S) = 5 := by
    rw [← alternatingSixUniversalCoverSylowFive_eq_sylowLift]
    exact natCard_alternatingSixUniversalCoverSylowFive_exact
  have htarget :
      Nat.card S = 5 :=
    natCard_sylowFive_alternatingSix S
  rw [hsource, htarget] at hltNat
  omega

/-- The order-six center and the order-five Sylow subgroup intersect
trivially. -/
theorem center_disjoint_alternatingSixUniversalCoverSylowFive :
    Disjoint
      (Subgroup.center AlternatingSixUniversalCover)
      (alternatingSixUniversalCoverSylow 5 :
        Subgroup AlternatingSixUniversalCover) := by
  apply Subgroup.disjoint_of_coprime_natCard
  rw [natCard_center_alternatingSixUniversalCover,
    natCard_alternatingSixUniversalCoverSylowFive_exact]
  norm_num

/-- The fixed Sylow `5`-normalizer in the canonical cover has order sixty. -/
@[simp]
theorem natCard_normalizer_alternatingSixUniversalCoverSylowFive_exact :
    Nat.card
        (Subgroup.normalizer
          (alternatingSixUniversalCoverSylow 5 :
            Set AlternatingSixUniversalCover)) =
      60 :=
  alternatingSixHopfKernelHasOrderSix.sylowFiveNormalizer

/-- The cover normalizer induces exactly the order-two automorphism group
already detected by the target `A₆` normalizer. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowFive_normalizerMonoidHom_range :
    Nat.card
        (alternatingSixUniversalCoverSylow 5 :
          Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.range =
      2 := by
  let E :=
    alternatingSixUniversalCentralExtension.toCentralExtension
  let S :=
    alternatingSixUniversalCoverTargetSylow 5
  have h :=
    E.natCard_normalizerMonoidHom_range_eq S
      alternatingSixUniversalCoverSylowLiftProjectionFive_injective
  rw [← alternatingSixUniversalCoverSylowFive_eq_sylowLift] at h
  exact
    h.trans
      (natCard_sylowFive_normalizerMonoidHom_range S)

/-- The kernel of the cover-normalizer action on its Sylow `5`-subgroup
has order thirty. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowFive_normalizerMonoidHom_ker :
    Nat.card
        (alternatingSixUniversalCoverSylow 5 :
          Subgroup AlternatingSixUniversalCover).normalizerMonoidHom.ker =
      30 := by
  let P :=
    alternatingSixUniversalCoverSylow 5
  let f :=
    (P : Subgroup AlternatingSixUniversalCover).normalizerMonoidHom
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
  have hrange : Nat.card f.range = 2 :=
    natCard_alternatingSixUniversalCoverSylowFive_normalizerMonoidHom_range
  have hnormalizer :
      Nat.card
          (Subgroup.normalizer
            (P : Set AlternatingSixUniversalCover)) =
        60 :=
    natCard_normalizer_alternatingSixUniversalCoverSylowFive_exact
  change Nat.card f.ker = 30
  rw [hrange, hnormalizer] at hcard
  omega

/-- The centralizer of the fixed Sylow `5`-subgroup in the canonical
cover has order thirty. -/
@[simp]
theorem natCard_centralizer_alternatingSixUniversalCoverSylowFive :
    Nat.card
        (Subgroup.centralizer
          (alternatingSixUniversalCoverSylow 5 :
            Set AlternatingSixUniversalCover)) =
      30 := by
  let P :=
    alternatingSixUniversalCoverSylow 5
  let N :=
    Subgroup.normalizer
      (P : Set AlternatingSixUniversalCover)
  let f :=
    (P : Subgroup AlternatingSixUniversalCover).normalizerMonoidHom
  have hker : Nat.card f.ker = 30 :=
    natCard_alternatingSixUniversalCoverSylowFive_normalizerMonoidHom_ker
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  calc
    Nat.card
        (Subgroup.centralizer
          (P : Set AlternatingSixUniversalCover)) =
        Nat.card
          ((Subgroup.centralizer
            (P : Set AlternatingSixUniversalCover)).subgroupOf N) :=
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.centralizer_le_normalizer
            (P : Set AlternatingSixUniversalCover))).toEquiv).symm
    _ = 30 := hker

/-- The centralizer of the fixed Sylow `5`-subgroup in the canonical
cover is commutative. -/
theorem centralizer_alternatingSixUniversalCoverSylowFive_isMulCommutative :
    IsMulCommutative
      (Subgroup.centralizer
        (alternatingSixUniversalCoverSylow 5 :
          Set AlternatingSixUniversalCover)) := by
  let E :=
    alternatingSixUniversalCentralExtension.toCentralExtension
  let S :=
    alternatingSixUniversalCoverTargetSylow 5
  letI :
      IsCyclic
        (Subgroup.centralizer (S : Set AlternatingSix)) :=
    isCyclic_of_prime_card
      (natCard_centralizer_sylowFive_alternatingSix S)
  have hcomm :
      IsMulCommutative
        (Subgroup.centralizer
          (E.sylowLift S : Set AlternatingSixUniversalCover)) :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (E.sylowCentralizerProjection S
        alternatingSixUniversalCoverSylowLiftProjectionFive_injective)
      (E.sylowCentralizerProjection_ker_le_center S
        alternatingSixUniversalCoverSylowLiftProjectionFive_injective)
  rw [← alternatingSixUniversalCoverSylowFive_eq_sylowLift]
    at hcomm
  exact hcomm

/-- The centralizer of the fixed Sylow `5`-subgroup is cyclic of order
thirty. -/
theorem centralizer_alternatingSixUniversalCoverSylowFive_isCyclic :
    IsCyclic
      (Subgroup.centralizer
        (alternatingSixUniversalCoverSylow 5 :
          Set AlternatingSixUniversalCover)) := by
  let C :=
    Subgroup.centralizer
      (alternatingSixUniversalCoverSylow 5 :
        Set AlternatingSixUniversalCover)
  letI : IsMulCommutative C :=
    centralizer_alternatingSixUniversalCoverSylowFive_isMulCommutative
  letI : CommGroup C := inferInstance
  letI : IsZGroup C :=
    IsZGroup.of_squarefree (by
      rw [natCard_centralizer_alternatingSixUniversalCoverSylowFive]
      have hsix : Squarefree 6 := by
        simpa using
          (Nat.squarefree_mul
            (m := 2) (n := 3) (by norm_num)).mpr
              ⟨Nat.prime_two.squarefree,
                Nat.prime_three.squarefree⟩
      simpa using
        (Nat.squarefree_mul
          (m := 6) (n := 5) (by norm_num)).mpr
            ⟨hsix, Nat.prime_five.squarefree⟩)
  infer_instance

/-- The cyclic Sylow centralizer has index two in the fixed Sylow
normalizer. -/
theorem relIndex_centralizer_alternatingSixUniversalCoverSylowFive_normalizer :
    (Subgroup.centralizer
        (alternatingSixUniversalCoverSylow 5 :
          Set AlternatingSixUniversalCover)).relIndex
      (Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 5 :
          Set AlternatingSixUniversalCover)) =
      2 := by
  let P :=
    alternatingSixUniversalCoverSylow 5
  let f :=
    (P : Subgroup AlternatingSixUniversalCover).normalizerMonoidHom
  change
    ((Subgroup.centralizer
      ((P : Subgroup AlternatingSixUniversalCover) :
        Set AlternatingSixUniversalCover)).subgroupOf
        (Subgroup.normalizer
          ((P : Subgroup AlternatingSixUniversalCover) :
            Set AlternatingSixUniversalCover))).index =
      2
  rw [← Subgroup.normalizerMonoidHom_ker,
    Subgroup.index_ker]
  exact
    natCard_alternatingSixUniversalCoverSylowFive_normalizerMonoidHom_range

/-- The center, viewed inside the fixed Sylow `5`-normalizer, still has
order six. -/
@[simp]
theorem natCard_center_subgroupOf_alternatingSixUniversalCoverSylowFiveNormalizer :
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 5 :
              Set AlternatingSixUniversalCover))) =
      6 := by
  calc
    Nat.card
        ((Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 5 :
              Set AlternatingSixUniversalCover))) =
        Nat.card (Subgroup.center AlternatingSixUniversalCover) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.center_le_normalizer
            (alternatingSixUniversalCoverSylow 5 :
              Set AlternatingSixUniversalCover))).toEquiv
    _ = 6 := natCard_center_alternatingSixUniversalCover

/-- The fixed Sylow `5`-normalizer is a proper subgroup of the canonical
cover. -/
theorem normalizer_alternatingSixUniversalCoverSylowFive_ne_top :
    Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 5 :
          Set AlternatingSixUniversalCover) ≠
      ⊤ := by
  intro htop
  have hcard :=
    natCard_normalizer_alternatingSixUniversalCoverSylowFive_exact
  rw [htop, Subgroup.card_top,
    natCard_alternatingSixUniversalCover_exact] at hcard
  omega

/-- Projection restricts to a central extension from the fixed cover
Sylow `5`-normalizer onto the corresponding normalizer in `A₆`. -/
def alternatingSixUniversalCoverSylowFiveNormalizerCentralExtension :
    CentralExtension
      (Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 5 :
          Set AlternatingSixUniversalCover))
      (Subgroup.normalizer
        (alternatingSixUniversalCoverTargetSylow 5 :
          Set AlternatingSix)) := by
  rw [alternatingSixUniversalCoverSylowFive_eq_sylowLift]
  exact
    alternatingSixUniversalCentralExtension.toCentralExtension
      |>.sylowNormalizerCentralExtension
        (alternatingSixUniversalCoverTargetSylow 5)

/-- The kernel of the restricted normalizer projection has order six. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowFiveNormalizerProjection_ker :
    Nat.card
        (CentralExtension.projection
          alternatingSixUniversalCoverSylowFiveNormalizerCentralExtension).ker =
      6 := by
  let C :=
    alternatingSixUniversalCoverSylowFiveNormalizerCentralExtension
  let f := C.projection
  have hrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr C.surjective
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 5 :
              Set AlternatingSixUniversalCover)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ =
          Nat.card
            (Subgroup.normalizer
              (alternatingSixUniversalCoverSylow 5 :
                Set AlternatingSixUniversalCover)) :=
        f.ker.card_mul_index
  have htarget :
      Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverTargetSylow 5 :
              Set AlternatingSix)) =
        10 :=
    natCard_normalizer_sylowFive_alternatingSix
      (alternatingSixUniversalCoverTargetSylow 5)
  have hsource :
      Nat.card
          (Subgroup.normalizer
            (alternatingSixUniversalCoverSylow 5 :
              Set AlternatingSixUniversalCover)) =
        60 :=
    natCard_normalizer_alternatingSixUniversalCoverSylowFive_exact
  rw [hrange, Subgroup.card_top, htarget, hsource] at hcard
  change Nat.card f.ker = 6
  omega

/-- Quotienting the cover normalizer by its central projection kernel
recovers the order-ten Sylow normalizer in `A₆`. -/
def alternatingSixUniversalCoverSylowFiveNormalizerQuotientEquiv :
    (Subgroup.normalizer
          (alternatingSixUniversalCoverSylow 5 :
            Set AlternatingSixUniversalCover)) ⧸
        (CentralExtension.projection
          alternatingSixUniversalCoverSylowFiveNormalizerCentralExtension).ker ≃*
      Subgroup.normalizer
        (alternatingSixUniversalCoverTargetSylow 5 :
          Set AlternatingSix) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (CentralExtension.projection
      alternatingSixUniversalCoverSylowFiveNormalizerCentralExtension)
    (CentralExtension.surjective
      alternatingSixUniversalCoverSylowFiveNormalizerCentralExtension)

/-- The fixed Sylow `5`-subgroup has relative index twelve in its
normalizer. -/
theorem relIndex_alternatingSixUniversalCoverSylowFive_normalizer :
    (alternatingSixUniversalCoverSylow 5 :
        Subgroup AlternatingSixUniversalCover).relIndex
      (Subgroup.normalizer
        (alternatingSixUniversalCoverSylow 5 :
          Set AlternatingSixUniversalCover)) =
      12 := by
  let P :=
    alternatingSixUniversalCoverSylow 5
  let N :=
    Subgroup.normalizer
      (P : Set AlternatingSixUniversalCover)
  change
    (P : Subgroup AlternatingSixUniversalCover).relIndex N = 12
  have hcardSubgroup :
      Nat.card
          ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N) =
        5 := by
    calc
      Nat.card
          ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N) =
          Nat.card P :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (P : Subgroup AlternatingSixUniversalCover).le_normalizer).toEquiv
      _ = 5 :=
        natCard_alternatingSixUniversalCoverSylowFive_exact
  have hcard :=
    ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N).card_mul_index
  change
    Nat.card
        ((P : Subgroup AlternatingSixUniversalCover).subgroupOf N) *
        (P : Subgroup AlternatingSixUniversalCover).relIndex N =
      Nat.card N at hcard
  have hcardNormalizer : Nat.card N = 60 := by
    exact natCard_normalizer_alternatingSixUniversalCoverSylowFive_exact
  rw [hcardSubgroup, hcardNormalizer] at hcard
  omega

end GroupTheory
end McKayConjecture
