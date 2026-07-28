/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Perm.Cycle.Type
import McKayConjecture.GroupTheory.AlternatingSix

/-!
# Sylow structure in `A₆` and its canonical universal cover

This file records the part of the local structure of `A₆` that does not
require a Schur-multiplier computation or a character table.

For the target:

* a Sylow `2`-subgroup has order `8` and is not cyclic;
* a Sylow `3`-subgroup is abelian of order `9`, is not cyclic, and has
  exponent `3`;
* a Sylow `5`-subgroup is cyclic of order `5`.

For the canonical free-presentation universal cover, restriction of the
canonical projection to any fixed Sylow subgroup is surjective onto a Sylow
subgroup of `A₆`.  Its kernel is exactly the part of the center lying in that
Sylow subgroup.  In particular, the order of the cover Sylow subgroup is the
order of the target Sylow subgroup times the `p`-part of the center.

None of these results identifies the center with the Schur multiplier
`C₆`; that is the remaining group-theoretic input needed to replace the
cardinality formulas below by the familiar orders of Sylow subgroups in
`6.A₆`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

open Equiv

local instance alternatingSixFactPrimeThree :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance alternatingSixFactPrimeFive :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ### Target Sylow subgroups -/

/-- No permutation of six letters has order eight. -/
theorem perm_fin_six_orderOf_ne_eight
    (g : Equiv.Perm (Fin 6)) :
    orderOf g ≠ 8 := by
  intro hg
  have hparts :
      ∀ n ∈ g.cycleType, n ∣ 4 := by
    intro n hn
    have hnTwo : 2 ≤ n :=
      Equiv.Perm.two_le_of_mem_cycleType hn
    have hnSix : n ≤ 6 := by
      exact
        (Multiset.le_sum_of_mem hn).trans
          (by simpa using g.sum_cycleType_le)
    have hnDvd : n ∣ 8 := by
      rw [← hg, ← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hn
    interval_cases n
    · norm_num
    · norm_num at hnDvd
    · norm_num
    · norm_num at hnDvd
    · norm_num at hnDvd
  have hlcm : g.cycleType.lcm ∣ 4 :=
    Multiset.lcm_dvd.mpr hparts
  rw [Equiv.Perm.lcm_cycleType, hg] at hlcm
  norm_num at hlcm

/-- No element of `A₆` has order eight. -/
theorem alternatingSix_orderOf_ne_eight
    (g : AlternatingSix) :
    orderOf g ≠ 8 := by
  rw [← Subgroup.orderOf_coe g]
  exact perm_fin_six_orderOf_ne_eight g

/-- A Sylow `2`-subgroup of `A₆` is not cyclic. -/
theorem sylowTwo_alternatingSix_not_isCyclic
    (P : Sylow 2 AlternatingSix) :
    ¬IsCyclic P := by
  intro hcyclic
  obtain ⟨g, hg⟩ :=
    (isCyclic_iff_exists_orderOf_eq_natCard (α := P)).mp hcyclic
  rw [natCard_sylowTwo_alternatingSix] at hg
  exact
    alternatingSix_orderOf_ne_eight g
      ((Subgroup.orderOf_coe g).trans hg)

/-- No permutation of six letters has order nine. -/
theorem perm_fin_six_orderOf_ne_nine
    (g : Equiv.Perm (Fin 6)) :
    orderOf g ≠ 9 := by
  intro hg
  have hparts :
      ∀ n ∈ g.cycleType, n = 3 := by
    intro n hn
    have hnTwo : 2 ≤ n :=
      Equiv.Perm.two_le_of_mem_cycleType hn
    have hnSix : n ≤ 6 := by
      exact
        (Multiset.le_sum_of_mem hn).trans
          (by simpa using g.sum_cycleType_le)
    have hnDvd : n ∣ 9 := by
      rw [← hg, ← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hn
    interval_cases n
    · norm_num at hnDvd
    · rfl
    · norm_num at hnDvd
    · norm_num at hnDvd
    · norm_num at hnDvd
  have hcard : 0 < g.cycleType.card := by
    rw [Multiset.card_pos]
    intro hzero
    have hOne : g = 1 :=
      Equiv.Perm.cycleType_eq_zero.mp hzero
    subst g
    norm_num at hg
  have hlcm : g.cycleType.lcm = 3 := by
    apply Nat.dvd_antisymm
    · exact
        Multiset.lcm_dvd.mpr fun n hn => by
          rw [hparts n hn]
    · obtain ⟨n, hn⟩ :=
        Multiset.card_pos_iff_exists_mem.mp hcard
      rw [← hparts n hn]
      exact Multiset.dvd_lcm hn
  rw [← Equiv.Perm.lcm_cycleType, hlcm] at hg
  norm_num at hg

/-- No element of `A₆` has order nine. -/
theorem alternatingSix_orderOf_ne_nine
    (g : AlternatingSix) :
    orderOf g ≠ 9 := by
  rw [← Subgroup.orderOf_coe g]
  exact perm_fin_six_orderOf_ne_nine g

/-- A Sylow `3`-subgroup of `A₆` is abelian. -/
theorem sylowThree_alternatingSix_isMulCommutative
    (P : Sylow 3 AlternatingSix) :
    IsMulCommutative P := by
  apply IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 3)
  norm_num [natCard_sylowThree_alternatingSix P]

/-- A Sylow `3`-subgroup of `A₆` is not cyclic. -/
theorem sylowThree_alternatingSix_not_isCyclic
    (P : Sylow 3 AlternatingSix) :
    ¬IsCyclic P := by
  intro hcyclic
  obtain ⟨g, hg⟩ :=
    (isCyclic_iff_exists_orderOf_eq_natCard (α := P)).mp hcyclic
  rw [natCard_sylowThree_alternatingSix] at hg
  exact
    alternatingSix_orderOf_ne_nine g
      ((Subgroup.orderOf_coe g).trans hg)

/-- A Sylow `3`-subgroup of `A₆` has exponent three. -/
theorem exponent_sylowThree_alternatingSix
    (P : Sylow 3 AlternatingSix) :
    Monoid.exponent P = 3 := by
  rw [← not_isCyclic_iff_exponent_eq_prime
    Nat.prime_three
    (by norm_num [natCard_sylowThree_alternatingSix P])]
  exact sylowThree_alternatingSix_not_isCyclic P

/-- A Sylow `5`-subgroup of `A₆` is cyclic. -/
theorem sylowFive_alternatingSix_isCyclic
    (P : Sylow 5 AlternatingSix) :
    IsCyclic P := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact
    isCyclic_of_prime_card
      (natCard_sylowFive_alternatingSix P)

/-- A Sylow `5`-subgroup of `A₆` has exponent five. -/
theorem exponent_sylowFive_alternatingSix
    (P : Sylow 5 AlternatingSix) :
    Monoid.exponent P = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : IsCyclic P :=
    sylowFive_alternatingSix_isCyclic P
  rw [IsCyclic.exponent_eq_card,
    natCard_sylowFive_alternatingSix]

/-! ### The Sylow projection from the canonical universal cover -/

/-- The image in `A₆` of the fixed Sylow subgroup of the canonical
universal cover. -/
def alternatingSixUniversalCoverTargetSylow
    (p : ℕ) [Fact p.Prime] :
    Sylow p AlternatingSix :=
  (alternatingSixUniversalCoverSylow p).mapSurjective
    alternatingSixUniversalCentralExtension.toCentralExtension.surjective

/-- Restriction of the canonical universal-cover projection to the fixed
Sylow subgroup. -/
def alternatingSixUniversalCoverSylowProjection
    (p : ℕ) [Fact p.Prime] :
    alternatingSixUniversalCoverSylow p →*
      alternatingSixUniversalCoverTargetSylow p :=
  alternatingSixUniversalCentralExtension.toCentralExtension.projection.subgroupMap
    (alternatingSixUniversalCoverSylow p)

/-- The restricted projection is surjective. -/
theorem alternatingSixUniversalCoverSylowProjection_surjective
    (p : ℕ) [Fact p.Prime] :
    Function.Surjective
      (alternatingSixUniversalCoverSylowProjection p) :=
  MonoidHom.subgroupMap_surjective _ _

/-- The kernel of the restricted projection is precisely the subgroup of
the fixed Sylow subgroup consisting of central elements. -/
theorem alternatingSixUniversalCoverSylowProjection_ker
    (p : ℕ) [Fact p.Prime] :
    (alternatingSixUniversalCoverSylowProjection p).ker =
      (Subgroup.center AlternatingSixUniversalCover).subgroupOf
        (alternatingSixUniversalCoverSylow p) := by
  change
    (alternatingSixUniversalCentralExtension.toCentralExtension.projection.subgroupMap
      (alternatingSixUniversalCoverSylow p)).ker =
        (Subgroup.center AlternatingSixUniversalCover).subgroupOf
          (alternatingSixUniversalCoverSylow p)
  rw [
    Subgroup.ker_subgroupMap,
    alternatingSixUniversalCentralExtension_ker_eq_center]

/-- The cardinality of the canonical universal cover is `360` times the
cardinality of its center. -/
theorem natCard_alternatingSixUniversalCover :
    Nat.card AlternatingSixUniversalCover =
      360 * Nat.card (Subgroup.center AlternatingSixUniversalCover) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr
      alternatingSixUniversalCoverQuotientCenterEquiv.toEquiv,
    natCard_alternatingSix]

/-- At every prime, the order of the fixed cover Sylow subgroup is the
order of its target image times the `p`-part of the center. -/
theorem natCard_alternatingSixUniversalCoverSylow
    (p : ℕ) [Fact p.Prime] :
    Nat.card (alternatingSixUniversalCoverSylow p) =
      Nat.card (alternatingSixUniversalCoverTargetSylow p) *
        p ^ Nat.factorization
          (Nat.card (Subgroup.center AlternatingSixUniversalCover)) p := by
  rw [Sylow.card_eq_multiplicity,
    Sylow.card_eq_multiplicity,
    natCard_alternatingSixUniversalCover,
    natCard_alternatingSix,
    Nat.factorization_mul
      (by norm_num : 360 ≠ 0)
      (Nat.card_pos.ne' :
        Nat.card (Subgroup.center AlternatingSixUniversalCover) ≠ 0),
    Finsupp.add_apply, pow_add]

/-- The central kernel of the restricted Sylow projection has exactly the
`p`-part of the center as its order. -/
theorem natCard_alternatingSixUniversalCoverSylowProjection_ker
    (p : ℕ) [Fact p.Prime] :
    Nat.card (alternatingSixUniversalCoverSylowProjection p).ker =
      p ^ Nat.factorization
        (Nat.card (Subgroup.center AlternatingSixUniversalCover)) p := by
  have hprojection :
      Nat.card (alternatingSixUniversalCoverSylowProjection p).ker *
          Nat.card (alternatingSixUniversalCoverTargetSylow p) =
        Nat.card (alternatingSixUniversalCoverSylow p) := by
    rw [←
      (alternatingSixUniversalCoverSylowProjection p).ker.card_mul_index,
      Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr
        (alternatingSixUniversalCoverSylowProjection_surjective p),
      Subgroup.card_top]
  have hdecomposition :=
    natCard_alternatingSixUniversalCoverSylow p
  apply Nat.mul_right_cancel
    (Nat.card_pos
      (α := alternatingSixUniversalCoverTargetSylow p))
  calc
    Nat.card (alternatingSixUniversalCoverSylowProjection p).ker *
        Nat.card (alternatingSixUniversalCoverTargetSylow p) =
      Nat.card (alternatingSixUniversalCoverSylow p) :=
        hprojection
    _ =
      Nat.card (alternatingSixUniversalCoverTargetSylow p) *
        p ^ Nat.factorization
          (Nat.card (Subgroup.center AlternatingSixUniversalCover)) p :=
        hdecomposition
    _ =
      p ^ Nat.factorization
          (Nat.card (Subgroup.center AlternatingSixUniversalCover)) p *
        Nat.card (alternatingSixUniversalCoverTargetSylow p) := by
          rw [mul_comm]

/-- The kernel of the fixed Sylow projection consists of central elements
of that Sylow subgroup. -/
theorem alternatingSixUniversalCoverSylowProjection_ker_le_center
    (p : ℕ) [Fact p.Prime] :
    (alternatingSixUniversalCoverSylowProjection p).ker ≤
      Subgroup.center (alternatingSixUniversalCoverSylow p) := by
  intro z hz
  rw [alternatingSixUniversalCoverSylowProjection_ker] at hz
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp hz x

/-- The fixed cover Sylow `5`-subgroup is abelian.  This does not require
knowing the order of the center: it is a central extension of the cyclic
target Sylow `5`-subgroup. -/
theorem alternatingSixUniversalCoverSylowFive_isMulCommutative :
    IsMulCommutative (alternatingSixUniversalCoverSylow 5) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI :
      IsCyclic (alternatingSixUniversalCoverTargetSylow 5) :=
    sylowFive_alternatingSix_isCyclic _
  exact
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (alternatingSixUniversalCoverSylowProjection 5)
      (alternatingSixUniversalCoverSylowProjection_ker_le_center 5)

/-- The fixed cover Sylow `2`-subgroup has order eight times the `2`-part
of the center. -/
theorem natCard_alternatingSixUniversalCoverSylowTwo :
    Nat.card (alternatingSixUniversalCoverSylow 2) =
      8 * 2 ^ Nat.factorization
        (Nat.card (Subgroup.center AlternatingSixUniversalCover)) 2 := by
  rw [natCard_alternatingSixUniversalCoverSylow,
    natCard_sylowTwo_alternatingSix]

/-- The fixed cover Sylow `3`-subgroup has order nine times the `3`-part
of the center. -/
theorem natCard_alternatingSixUniversalCoverSylowThree :
    Nat.card (alternatingSixUniversalCoverSylow 3) =
      9 * 3 ^ Nat.factorization
        (Nat.card (Subgroup.center AlternatingSixUniversalCover)) 3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [natCard_alternatingSixUniversalCoverSylow,
    natCard_sylowThree_alternatingSix]

/-- The fixed cover Sylow `5`-subgroup has order five times the `5`-part
of the center. -/
theorem natCard_alternatingSixUniversalCoverSylowFive :
    Nat.card (alternatingSixUniversalCoverSylow 5) =
      5 * 5 ^ Nat.factorization
        (Nat.card (Subgroup.center AlternatingSixUniversalCover)) 5 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [natCard_alternatingSixUniversalCoverSylow,
    natCard_sylowFive_alternatingSix]

/-! ### Specialization to the classical Schur-multiplier order -/

/-- If the center of the canonical cover has the classical order six, its
Sylow `2`-subgroup has order sixteen. -/
theorem natCard_alternatingSixUniversalCoverSylowTwo_of_center_eq_six
    (hcenter :
      Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6) :
    Nat.card (alternatingSixUniversalCoverSylow 2) = 16 := by
  rw [natCard_alternatingSixUniversalCoverSylowTwo, hcenter]
  rw [show 6 = 2 * 3 by norm_num,
    Nat.factorization_mul_apply_of_coprime (by decide),
    Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

/-- If the center of the canonical cover has order six, its Sylow
`3`-subgroup has order twenty-seven. -/
theorem natCard_alternatingSixUniversalCoverSylowThree_of_center_eq_six
    (hcenter :
      Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6) :
    Nat.card (alternatingSixUniversalCoverSylow 3) = 27 := by
  rw [natCard_alternatingSixUniversalCoverSylowThree, hcenter]
  rw [show 6 = 2 * 3 by norm_num,
    Nat.factorization_mul_apply_of_coprime (by decide),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num),
    Nat.prime_three.factorization_self]
  norm_num

/-- If the center of the canonical cover has order six, its Sylow
`5`-subgroup has order five. -/
theorem natCard_alternatingSixUniversalCoverSylowFive_of_center_eq_six
    (hcenter :
      Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6) :
    Nat.card (alternatingSixUniversalCoverSylow 5) = 5 := by
  rw [natCard_alternatingSixUniversalCoverSylowFive, hcenter]
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

/-- Under the order-six center calculation, the restricted Sylow
`5`-projection has trivial kernel. -/
theorem alternatingSixUniversalCoverSylowFiveProjection_ker_eq_bot_of_center_eq_six
    (hcenter :
      Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6) :
    (alternatingSixUniversalCoverSylowProjection 5).ker = ⊥ := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply Subgroup.eq_bot_of_card_eq
  rw [natCard_alternatingSixUniversalCoverSylowProjection_ker,
    hcenter]
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

/-- Under the order-six center calculation, the cover Sylow
`5`-subgroup is canonically isomorphic to its target image. -/
def alternatingSixUniversalCoverSylowFiveEquivTarget_of_center_eq_six
    (hcenter :
      Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6) :
    alternatingSixUniversalCoverSylow 5 ≃*
      alternatingSixUniversalCoverTargetSylow 5 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact
    MulEquiv.ofBijective
      (alternatingSixUniversalCoverSylowProjection 5)
      ⟨(MonoidHom.ker_eq_bot_iff
          (alternatingSixUniversalCoverSylowProjection 5)).mp
          (alternatingSixUniversalCoverSylowFiveProjection_ker_eq_bot_of_center_eq_six
            hcenter),
        alternatingSixUniversalCoverSylowProjection_surjective 5⟩

/-- Under the order-six center calculation, the fixed cover Sylow
`5`-subgroup is cyclic. -/
theorem alternatingSixUniversalCoverSylowFive_isCyclic_of_center_eq_six
    (hcenter :
      Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6) :
    IsCyclic (alternatingSixUniversalCoverSylow 5) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact
    isCyclic_of_prime_card
      (natCard_alternatingSixUniversalCoverSylowFive_of_center_eq_six
        hcenter)

end GroupTheory
end McKayConjecture
