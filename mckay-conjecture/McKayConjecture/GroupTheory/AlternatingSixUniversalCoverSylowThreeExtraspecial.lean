/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverSylowThreeStructure
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverSylowTwoQuaternion
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverThreeLocalStructure
import McKayConjecture.GroupTheory.CommutatorEquiv

/-!
# Extraspecial Sylow-three subgroups of the universal cover of `A₆`

The explicit Heisenberg Sylow subgroup of the presented sixfold cover is
transported across the canonical equivalence of universal central
extensions.  Sylow conjugacy then transports it to every Sylow
`3`-subgroup of the canonical universal cover.

Consequently every such Sylow subgroup has order `27`, center and
commutator subgroup of order `3`, equal center and commutator subgroup, and
exponent `3`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixUniversalCoverExtraspecialFactPrimeThree :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ### An explicit Sylow subgroup in the canonical cover -/

/-- The image of the explicit Heisenberg subgroup under the canonical
equivalence from the presented cover to the canonical universal cover. -/
def alternatingSixUniversalCoverHeisenbergThreeSubgroup :
    Subgroup AlternatingSixUniversalCover :=
  alternatingSixSchurSylowThreeSubgroup.map
    alternatingSixSchurEquivUniversalCover.toMonoidHom

/-- Transport along the universal-cover equivalence identifies the
explicit Heisenberg subgroup with its image in the canonical cover. -/
def alternatingSixSchurSylowThreeEquivUniversalCoverHeisenberg :
    alternatingSixSchurSylowThreeSubgroup ≃*
      alternatingSixUniversalCoverHeisenbergThreeSubgroup :=
  alternatingSixSchurEquivUniversalCover.subgroupMap
    alternatingSixSchurSylowThreeSubgroup

/-- The transported Heisenberg subgroup has order twenty-seven. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverHeisenbergThreeSubgroup :
    Nat.card alternatingSixUniversalCoverHeisenbergThreeSubgroup =
      27 := by
  calc
    Nat.card alternatingSixUniversalCoverHeisenbergThreeSubgroup =
        Nat.card alternatingSixSchurSylowThreeSubgroup :=
      Nat.card_congr
        alternatingSixSchurSylowThreeEquivUniversalCoverHeisenberg.symm.toEquiv
    _ = 27 :=
      natCard_alternatingSixSchurSylowThreeSubgroup

/-- The transported Heisenberg subgroup, regarded as a Sylow
`3`-subgroup of the canonical universal cover. -/
def alternatingSixUniversalCoverHeisenbergSylowThree :
    Sylow 3 AlternatingSixUniversalCover :=
  Sylow.ofCard
    alternatingSixUniversalCoverHeisenbergThreeSubgroup (by
      rw [← Sylow.card_eq_multiplicity
          (alternatingSixUniversalCoverSylow 3),
        natCard_alternatingSixUniversalCoverHeisenbergThreeSubgroup,
        natCard_alternatingSixUniversalCoverSylowThree_exact])

@[simp]
theorem alternatingSixUniversalCoverHeisenbergSylowThree_coe :
    (alternatingSixUniversalCoverHeisenbergSylowThree :
        Subgroup AlternatingSixUniversalCover) =
      alternatingSixUniversalCoverHeisenbergThreeSubgroup :=
  rfl

/-! ### Transport to an arbitrary Sylow subgroup -/

/-- Every Sylow `3`-subgroup of the canonical universal cover is
canonically equivalent (up to the choice made by Sylow conjugacy) to the
explicit Heisenberg subgroup of the presented cover. -/
def alternatingSixUniversalCoverSylowThreeEquivSchurHeisenberg
    (P : Sylow 3 AlternatingSixUniversalCover) :
    P ≃* alternatingSixSchurSylowThreeSubgroup :=
  (Sylow.equiv P
      alternatingSixUniversalCoverHeisenbergSylowThree).trans
    alternatingSixSchurSylowThreeEquivUniversalCoverHeisenberg.symm

/-- Every Sylow `3`-subgroup in the canonical cover has order
twenty-seven. -/
@[simp]
theorem natCard_sylowThree_alternatingSixUniversalCover
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Nat.card P = 27 := by
  rw [Nat.card_congr
      (alternatingSixUniversalCoverSylowThreeEquivSchurHeisenberg P).toEquiv,
    natCard_alternatingSixSchurSylowThreeSubgroup]

/-- The intrinsic center of every Sylow `3`-subgroup has order three. -/
@[simp]
theorem natCard_center_sylowThree_alternatingSixUniversalCover
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Nat.card (Subgroup.center P) = 3 := by
  let e :=
    alternatingSixUniversalCoverSylowThreeEquivSchurHeisenberg P
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
    natCard_center_alternatingSixSchurSylowThreeSubgroup]

/-- The center of every Sylow `3`-subgroup is cyclic. -/
theorem center_sylowThree_alternatingSixUniversalCover_isCyclic
    (P : Sylow 3 AlternatingSixUniversalCover) :
    IsCyclic (Subgroup.center P) :=
  isCyclic_of_prime_card
    (natCard_center_sylowThree_alternatingSixUniversalCover P)

/-- Every Sylow `3`-subgroup is extraspecial: its commutator subgroup is
its center. -/
theorem commutator_sylowThree_alternatingSixUniversalCover_eq_center
    (P : Sylow 3 AlternatingSixUniversalCover) :
    _root_.commutator P = Subgroup.center P := by
  let e :=
    alternatingSixUniversalCoverSylowThreeEquivSchurHeisenberg P
  exact e.commutator_eq_center_iff.mpr
    alternatingSixSchurSylowThree_commutator_eq_center

/-- The commutator subgroup of every Sylow `3`-subgroup has order
three. -/
@[simp]
theorem natCard_commutator_sylowThree_alternatingSixUniversalCover
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Nat.card (_root_.commutator P) = 3 := by
  rw [commutator_sylowThree_alternatingSixUniversalCover_eq_center,
    natCard_center_sylowThree_alternatingSixUniversalCover]

/-- The commutator subgroup of every Sylow `3`-subgroup is cyclic. -/
theorem commutator_sylowThree_alternatingSixUniversalCover_isCyclic
    (P : Sylow 3 AlternatingSixUniversalCover) :
    IsCyclic (_root_.commutator P) :=
  isCyclic_of_prime_card
    (natCard_commutator_sylowThree_alternatingSixUniversalCover P)

/-- Every element of every Sylow `3`-subgroup has cube one. -/
theorem sylowThree_alternatingSixUniversalCover_cube
    (P : Sylow 3 AlternatingSixUniversalCover) (g : P) :
    g ^ 3 = 1 := by
  let e :=
    alternatingSixUniversalCoverSylowThreeEquivSchurHeisenberg P
  apply e.injective
  rw [map_pow,
    alternatingSixSchurSylowThreeSubgroup_cube,
    map_one]

/-- A compact statement of the exponent-three extraspecial structure of
every Sylow `3`-subgroup of the canonical universal cover. -/
theorem sylowThree_alternatingSixUniversalCover_is_extraspecial_exponent_three
    (P : Sylow 3 AlternatingSixUniversalCover) :
    Nat.card P = 27 ∧
      Nat.card (Subgroup.center P) = 3 ∧
      _root_.commutator P = Subgroup.center P ∧
      (∀ g : P, g ^ 3 = 1) :=
  ⟨natCard_sylowThree_alternatingSixUniversalCover P,
    natCard_center_sylowThree_alternatingSixUniversalCover P,
    commutator_sylowThree_alternatingSixUniversalCover_eq_center P,
    sylowThree_alternatingSixUniversalCover_cube P⟩

end GroupTheory
end McKayConjecture
