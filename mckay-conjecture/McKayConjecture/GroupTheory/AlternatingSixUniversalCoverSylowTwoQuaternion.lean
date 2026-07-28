/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurTwoLocalModel
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverTwoLocalStructure

/-!
# The generalized-quaternion Sylow subgroup of `6.A₆`

The explicit faithful `QuaternionGroup 4` map into the presented Schur
cover transports across uniqueness of universal central extensions.  Its
order-sixteen range is a Sylow `2`-subgroup of the canonical universal
cover.  Sylow conjugacy then identifies the fixed canonical Sylow subgroup
with the generalized quaternion group of order sixteen.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixUniversalCoverQuaternionFactPrimeTwo :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The center of the generalized quaternion group of order sixteen has
order two. -/
@[simp]
theorem natCard_center_quaternionGroup_four :
    Nat.card (Subgroup.center (QuaternionGroup 4)) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The canonical equivalence from the presented Schur cover to the fixed
free-presentation universal cover. -/
def alternatingSixSchurEquivUniversalCover :
    AlternatingSixSchurPresentedGroup ≃*
      AlternatingSixUniversalCover :=
  alternatingSixSchurUniversalCentralExtension.sourceEquiv
    alternatingSixUniversalCentralExtension

/-- Transport the explicit generalized-quaternion map to the canonical
universal cover. -/
def quaternionFourToAlternatingSixUniversalCover :
    QuaternionGroup 4 →*
      AlternatingSixUniversalCover :=
  alternatingSixSchurEquivUniversalCover.toMonoidHom.comp
    quaternionFourToAlternatingSixSchur

/-- The transported generalized-quaternion map remains faithful. -/
theorem quaternionFourToAlternatingSixUniversalCover_injective :
    Function.Injective
      quaternionFourToAlternatingSixUniversalCover :=
  alternatingSixSchurEquivUniversalCover.injective.comp
    quaternionFourToAlternatingSixSchur_injective

/-- The transported generalized-quaternion range has order sixteen. -/
@[simp]
theorem natCard_quaternionFourToAlternatingSixUniversalCover_range :
    Nat.card quaternionFourToAlternatingSixUniversalCover.range = 16 := by
  calc
    Nat.card quaternionFourToAlternatingSixUniversalCover.range =
        Nat.card (QuaternionGroup 4) :=
      (Nat.card_congr
        (MonoidHom.ofInjective
          quaternionFourToAlternatingSixUniversalCover_injective).toEquiv).symm
    _ = 16 := by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- The explicit generalized-quaternion range as a Sylow `2`-subgroup of
the canonical universal cover. -/
def alternatingSixUniversalCoverQuaternionSylowTwo :
    Sylow 2 AlternatingSixUniversalCover :=
  Sylow.ofCard
    quaternionFourToAlternatingSixUniversalCover.range (by
      rw [← Sylow.card_eq_multiplicity
        (alternatingSixUniversalCoverSylow 2),
        natCard_quaternionFourToAlternatingSixUniversalCover_range,
        natCard_alternatingSixUniversalCoverSylowTwo_exact])

@[simp]
theorem alternatingSixUniversalCoverQuaternionSylowTwo_coe :
    (alternatingSixUniversalCoverQuaternionSylowTwo :
      Subgroup AlternatingSixUniversalCover) =
        quaternionFourToAlternatingSixUniversalCover.range :=
  rfl

/-- The explicit generalized-quaternion range is canonically equivalent
to `QuaternionGroup 4`. -/
def quaternionFourEquivAlternatingSixUniversalCoverQuaternionSylowTwo :
    QuaternionGroup 4 ≃*
      alternatingSixUniversalCoverQuaternionSylowTwo := by
  change
    QuaternionGroup 4 ≃*
      quaternionFourToAlternatingSixUniversalCover.range
  exact
    MonoidHom.ofInjective
      quaternionFourToAlternatingSixUniversalCover_injective

/-- Every Sylow `2`-subgroup of the canonical universal cover is
generalized quaternion of order sixteen. -/
def alternatingSixUniversalCoverSylowTwoEquivQuaternionFour
    (P : Sylow 2 AlternatingSixUniversalCover) :
    P ≃* QuaternionGroup 4 :=
  (Sylow.equiv P
      alternatingSixUniversalCoverQuaternionSylowTwo).trans
    quaternionFourEquivAlternatingSixUniversalCoverQuaternionSylowTwo.symm

/-- The intrinsic center of every Sylow `2`-subgroup in the canonical
universal cover has order two. -/
@[simp]
theorem natCard_center_sylowTwo_alternatingSixUniversalCover
    (P : Sylow 2 AlternatingSixUniversalCover) :
    Nat.card (Subgroup.center P) = 2 := by
  rw [Nat.card_congr
      (Subgroup.centerCongr
        (alternatingSixUniversalCoverSylowTwoEquivQuaternionFour P)).toEquiv,
    natCard_center_quaternionGroup_four]

end GroupTheory
end McKayConjecture
