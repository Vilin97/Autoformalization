/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import McKayConjecture.GroupTheory.FiniteUniversalCentralExtension

/-!
# The first unresolved alternating simple group

This file fixes `A₆` as a concrete mathlib group and records the structural
facts needed before any character-table computation:

* `|A₆| = 360`;
* `A₆` is nonabelian, simple, centerless, and perfect;
* the only primes dividing its order are `2`, `3`, and `5`; and
* the free-presentation construction gives a fixed finite universal central
  extension of `A₆`.

The last construction is deliberately canonical.  It does not identify the
source with the classical group `6.A₆`; doing so requires the Schur-multiplier
calculation, which is not currently available in mathlib.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace GroupTheory

/-- The concrete six-point alternating group. -/
abbrev AlternatingSix :=
  alternatingGroup (Fin 6)

/-- The exact order of `A₆`. -/
@[simp]
theorem natCard_alternatingSix :
    Nat.card AlternatingSix = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

/-- `A₆` is simple. -/
instance alternatingSixIsSimpleGroup :
    IsSimpleGroup AlternatingSix :=
  alternatingGroup.isSimpleGroup (by simp)

/-- `A₆` is noncommutative. -/
theorem alternatingSix_not_isMulCommutative :
    ¬IsMulCommutative AlternatingSix := by
  intro h
  have :
      Nat.card (Fin 6) ≤ 3 :=
    alternatingGroup.isMulCommutative_iff_card_le_three.mp h
  simp at this

/-- `A₆` is centerless. -/
@[simp]
theorem alternatingSix_center_eq_bot :
    Subgroup.center AlternatingSix = ⊥ :=
  center_eq_bot_of_isSimpleGroup
    (inferInstance : IsSimpleGroup AlternatingSix)
    alternatingSix_not_isMulCommutative

/-- `A₆` is perfect. -/
instance alternatingSixIsPerfect :
    Group.IsPerfect AlternatingSix :=
  isPerfect_of_isSimpleGroup
    (inferInstance : IsSimpleGroup AlternatingSix)
    alternatingSix_not_isMulCommutative

/-- A prime divides `|A₆|` exactly when it is `2`, `3`, or `5`. -/
theorem prime_dvd_natCard_alternatingSix_iff
    {p : ℕ} [Fact p.Prime] :
    p ∣ Nat.card AlternatingSix ↔
      p = 2 ∨ p = 3 ∨ p = 5 := by
  rw [natCard_alternatingSix]
  constructor
  · intro hp
    have hp' : p ∣ 2 ^ 3 * 3 ^ 2 * 5 := by
      norm_num at hp ⊢
      exact hp
    rcases (Fact.out : p.Prime).dvd_mul.mp hp' with hp23 | hp5
    · rcases (Fact.out : p.Prime).dvd_mul.mp hp23 with hp2 | hp3
      · left
        exact (Nat.dvd_prime Nat.prime_two).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow hp2) |>.resolve_left
            (Fact.out : p.Prime).ne_one
      · right
        left
        exact Nat.dvd_prime Nat.prime_three |>.mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow hp3) |>.resolve_left
            (Fact.out : p.Prime).ne_one
    · right
      right
      exact Nat.dvd_prime Nat.prime_five |>.mp hp5
        |>.resolve_left (Fact.out : p.Prime).ne_one
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- The prime factorization of `|A₆|`. -/
theorem factorization_natCard_alternatingSix :
    Nat.factorization (Nat.card AlternatingSix) =
      Finsupp.single 2 3 +
        Finsupp.single 3 2 +
          Finsupp.single 5 1 := by
  rw [natCard_alternatingSix]
  conv_lhs =>
    rw [show 360 = 2 ^ 3 * 3 ^ 2 * 5 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.prime_two.factorization_pow]
  rw [Nat.prime_three.factorization_pow]
  rw [Nat.prime_five.factorization]

/-- Every Sylow `2`-subgroup of `A₆` has order `8`. -/
@[simp]
theorem natCard_sylowTwo_alternatingSix
    (P : Sylow 2 AlternatingSix) :
    Nat.card P = 8 := by
  rw [Sylow.card_eq_multiplicity, natCard_alternatingSix]
  have :
      Nat.factorization 360 2 = 3 := by
    have h :=
      DFunLike.congr_fun
        factorization_natCard_alternatingSix 2
    rw [natCard_alternatingSix] at h
    norm_num [Finsupp.add_apply, Finsupp.single_apply] at h
    exact h
  rw [this]
  norm_num

/-- Every Sylow `3`-subgroup of `A₆` has order `9`. -/
@[simp]
theorem natCard_sylowThree_alternatingSix
    (P : Sylow 3 AlternatingSix) :
    Nat.card P = 9 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, natCard_alternatingSix]
  have :
      Nat.factorization 360 3 = 2 := by
    have h :=
      DFunLike.congr_fun
        factorization_natCard_alternatingSix 3
    rw [natCard_alternatingSix] at h
    norm_num [Finsupp.add_apply, Finsupp.single_apply] at h
    exact h
  rw [this]
  norm_num

/-- Every Sylow `5`-subgroup of `A₆` has order `5`. -/
@[simp]
theorem natCard_sylowFive_alternatingSix
    (P : Sylow 5 AlternatingSix) :
    Nat.card P = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Sylow.card_eq_multiplicity, natCard_alternatingSix]
  have :
      Nat.factorization 360 5 = 1 := by
    have h :=
      DFunLike.congr_fun
        factorization_natCard_alternatingSix 5
    rw [natCard_alternatingSix] at h
    norm_num [Finsupp.add_apply, Finsupp.single_apply] at h
    exact h
  rw [this]
  norm_num

/-- The fixed free-presentation model of the universal cover of `A₆`. -/
abbrev AlternatingSixUniversalCover :=
  FreePresentation.Cover AlternatingSix

/-- The canonical universal central extension of `A₆`, obtained from its
perfectness. -/
def alternatingSixUniversalCentralExtension :
    UniversalCentralExtension
      AlternatingSixUniversalCover AlternatingSix :=
  FreePresentation.universalCentralExtension
    (inferInstance : Group.IsPerfect AlternatingSix)

/-- The fixed universal cover is perfect. -/
instance alternatingSixUniversalCoverIsPerfect :
    Group.IsPerfect AlternatingSixUniversalCover :=
  alternatingSixUniversalCentralExtension.sourcePerfect

/-- The canonical free-presentation universal cover of `A₆` is finite. -/
instance alternatingSixUniversalCoverFinite :
    Finite AlternatingSixUniversalCover :=
  alternatingSixUniversalCentralExtension.toCentralExtension.finite_source
    alternatingSixUniversalCentralExtension.sourcePerfect

/-- The kernel of the fixed projection is exactly the center of the
canonical cover. -/
@[simp]
theorem alternatingSixUniversalCentralExtension_ker_eq_center :
    alternatingSixUniversalCentralExtension.toCentralExtension.projection.ker =
      Subgroup.center AlternatingSixUniversalCover :=
  alternatingSixUniversalCentralExtension.toCentralExtension.ker_eq_center
    (inferInstance : IsSimpleGroup AlternatingSix)
    alternatingSix_not_isMulCommutative

/-- The central quotient of the fixed cover is canonically `A₆`. -/
def alternatingSixUniversalCoverQuotientCenterEquiv :
    (AlternatingSixUniversalCover ⧸
      Subgroup.center AlternatingSixUniversalCover) ≃*
        AlternatingSix :=
  alternatingSixUniversalCentralExtension.toCentralExtension.quotientCenterEquiv
    (inferInstance : IsSimpleGroup AlternatingSix)
    alternatingSix_not_isMulCommutative

/-- The fixed universal cover of `A₆` is quasisimple. -/
theorem alternatingSixUniversalCover_isQuasisimple :
    IsQuasisimple AlternatingSixUniversalCover :=
  alternatingSixUniversalCentralExtension.source_isQuasisimple
    (inferInstance : IsSimpleGroup AlternatingSix)
    alternatingSix_not_isMulCommutative

/-- A fixed Sylow subgroup of the canonical universal cover. -/
def alternatingSixUniversalCoverSylow
    (p : ℕ) :
    Sylow p AlternatingSixUniversalCover :=
  default

end GroupTheory
end McKayConjecture
