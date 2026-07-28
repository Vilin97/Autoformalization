/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveConjugacyClassEquiv
import Mathlib.Algebra.Group.ConjFinite

/-!
# The Sylow-two normalizer in `SL(2, 𝔽₅)`

The normalizer of the explicit quaternion Sylow subgroup has order `24`.
This file equips that subtype with a computational `Fintype`, exhibits an
order-three complement, and constructs its quotient map to `C₃`.  Thus it
records the concrete binary-tetrahedral structure needed by the local
character table.

The last section counts the intersections of the normalizer with the nine
ambient conjugacy classes.  It packages those counts as a reusable formula
for sums of ambient class functions restricted to the normalizer.
-/

namespace McKayConjecture
namespace GroupTheory

open Matrix
open scoped MatrixGroups

local instance factPrimeTwoForSylowTwoNormalizer :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The exact normalizer of the chosen quaternion Sylow subgroup. -/
abbrev SpecialLinearTwoFiveSylowTwoNormalizer :=
  Subgroup.normalizer
    (specialLinearTwoFiveSylowTwo :
      Set SpecialLinearTwoFive)

/-- Identify the normalizer subtype with the executable normalizer table. -/
def specialLinearTwoFiveSylowTwoNormalizerEquivTableSubtype :
    SpecialLinearTwoFiveSylowTwoNormalizer ≃
      {g : SpecialLinearTwoFive //
        g ∈ finiteSetNormalizer
          specialLinearTwoFiveQuaternionElements} where
  toFun g := ⟨g, by
    change
      (g : SpecialLinearTwoFive) ∈
        (finiteSetNormalizer
          specialLinearTwoFiveQuaternionElements :
            Set SpecialLinearTwoFive)
    rw [← coe_finiteSetNormalizer
      (specialLinearTwoFiveSylowTwo :
        Subgroup SpecialLinearTwoFive)
      specialLinearTwoFiveQuaternionElements
      coe_specialLinearTwoFiveSylowTwo]
    exact g.property⟩
  invFun g := ⟨g, by
    change
      (g : SpecialLinearTwoFive) ∈
        (Subgroup.normalizer
          ((specialLinearTwoFiveSylowTwo :
            Subgroup SpecialLinearTwoFive) :
              Set SpecialLinearTwoFive) :
          Set SpecialLinearTwoFive)
    rw [coe_finiteSetNormalizer
      (specialLinearTwoFiveSylowTwo :
        Subgroup SpecialLinearTwoFive)
      specialLinearTwoFiveQuaternionElements
      coe_specialLinearTwoFiveSylowTwo]
    exact g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A computational finite enumeration of the exact normalizer. -/
instance specialLinearTwoFiveSylowTwoNormalizerFintype :
    Fintype SpecialLinearTwoFiveSylowTwoNormalizer :=
  Fintype.ofEquiv
    {g : SpecialLinearTwoFive //
      g ∈ finiteSetNormalizer
        specialLinearTwoFiveQuaternionElements}
    specialLinearTwoFiveSylowTwoNormalizerEquivTableSubtype.symm

/-- The matrix `[[1,1],[2,3]]`, which cyclically permutes the quaternion
directions (up to signs). -/
def specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix :
    SpecialLinearTwoFive :=
  ⟨!![(1 : ZMod 5), 1; 2, 3], by native_decide⟩

/-- The order-three complement element in the exact normalizer. -/
def specialLinearTwoFiveSylowTwoNormalizerOrderThree :
    SpecialLinearTwoFiveSylowTwoNormalizer :=
  ⟨specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix, by
    change
      specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix ∈
        (Subgroup.normalizer
          ((specialLinearTwoFiveSylowTwo :
            Subgroup SpecialLinearTwoFive) :
              Set SpecialLinearTwoFive) :
          Set SpecialLinearTwoFive)
    rw [coe_finiteSetNormalizer
      (specialLinearTwoFiveSylowTwo :
        Subgroup SpecialLinearTwoFive)
      specialLinearTwoFiveQuaternionElements
      coe_specialLinearTwoFiveSylowTwo]
    native_decide⟩

theorem orderOf_specialLinearTwoFiveSylowTwoNormalizerOrderThree :
    orderOf specialLinearTwoFiveSylowTwoNormalizerOrderThree = 3 :=
  orderOf_eq_prime (by native_decide) (by native_decide)

/-- The complement conjugates the three quaternion directions cyclically,
with the signs dictated by the chosen matrix coordinates. -/
theorem specialLinearTwoFiveSylowTwoNormalizerOrderThree_conjugation :
    specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix *
          specialLinearTwoFiveQuaternionI *
          specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix⁻¹ =
        -specialLinearTwoFiveQuaternionK ∧
      specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix *
          specialLinearTwoFiveQuaternionJ *
          specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix⁻¹ =
        specialLinearTwoFiveQuaternionI ∧
      specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix *
          specialLinearTwoFiveQuaternionK *
          specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix⁻¹ =
        -specialLinearTwoFiveQuaternionJ := by
  native_decide

/-- The `C₃` coordinate in the normal form `Q₈ ⋊ C₃`.  The three cases are
the quaternion subgroup and the two cosets represented by the chosen
order-three element. -/
def specialLinearTwoFiveSylowTwoNormalizerCyclicCoordinate
    (g : SpecialLinearTwoFiveSylowTwoNormalizer) :
    Multiplicative (ZMod 3) :=
  if (g : SpecialLinearTwoFive) ∈
      specialLinearTwoFiveQuaternionElements then
    Multiplicative.ofAdd 0
  else if
      ((specialLinearTwoFiveSylowTwoNormalizerOrderThree⁻¹ * g :
        SpecialLinearTwoFiveSylowTwoNormalizer) :
          SpecialLinearTwoFive) ∈
            specialLinearTwoFiveQuaternionElements then
    Multiplicative.ofAdd 1
  else
    Multiplicative.ofAdd 2

/-- The quotient homomorphism from the binary tetrahedral normalizer to its
cyclic abelianization `C₃`. -/
def specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient :
    SpecialLinearTwoFiveSylowTwoNormalizer →*
      Multiplicative (ZMod 3) where
  toFun :=
    specialLinearTwoFiveSylowTwoNormalizerCyclicCoordinate
  map_one' := by native_decide
  map_mul' := by native_decide

@[simp]
theorem specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient_orderThree :
    specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient
        specialLinearTwoFiveSylowTwoNormalizerOrderThree =
      Multiplicative.ofAdd (1 : ZMod 3) := by
  native_decide

theorem specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient_surjective :
    Function.Surjective
      specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient := by
  intro z
  obtain ⟨z, rfl⟩ := Multiplicative.toAdd.surjective z
  fin_cases z
  · exact ⟨1, by native_decide⟩
  · exact
      ⟨specialLinearTwoFiveSylowTwoNormalizerOrderThree,
        by native_decide⟩
  · exact
      ⟨specialLinearTwoFiveSylowTwoNormalizerOrderThree ^ 2,
        by native_decide⟩

/-! ## Ambient conjugacy classes inside the normalizer -/

/-- The intersection sizes with the nine ambient conjugacy classes. -/
def specialLinearTwoFiveSylowTwoNormalizerAmbientClassSize :
    SpecialLinearTwoFiveConjugacyClass → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 6
  | 3 => 8
  | 4 => 8
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0

theorem specialLinearTwoFiveSylowTwoNormalizer_card_ambientClass
    (c : SpecialLinearTwoFiveConjugacyClass) :
    (Finset.univ.filter fun
      g : SpecialLinearTwoFiveSylowTwoNormalizer =>
        specialLinearTwoFiveAreConjugate
          (g : SpecialLinearTwoFive)
          (specialLinearTwoFiveConjugacyRepresentative c) =
            true).card =
      specialLinearTwoFiveSylowTwoNormalizerAmbientClassSize c := by
  fin_cases c <;> native_decide

/-- Sum an ambient conjugacy-invariant function over the exact Sylow-two
normalizer using the five ambient classes which meet it. -/
theorem specialLinearTwoFiveSylowTwoNormalizer_sum_by_ambientClasses
    {R : Type*} [AddCommMonoid R]
    (f : SpecialLinearTwoFive → R)
    (hf :
      ∀ {g h : SpecialLinearTwoFive},
        IsConj g h → f g = f h) :
    (∑ g : SpecialLinearTwoFiveSylowTwoNormalizer,
        f (g : SpecialLinearTwoFive)) =
      ∑ c : SpecialLinearTwoFiveConjugacyClass,
        specialLinearTwoFiveSylowTwoNormalizerAmbientClassSize c •
          f (specialLinearTwoFiveConjugacyRepresentative c) := by
  have hpointwise
      (g : SpecialLinearTwoFiveSylowTwoNormalizer) :
      f (g : SpecialLinearTwoFive) =
        ∑ c : SpecialLinearTwoFiveConjugacyClass,
          if specialLinearTwoFiveAreConjugate
              (g : SpecialLinearTwoFive)
              (specialLinearTwoFiveConjugacyRepresentative c) =
                true then
            f (specialLinearTwoFiveConjugacyRepresentative c)
          else 0 := by
    obtain ⟨c, hc, hunique⟩ :=
      specialLinearTwoFive_existsUnique_conjugacyClass
        (g : SpecialLinearTwoFive)
    have hcBool :
        specialLinearTwoFiveAreConjugate
            (g : SpecialLinearTwoFive)
            (specialLinearTwoFiveConjugacyRepresentative c) =
          true :=
      (specialLinearTwoFiveAreConjugate_iff_isConj _ _).2 hc
    rw [Finset.sum_eq_single c]
    · rw [if_pos hcBool]
      exact hf hc
    · intro d _ hdc
      have hd :
          ¬IsConj (g : SpecialLinearTwoFive)
            (specialLinearTwoFiveConjugacyRepresentative d) := by
        intro hd
        exact hdc (hunique d hd)
      rw [if_neg]
      exact fun hdBool =>
        hd
          ((specialLinearTwoFiveAreConjugate_iff_isConj _ _).1
            hdBool)
    · simp
  calc
    (∑ g : SpecialLinearTwoFiveSylowTwoNormalizer,
        f (g : SpecialLinearTwoFive)) =
        ∑ g : SpecialLinearTwoFiveSylowTwoNormalizer,
          ∑ c : SpecialLinearTwoFiveConjugacyClass,
            if specialLinearTwoFiveAreConjugate
                (g : SpecialLinearTwoFive)
                (specialLinearTwoFiveConjugacyRepresentative c) =
                  true then
              f (specialLinearTwoFiveConjugacyRepresentative c)
            else 0 := by
          apply Finset.sum_congr rfl
          intro g _
          exact hpointwise g
    _ =
        ∑ c : SpecialLinearTwoFiveConjugacyClass,
          ∑ g : SpecialLinearTwoFiveSylowTwoNormalizer,
            if specialLinearTwoFiveAreConjugate
                (g : SpecialLinearTwoFive)
                (specialLinearTwoFiveConjugacyRepresentative c) =
                  true then
              f (specialLinearTwoFiveConjugacyRepresentative c)
            else 0 := by
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.sum_filter]
      rw [Finset.sum_const]
      rw [
        specialLinearTwoFiveSylowTwoNormalizer_card_ambientClass]

/-- The binary tetrahedral normalizer has seven conjugacy classes. -/
theorem natCard_conjClasses_specialLinearTwoFiveSylowTwoNormalizer :
    Nat.card
        (ConjClasses
          SpecialLinearTwoFiveSylowTwoNormalizer) =
      7 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

end GroupTheory
end McKayConjecture
