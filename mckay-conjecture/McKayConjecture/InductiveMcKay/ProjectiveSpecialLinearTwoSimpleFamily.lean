/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import McKayConjecture.InductiveMcKay.UniversalCoverFamilyReduction

/-!
# The simple two-dimensional projective-special-linear groups

This file packages the concrete groups

`PSL(2, GaloisField p n)`

with `p` prime, `n > 0`, and `4 ≤ p^n` as an isomorphism-invariant
`FiniteGroupFamily`.  The last inequality is exactly the small-field
exclusion used by mathlib's `PSL₂` simplicity theorem: it omits the fields
of orders two and three.

No classification coverage or inductive-McKay verification is asserted.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Parameters for a simple two-dimensional projective special linear group over a
canonical finite field.  The condition `4 ≤ p^n` is the exact hypothesis
consumed by `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple`. -/
structure ProjectiveSpecialLinearTwoSimpleParameter where
  characteristic : ℕ
  degree : ℕ
  characteristic_prime : characteristic.Prime
  degree_ne_zero : degree ≠ 0
  four_le_card : 4 ≤ characteristic ^ degree

/-- The canonical representative `PSL(2, 𝔽_{p^n})` attached to a valid
simple-family parameter. -/
abbrev projectiveSpecialLinearTwoRepresentative
    (a : ProjectiveSpecialLinearTwoSimpleParameter) : Type :=
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  Matrix.ProjectiveSpecialLinearGroup
    (Fin 2) (GaloisField a.characteristic a.degree)

/-- A field with at least four elements contains a nonzero element whose
square is not one.  This is the commutator hypothesis in the `PSL₂`
simplicity proof. -/
theorem exists_ne_zero_sq_ne_one_of_four_le_natCard
    {F : Type} [Field F]
    (hF : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  have : Finite F :=
    (Nat.card_pos_iff.1 (by omega)).2
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by
    infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F,
    ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two
      (Units.ext <| by simpa using h)] at hF
  omega

/-- The canonical finite field in a valid parameter has the advertised
prime-power cardinality. -/
theorem natCard_galoisField_projectiveSpecialLinearTwoParameter
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    letI : Fact a.characteristic.Prime :=
      ⟨a.characteristic_prime⟩
    Nat.card (GaloisField a.characteristic a.degree) =
      a.characteristic ^ a.degree := by
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  exact
    GaloisField.card
      a.characteristic a.degree a.degree_ne_zero

/-- Every canonical `PSL₂` representative is finite. -/
theorem projectiveSpecialLinearTwoRepresentative_finite
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Finite (projectiveSpecialLinearTwoRepresentative a) := by
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  change
    Finite
      (Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) (GaloisField a.characteristic a.degree))
  infer_instance

/-- Every canonical `PSL₂` representative is simple. -/
theorem projectiveSpecialLinearTwoRepresentative_isSimpleGroup
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    IsSimpleGroup
      (projectiveSpecialLinearTwoRepresentative a) := by
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  change
    IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) (GaloisField a.characteristic a.degree))
  apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
  rw [GaloisField.card
    a.characteristic a.degree a.degree_ne_zero]
  exact a.four_le_card

/-- Every canonical `PSL₂` representative is perfect. -/
theorem projectiveSpecialLinearTwoRepresentative_isPerfect
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Group.IsPerfect
      (projectiveSpecialLinearTwoRepresentative a) := by
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  let F := GaloisField a.characteristic a.degree
  have hcard : 4 ≤ Nat.card F := by
    dsimp only [F]
    rw [GaloisField.card
      a.characteristic a.degree a.degree_ne_zero]
    exact a.four_le_card
  have hfield :
      ∃ x : F, x ≠ 0 ∧ x ^ 2 ≠ 1 :=
    exists_ne_zero_sq_ne_one_of_four_le_natCard hcard
  exact
    ⟨SL2Simple.PSL_commutator_eq_top hfield⟩

/-- Every canonical `PSL₂` representative is noncommutative. -/
theorem projectiveSpecialLinearTwoRepresentative_not_isMulCommutative
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    ¬IsMulCommutative
      (projectiveSpecialLinearTwoRepresentative a) := by
  letI : Group.IsPerfect
      (projectiveSpecialLinearTwoRepresentative a) :=
    projectiveSpecialLinearTwoRepresentative_isPerfect a
  exact
    Group.IsPerfect.not_isMulCommutative
      (projectiveSpecialLinearTwoRepresentative a)

/-- A finite group belongs to the `PSL₂` simple family when it is
isomorphic to one of the canonical prime-power representatives above. -/
def IsProjectiveSpecialLinearTwoSimpleGroup
    (S : Type) [Group S] [Finite S] : Prop :=
  ∃ a : ProjectiveSpecialLinearTwoSimpleParameter,
    Nonempty
      (S ≃* projectiveSpecialLinearTwoRepresentative a)

/-- The isomorphism-closed family of simple groups
`PSL(2, 𝔽_{p^n})` with `p^n ≥ 4`. -/
def projectiveSpecialLinearTwoSimpleGroupFamily :
    FiniteGroupFamily.{0} where
  member S groupS finiteS :=
    @IsProjectiveSpecialLinearTwoSimpleGroup S groupS finiteS

@[simp]
theorem projectiveSpecialLinearTwoSimpleGroupFamily_contains_iff
    (S : Type) [Group S] [Finite S] :
    projectiveSpecialLinearTwoSimpleGroupFamily.Contains S ↔
      IsProjectiveSpecialLinearTwoSimpleGroup S :=
  Iff.rfl

/-- The `PSL₂` simple-family predicate is invariant under group
isomorphism. -/
theorem
    projectiveSpecialLinearTwoSimpleGroupFamily_isIsomorphismInvariant :
    projectiveSpecialLinearTwoSimpleGroupFamily.IsIsomorphismInvariant := by
  intro S T _ _ _ _ ⟨e⟩
  constructor
  · rintro ⟨a, ⟨f⟩⟩
    exact ⟨a, ⟨e.symm.trans f⟩⟩
  · rintro ⟨a, ⟨f⟩⟩
    exact ⟨a, ⟨e.trans f⟩⟩

/-- Every canonical representative belongs to the family it generates. -/
theorem projectiveSpecialLinearTwoRepresentative_mem_family
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    projectiveSpecialLinearTwoSimpleGroupFamily.Contains
      (projectiveSpecialLinearTwoRepresentative a) :=
  ⟨a, ⟨MulEquiv.refl _⟩⟩

/-- The concrete finite, simple, and noncommutative properties of every
parameterized representative. -/
theorem projectiveSpecialLinearTwoRepresentative_properties
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Finite (projectiveSpecialLinearTwoRepresentative a) ∧
      IsSimpleGroup
        (projectiveSpecialLinearTwoRepresentative a) ∧
      ¬IsMulCommutative
        (projectiveSpecialLinearTwoRepresentative a) :=
  ⟨projectiveSpecialLinearTwoRepresentative_finite a,
    projectiveSpecialLinearTwoRepresentative_isSimpleGroup a,
    projectiveSpecialLinearTwoRepresentative_not_isMulCommutative a⟩

end InductiveMcKay
end McKayConjecture
