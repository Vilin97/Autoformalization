/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.Abel
import McKayConjecture.GroupTheory.SpecialLinearTwoFivePresentation

/-!
# Perfectness of the balanced binary-icosahedral presentation

The exponent-sum matrix of

`⟨x,y,z | x² = y³ = z⁵ = xyz⟩`

has determinant `-1`.  Hence its abelianization is trivial.  We record the
integer row combinations explicitly, obtaining a kernel-checked
perfectness instance for the presented group.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The abelianization images of all three binary-icosahedral generators
are trivial. -/
theorem binaryIcosahedralPresented_generators_mem_commutator :
    Abelianization.of binaryIcosahedralPresentedX = 1 ∧
      Abelianization.of binaryIcosahedralPresentedY = 1 ∧
      Abelianization.of binaryIcosahedralPresentedZ = 1 := by
  let A :=
    Abelianization BinaryIcosahedralPresentedGroup
  let qx : Additive A :=
    Additive.ofMul
      (Abelianization.of binaryIcosahedralPresentedX)
  let qy : Additive A :=
    Additive.ofMul
      (Abelianization.of binaryIcosahedralPresentedY)
  let qz : Additive A :=
    Additive.ofMul
      (Abelianization.of binaryIcosahedralPresentedZ)
  have h₀Mul :=
    congrArg Abelianization.of
      binaryIcosahedralPresented_relations.1
  have h₁Mul :=
    congrArg Abelianization.of
      binaryIcosahedralPresented_relations.2.1
  have h₂Mul :=
    congrArg Abelianization.of
      binaryIcosahedralPresented_relations.2.2
  simp only [map_pow] at h₀Mul h₁Mul
  simp only [map_pow, map_mul] at h₂Mul
  have h₀ : 2 • qx = 3 • qy := by
    exact h₀Mul
  have h₁ : 3 • qy = 5 • qz := by
    exact h₁Mul
  have h₂ : 5 • qz = qx + qy + qz := by
    exact h₂Mul
  let r₀ : Additive A := 2 • qx - 3 • qy
  let r₁ : Additive A := 3 • qy - 5 • qz
  let r₂ : Additive A := -qx - qy + 4 • qz
  have hr₀ : r₀ = 0 :=
    sub_eq_zero.mpr h₀
  have hr₁ : r₁ = 0 :=
    sub_eq_zero.mpr h₁
  have hr₂ : r₂ = 0 := by
    dsimp [r₂]
    calc
      -qx - qy + 4 • qz =
          5 • qz - (qx + qy + qz) := by
        abel
      _ = 0 := sub_eq_zero.mpr h₂
  have hqx :
      qx =
        (-7 : ℤ) • r₀ +
          (-12 : ℤ) • r₁ +
          (-15 : ℤ) • r₂ := by
    dsimp [r₀, r₁, r₂]
    abel
  have hqy :
      qy =
        (-5 : ℤ) • r₀ +
          (-8 : ℤ) • r₁ +
          (-10 : ℤ) • r₂ := by
    dsimp [r₀, r₁, r₂]
    abel
  have hqz :
      qz =
        (-3 : ℤ) • r₀ +
          (-5 : ℤ) • r₁ +
          (-6 : ℤ) • r₂ := by
    dsimp [r₀, r₁, r₂]
    abel
  rw [hr₀, hr₁, hr₂] at hqx hqy hqz
  simp only [smul_zero, add_zero] at hqx hqy hqz
  exact ⟨hqx, hqy, hqz⟩

/-- The canonical map to the abelianization is trivial. -/
theorem binaryIcosahedralPresented_abelianization_of_eq_one :
    (Abelianization.of :
      BinaryIcosahedralPresentedGroup →*
        Abelianization BinaryIcosahedralPresentedGroup) =
      1 := by
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · exact
      binaryIcosahedralPresented_generators_mem_commutator.1
  · exact
      binaryIcosahedralPresented_generators_mem_commutator.2.1
  · exact
      binaryIcosahedralPresented_generators_mem_commutator.2.2

/-- The balanced binary-icosahedral presented group is perfect. -/
instance binaryIcosahedralPresentedGroup_isPerfect :
    Group.IsPerfect BinaryIcosahedralPresentedGroup where
  commutator_eq_top := by
    rw [← Abelianization.ker_of]
    rw [binaryIcosahedralPresented_abelianization_of_eq_one]
    simp

end GroupTheory
end McKayConjecture
