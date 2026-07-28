/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFivePresentation

/-!
# The two-generator binary-icosahedral presentation

Eliminating `x` from the balanced presentation

`⟨x,y,z | x² = y³ = z⁵ = xyz⟩`

gives the standard two-generator presentation

`⟨a,b | (ab)² = a³ = b⁵⟩`.

This file defines that presentation and proves that it maps onto the
balanced presentation.  The finite normal-form certificate is kept in a
separate file.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- A word in the two abstract generators. -/
def binaryIcosahedralTwoGenerator (i : Fin 2) :
    FreeGroup (Fin 2) :=
  FreeGroup.of i

/-- The relation `a³ = b⁵`. -/
def binaryIcosahedralTwoRelatorPower :
    FreeGroup (Fin 2) :=
  binaryIcosahedralTwoGenerator 0 ^ 3 *
    (binaryIcosahedralTwoGenerator 1 ^ 5)⁻¹

/-- The relation `(ab)² = a³`. -/
def binaryIcosahedralTwoRelatorProduct :
    FreeGroup (Fin 2) :=
  (binaryIcosahedralTwoGenerator 0 *
      binaryIcosahedralTwoGenerator 1) ^ 2 *
    (binaryIcosahedralTwoGenerator 0 ^ 3)⁻¹

/-- The two standard binary-icosahedral relators. -/
def binaryIcosahedralTwoRelators :
    Set (FreeGroup (Fin 2)) :=
  {binaryIcosahedralTwoRelatorPower,
    binaryIcosahedralTwoRelatorProduct}

/-- The group `⟨a,b | (ab)² = a³ = b⁵⟩`. -/
abbrev BinaryIcosahedralTwoPresentedGroup :=
  PresentedGroup binaryIcosahedralTwoRelators

/-- The presented generator `a`. -/
def binaryIcosahedralTwoPresentedA :
    BinaryIcosahedralTwoPresentedGroup :=
  PresentedGroup.of 0

/-- The presented generator `b`. -/
def binaryIcosahedralTwoPresentedB :
    BinaryIcosahedralTwoPresentedGroup :=
  PresentedGroup.of 1

/-- Both defining equalities in the two-generator presented group. -/
theorem binaryIcosahedralTwoPresented_relations :
    (binaryIcosahedralTwoPresentedA *
        binaryIcosahedralTwoPresentedB) ^ 2 =
      binaryIcosahedralTwoPresentedA ^ 3 ∧
    binaryIcosahedralTwoPresentedA ^ 3 =
      binaryIcosahedralTwoPresentedB ^ 5 := by
  constructor
  · apply mul_inv_eq_one.mp
    simpa [binaryIcosahedralTwoPresentedA,
      binaryIcosahedralTwoPresentedB,
      PresentedGroup.of,
      binaryIcosahedralTwoRelatorProduct,
      binaryIcosahedralTwoGenerator] using
        PresentedGroup.one_of_mem
          (rels := binaryIcosahedralTwoRelators)
          (x := binaryIcosahedralTwoRelatorProduct)
          (by simp [binaryIcosahedralTwoRelators])
  · apply mul_inv_eq_one.mp
    simpa [binaryIcosahedralTwoPresentedA,
      binaryIcosahedralTwoPresentedB,
      PresentedGroup.of,
      binaryIcosahedralTwoRelatorPower,
      binaryIcosahedralTwoGenerator] using
        PresentedGroup.one_of_mem
          (rels := binaryIcosahedralTwoRelators)
          (x := binaryIcosahedralTwoRelatorPower)
          (by simp [binaryIcosahedralTwoRelators])

/-- In the balanced presentation, `x` is the product `yz`. -/
theorem binaryIcosahedralPresented_x_eq_y_mul_z :
    binaryIcosahedralPresentedX =
      binaryIcosahedralPresentedY *
        binaryIcosahedralPresentedZ := by
  apply mul_left_cancel
    (a := binaryIcosahedralPresentedX)
  simpa [pow_two, mul_assoc] using
    binaryIcosahedralPresented_relations.1.trans
      (binaryIcosahedralPresented_relations.2.1.trans
        binaryIcosahedralPresented_relations.2.2)

/-- The images `a ↦ y`, `b ↦ z` satisfy the two relators. -/
theorem binaryIcosahedralTwoToBalancedGenerator_kills_relators :
    ∀ r ∈ binaryIcosahedralTwoRelators,
      FreeGroup.lift
        (fun i : Fin 2 ↦
          if i = 0 then binaryIcosahedralPresentedY
          else binaryIcosahedralPresentedZ) r = 1 := by
  intro r hr
  simp only [binaryIcosahedralTwoRelators,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · simp only [binaryIcosahedralTwoRelatorPower,
      binaryIcosahedralTwoGenerator, map_mul, map_pow,
      FreeGroup.lift_apply_of, map_inv]
    simp only [ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    exact
      mul_inv_eq_one.mpr
        binaryIcosahedralPresented_relations.2.1
  · simp only [binaryIcosahedralTwoRelatorProduct,
      binaryIcosahedralTwoGenerator, map_mul, map_pow,
      FreeGroup.lift_apply_of, map_inv]
    simp only [ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    apply mul_inv_eq_one.mpr
    rw [← binaryIcosahedralPresented_x_eq_y_mul_z]
    exact binaryIcosahedralPresented_relations.1

/-- The Tietze map from the two-generator presentation to the balanced
presentation. -/
def binaryIcosahedralTwoPresentationToBalanced :
    BinaryIcosahedralTwoPresentedGroup →*
      BinaryIcosahedralPresentedGroup :=
  PresentedGroup.toGroup
    binaryIcosahedralTwoToBalancedGenerator_kills_relators

@[simp]
theorem binaryIcosahedralTwoPresentationToBalanced_a :
    binaryIcosahedralTwoPresentationToBalanced
        binaryIcosahedralTwoPresentedA =
      binaryIcosahedralPresentedY := by
  simp [binaryIcosahedralTwoPresentationToBalanced,
    binaryIcosahedralTwoPresentedA]

@[simp]
theorem binaryIcosahedralTwoPresentationToBalanced_b :
    binaryIcosahedralTwoPresentationToBalanced
        binaryIcosahedralTwoPresentedB =
      binaryIcosahedralPresentedZ := by
  simp [binaryIcosahedralTwoPresentationToBalanced,
    binaryIcosahedralTwoPresentedB]

/-- The two-generator presentation maps onto the balanced presentation. -/
theorem binaryIcosahedralTwoPresentationToBalanced_surjective :
    Function.Surjective
      binaryIcosahedralTwoPresentationToBalanced := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  intro g _
  apply
    PresentedGroup.generated_by
      binaryIcosahedralRelators
      binaryIcosahedralTwoPresentationToBalanced.range
      (x := g)
  intro i
  fin_cases i
  · refine ⟨
      binaryIcosahedralTwoPresentedA *
        binaryIcosahedralTwoPresentedB, ?_⟩
    simp only [map_mul,
      binaryIcosahedralTwoPresentationToBalanced_a,
      binaryIcosahedralTwoPresentationToBalanced_b]
    exact binaryIcosahedralPresented_x_eq_y_mul_z.symm
  · exact ⟨binaryIcosahedralTwoPresentedA, by
      simp [binaryIcosahedralPresentedY]⟩
  · exact ⟨binaryIcosahedralTwoPresentedB, by
      simp [binaryIcosahedralPresentedZ]⟩

end GroupTheory
end McKayConjecture
