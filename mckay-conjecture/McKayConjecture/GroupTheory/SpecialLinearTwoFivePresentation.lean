/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.PresentedGroup
import McKayConjecture.GroupTheory.SpecialLinearTwoFive

/-!
# A balanced presentation of `SL(2, 𝔽₅)`

The binary icosahedral presentation

`⟨x,y,z | x² = y³ = z⁵ = xyz⟩`

has a unimodular exponent-sum matrix.  This is the presentation used to
prove that the concrete binary cover is centrally closed.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace GroupTheory

local instance : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- A subgroup of `SL(2, F)` containing every elementary transvection is
the whole special linear group. -/
theorem slTwo_subgroup_eq_top_of_transvection_mem
    {F : Type*} [Field F]
    (H : Subgroup (SL(2, F)))
    (htransvection :
      ∀ (i j : Fin 2) (hij : i ≠ j) (c : F),
        Matrix.SpecialLinearGroup.transvection hij c ∈ H) :
    H = ⊤ := by
  apply top_unique
  intro A _
  exact
    Matrix.SL2.transvection_induction
      (fun B : SL(2, F) ↦ B ∈ H)
      htransvection
      (fun _ _ hB hC ↦ H.mul_mem hB hC)
      A

/-- The order-four generator in the binary icosahedral presentation. -/
def specialLinearTwoFivePresentationX :
    SpecialLinearTwoFive :=
  specialLinearTwoFiveQuaternionI

/-- The order-six generator in the binary icosahedral presentation. -/
def specialLinearTwoFivePresentationY :
    SpecialLinearTwoFive :=
  ⟨!![(1 : ZMod 5), -1; 1, 0], by native_decide⟩

/-- The third generator, chosen so that `x*y*z = -1`. -/
def specialLinearTwoFivePresentationZ :
    SpecialLinearTwoFive :=
  (specialLinearTwoFivePresentationX *
    specialLinearTwoFivePresentationY)⁻¹ * (-1)

/-- The three standard binary-icosahedral relations hold for the concrete
matrices. -/
theorem specialLinearTwoFivePresentation_relations :
    specialLinearTwoFivePresentationX ^ 2 =
        specialLinearTwoFivePresentationY ^ 3 ∧
      specialLinearTwoFivePresentationY ^ 3 =
        specialLinearTwoFivePresentationZ ^ 5 ∧
      specialLinearTwoFivePresentationZ ^ 5 =
        specialLinearTwoFivePresentationX *
          specialLinearTwoFivePresentationY *
          specialLinearTwoFivePresentationZ := by
  native_decide

/-! ## The presented group and its concrete quotient -/

/-- The three abstract generators `x`, `y`, and `z`. -/
def binaryIcosahedralGenerator (i : Fin 3) :
    FreeGroup (Fin 3) :=
  FreeGroup.of i

/-- Relation `x² = y³`. -/
def binaryIcosahedralRelatorXY :
    FreeGroup (Fin 3) :=
  binaryIcosahedralGenerator 0 ^ 2 *
    (binaryIcosahedralGenerator 1 ^ 3)⁻¹

/-- Relation `y³ = z⁵`. -/
def binaryIcosahedralRelatorYZ :
    FreeGroup (Fin 3) :=
  binaryIcosahedralGenerator 1 ^ 3 *
    (binaryIcosahedralGenerator 2 ^ 5)⁻¹

/-- Relation `z⁵ = xyz`. -/
def binaryIcosahedralRelatorZXYZ :
    FreeGroup (Fin 3) :=
  binaryIcosahedralGenerator 2 ^ 5 *
    (binaryIcosahedralGenerator 0 *
      binaryIcosahedralGenerator 1 *
      binaryIcosahedralGenerator 2)⁻¹

/-- The balanced binary-icosahedral relator set. -/
def binaryIcosahedralRelators :
    Set (FreeGroup (Fin 3)) :=
  {binaryIcosahedralRelatorXY,
    binaryIcosahedralRelatorYZ,
    binaryIcosahedralRelatorZXYZ}

/-- The group defined by the balanced binary-icosahedral presentation. -/
abbrev BinaryIcosahedralPresentedGroup :=
  PresentedGroup binaryIcosahedralRelators

/-- Send the three abstract generators to the three concrete matrices. -/
def specialLinearTwoFivePresentationGenerator :
    Fin 3 → SpecialLinearTwoFive
  | 0 => specialLinearTwoFivePresentationX
  | 1 => specialLinearTwoFivePresentationY
  | 2 => specialLinearTwoFivePresentationZ

/-- The concrete matrices kill all three presentation relators. -/
theorem specialLinearTwoFivePresentationGenerator_kills_relators :
    ∀ r ∈ binaryIcosahedralRelators,
      FreeGroup.lift
        specialLinearTwoFivePresentationGenerator r = 1 := by
  intro r hr
  simp only [binaryIcosahedralRelators,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with (rfl | rfl | rfl) <;>
    native_decide

/-- The homomorphism from the binary-icosahedral presentation to the
concrete matrix group. -/
def binaryIcosahedralPresentationToSpecialLinearTwoFive :
    BinaryIcosahedralPresentedGroup →*
      SpecialLinearTwoFive :=
  PresentedGroup.toGroup
    specialLinearTwoFivePresentationGenerator_kills_relators

/-- The presented generator mapping to `x`. -/
def binaryIcosahedralPresentedX :
    BinaryIcosahedralPresentedGroup :=
  PresentedGroup.of 0

/-- The presented generator mapping to `y`. -/
def binaryIcosahedralPresentedY :
    BinaryIcosahedralPresentedGroup :=
  PresentedGroup.of 1

/-- The presented generator mapping to `z`. -/
def binaryIcosahedralPresentedZ :
    BinaryIcosahedralPresentedGroup :=
  PresentedGroup.of 2

/-- Each defining relator is trivial in the presented group. -/
theorem binaryIcosahedralPresented_relator_eq_one
    {r : FreeGroup (Fin 3)}
    (hr : r ∈ binaryIcosahedralRelators) :
    PresentedGroup.mk binaryIcosahedralRelators r = 1 := by
  apply
    (QuotientGroup.eq_one_iff r).mpr
  exact
    Subgroup.subset_normalClosure hr

/-- The three defining equalities inside the presented group. -/
theorem binaryIcosahedralPresented_relations :
    binaryIcosahedralPresentedX ^ 2 =
        binaryIcosahedralPresentedY ^ 3 ∧
      binaryIcosahedralPresentedY ^ 3 =
        binaryIcosahedralPresentedZ ^ 5 ∧
      binaryIcosahedralPresentedZ ^ 5 =
        binaryIcosahedralPresentedX *
          binaryIcosahedralPresentedY *
          binaryIcosahedralPresentedZ := by
  constructor
  · apply mul_inv_eq_one.mp
    simpa [binaryIcosahedralPresentedX,
      binaryIcosahedralPresentedY,
      PresentedGroup.of,
      binaryIcosahedralRelatorXY,
      binaryIcosahedralGenerator] using
        binaryIcosahedralPresented_relator_eq_one
          (r := binaryIcosahedralRelatorXY)
          (by
            simp [binaryIcosahedralRelators])
  constructor
  · apply mul_inv_eq_one.mp
    simpa [binaryIcosahedralPresentedY,
      binaryIcosahedralPresentedZ,
      PresentedGroup.of,
      binaryIcosahedralRelatorYZ,
      binaryIcosahedralGenerator] using
        binaryIcosahedralPresented_relator_eq_one
          (r := binaryIcosahedralRelatorYZ)
          (by
            simp [binaryIcosahedralRelators])
  · apply mul_inv_eq_one.mp
    simpa [binaryIcosahedralPresentedX,
      binaryIcosahedralPresentedY,
      binaryIcosahedralPresentedZ,
      PresentedGroup.of,
      binaryIcosahedralRelatorZXYZ,
      binaryIcosahedralGenerator] using
        binaryIcosahedralPresented_relator_eq_one
          (r := binaryIcosahedralRelatorZXYZ)
          (by
            simp [binaryIcosahedralRelators])

/-- A word mapping to the upper transvection with parameter `c`. -/
def binaryIcosahedralUpperTransvectionPreimage
    (c : ZMod 5) :
    BinaryIcosahedralPresentedGroup :=
  binaryIcosahedralPresentedX *
    (binaryIcosahedralPresentedX *
      binaryIcosahedralPresentedY) ^ c.val *
    binaryIcosahedralPresentedX⁻¹

/-- A word mapping to the lower transvection with parameter `c`. -/
def binaryIcosahedralLowerTransvectionPreimage
    (c : ZMod 5) :
    BinaryIcosahedralPresentedGroup :=
  (binaryIcosahedralPresentedX *
    binaryIcosahedralPresentedY) ^
      ((5 - c.val) % 5)

@[simp]
theorem binaryIcosahedralPresentationToSpecialLinearTwoFive_x :
    binaryIcosahedralPresentationToSpecialLinearTwoFive
        binaryIcosahedralPresentedX =
      specialLinearTwoFivePresentationX := by
  simp [binaryIcosahedralPresentationToSpecialLinearTwoFive,
    binaryIcosahedralPresentedX,
    specialLinearTwoFivePresentationGenerator]

@[simp]
theorem binaryIcosahedralPresentationToSpecialLinearTwoFive_y :
    binaryIcosahedralPresentationToSpecialLinearTwoFive
        binaryIcosahedralPresentedY =
      specialLinearTwoFivePresentationY := by
  simp [binaryIcosahedralPresentationToSpecialLinearTwoFive,
    binaryIcosahedralPresentedY,
    specialLinearTwoFivePresentationGenerator]

/-- Explicit words lift every upper transvection. -/
theorem binaryIcosahedralUpperTransvectionPreimage_mapsTo
    (c : ZMod 5) :
    binaryIcosahedralPresentationToSpecialLinearTwoFive
        (binaryIcosahedralUpperTransvectionPreimage c) =
      Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 2) ≠ 1 by decide) c := by
  simp only [binaryIcosahedralUpperTransvectionPreimage,
    map_mul, map_pow, map_inv,
    binaryIcosahedralPresentationToSpecialLinearTwoFive_x,
    binaryIcosahedralPresentationToSpecialLinearTwoFive_y]
  fin_cases c <;> native_decide

/-- Explicit words lift every lower transvection. -/
theorem binaryIcosahedralLowerTransvectionPreimage_mapsTo
    (c : ZMod 5) :
    binaryIcosahedralPresentationToSpecialLinearTwoFive
        (binaryIcosahedralLowerTransvectionPreimage c) =
      Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 2) ≠ 0 by decide) c := by
  simp only [binaryIcosahedralLowerTransvectionPreimage,
    map_mul, map_pow,
    binaryIcosahedralPresentationToSpecialLinearTwoFive_x,
    binaryIcosahedralPresentationToSpecialLinearTwoFive_y]
  fin_cases c <;> native_decide

/-- An opaque name for the concrete range, used to keep the transvection
induction below within the default heartbeat budget. -/
def binaryIcosahedralConcreteRange :
    Subgroup SpecialLinearTwoFive :=
  binaryIcosahedralPresentationToSpecialLinearTwoFive.range

/-- Every elementary transvection lies in the range of the presentation
map. -/
theorem binaryIcosahedralPresentationToSpecialLinearTwoFive_transvection_mem_range
    (i j : Fin 2) (hij : i ≠ j) (c : ZMod 5) :
    Matrix.SpecialLinearGroup.transvection hij c ∈
      binaryIcosahedralConcreteRange := by
  change
    Matrix.SpecialLinearGroup.transvection hij c ∈
      binaryIcosahedralPresentationToSpecialLinearTwoFive.range
  fin_cases i
  · obtain rfl : j = 1 := by
      fin_cases j <;> tauto
    exact
      ⟨binaryIcosahedralUpperTransvectionPreimage c,
        binaryIcosahedralUpperTransvectionPreimage_mapsTo c⟩
  · obtain rfl : j = 0 := by
      fin_cases j <;> tauto
    exact
      ⟨binaryIcosahedralLowerTransvectionPreimage c,
        binaryIcosahedralLowerTransvectionPreimage_mapsTo c⟩

/-- The opaque concrete range is all of `SL(2, ZMod 5)`. -/
theorem binaryIcosahedralConcreteRange_eq_top :
    binaryIcosahedralConcreteRange = ⊤ := by
  apply
    slTwo_subgroup_eq_top_of_transvection_mem
      (F := ZMod 5)
  intro i j hij c
  exact
    binaryIcosahedralPresentationToSpecialLinearTwoFive_transvection_mem_range
      i j hij c

/-- The presentation map has full range. -/
theorem binaryIcosahedralPresentationToSpecialLinearTwoFive_range :
    binaryIcosahedralPresentationToSpecialLinearTwoFive.range =
      ⊤ := by
  change binaryIcosahedralConcreteRange = ⊤
  exact binaryIcosahedralConcreteRange_eq_top

/-- The balanced presentation maps onto every matrix in
`SL(2, ZMod 5)`. -/
theorem binaryIcosahedralPresentationToSpecialLinearTwoFive_surjective :
    Function.Surjective
      binaryIcosahedralPresentationToSpecialLinearTwoFive :=
  MonoidHom.range_eq_top.mp
    binaryIcosahedralPresentationToSpecialLinearTwoFive_range

end GroupTheory
end McKayConjecture
