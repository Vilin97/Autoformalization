/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Units.Hom

/-!
# Assembling units from a graded monoid family

This file isolates the elementary algebra needed after constructing a
multiplicative collapse of a graded family.  A multiplicative section
of the family maps to a monoid homomorphism in the target.  When the
grading monoid is a group, the image automatically consists of units,
with inverse supplied by the inverse degree.

No associativity law on the whole family is needed for this conclusion:
only the multiplication law on the distinguished section and the
multiplicativity of the collapse are used.
-/

namespace GradedMonoidFamily

/-- A family of types graded by a monoid, with a chosen identity and
products landing in the product degree. -/
structure Data (G : Type*) [Monoid G] where
  /-- The type in each degree. -/
  carrier : G → Type*
  /-- The distinguished element in the identity degree. -/
  one : carrier 1
  /-- Multiplication between homogeneous degrees. -/
  mul :
    ∀ g h : G, carrier g → carrier h → carrier (g * h)

/-- A multiplicative choice of one distinguished element in every
degree of a graded family. -/
structure Section {G : Type*} [Monoid G] (F : Data G) where
  /-- The distinguished homogeneous element. -/
  val : ∀ g : G, F.carrier g
  /-- The identity degree contains the chosen family identity. -/
  val_one : val 1 = F.one
  /-- Distinguished homogeneous elements multiply degreewise. -/
  val_mul :
    ∀ g h : G,
      F.mul g h (val g) (val h) = val (g * h)

/-- A multiplicative collapse from a graded family to an ordinary
monoid.  The maps are required to respect all homogeneous products,
not merely a preselected section. -/
structure Collapse {G : Type*} [Monoid G]
    (F : Data G) (M : Type*) [Monoid M] where
  /-- The map out of each homogeneous degree. -/
  toFun : ∀ g : G, F.carrier g → M
  /-- The family identity maps to the target identity. -/
  map_one : toFun 1 F.one = 1
  /-- Homogeneous products map to products in the target. -/
  map_mul :
    ∀ (g h : G) (x : F.carrier g) (y : F.carrier h),
      toFun (g * h) (F.mul g h x y) =
        toFun g x * toFun h y

namespace Collapse

section Monoid

variable {G M : Type*} [Monoid G] [Monoid M]
variable {F : Data G}

/-- A collapse sends a multiplicative section to a monoid
homomorphism. -/
def sectionMonoidHom
    (C : Collapse F M)
    (S : Section F) :
    G →* M where
  toFun := fun g ↦ C.toFun g (S.val g)
  map_one' := by
    rw [S.val_one, C.map_one]
  map_mul' := by
    intro g h
    rw [← C.map_mul, S.val_mul]

@[simp]
theorem sectionMonoidHom_apply
    (C : Collapse F M)
    (S : Section F)
    (g : G) :
    C.sectionMonoidHom S g = C.toFun g (S.val g) :=
  rfl

end Monoid

section Group

variable {G M : Type*} [Group G] [Monoid M]
variable {F : Data G}

/-- If the grading monoid is a group, the collapsed section lands
canonically in the units of the target monoid. -/
def sectionUnitsHom
    (C : Collapse F M)
    (S : Section F) :
    G →* Mˣ :=
  (C.sectionMonoidHom S).toHomUnits

@[simp]
theorem coe_sectionUnitsHom
    (C : Collapse F M)
    (S : Section F)
    (g : G) :
    (C.sectionUnitsHom S g : M) =
      C.toFun g (S.val g) :=
  rfl

/-- The inverse of a collapsed homogeneous section value is the
collapsed value in the inverse degree. -/
@[simp]
theorem coe_inv_sectionUnitsHom
    (C : Collapse F M)
    (S : Section F)
    (g : G) :
    (↑((C.sectionUnitsHom S g)⁻¹) : M) =
      C.toFun g⁻¹ (S.val g⁻¹) := by
  change
    (C.sectionMonoidHom S g⁻¹ : M) =
      C.toFun g⁻¹ (S.val g⁻¹)
  rfl

/-- Every collapsed section value is a unit, independently of any
cancellation assumptions on the target monoid. -/
theorem isUnit_toFun_section
    (C : Collapse F M)
    (S : Section F)
    (g : G) :
    IsUnit (C.toFun g (S.val g)) :=
  ⟨C.sectionUnitsHom S g,
    C.coe_sectionUnitsHom S g⟩

end Group

end Collapse
end GradedMonoidFamily
