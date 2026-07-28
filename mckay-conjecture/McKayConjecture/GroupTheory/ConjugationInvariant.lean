/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Conjugation-invariant functions

A function on a group need not be a class function globally.  The elements
whose inner automorphisms preserve it nevertheless form a subgroup.  This
small interface lets finite checks on a generating set promote a candidate
class label to a genuine conjugacy invariant.
-/

namespace McKayConjecture
namespace GroupTheory

/-- The subgroup of elements whose conjugation preserves `f` everywhere. -/
def conjugationInvariantSubgroup
    {G X : Type*} [Group G] (f : G → X) :
    Subgroup G where
  carrier := {g | ∀ x, f (g * x * g⁻¹) = f x}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro g h hg hh x
    calc
      f ((g * h) * x * (g * h)⁻¹) =
          f (g * (h * x * h⁻¹) * g⁻¹) := by
            congr 1
            simp only [mul_inv_rev]
            simp [mul_assoc]
      _ = f (h * x * h⁻¹) := hg _
      _ = f x := hh x
  inv_mem' := by
    intro g hg x
    have h := (hg (g⁻¹ * x * g)).symm
    simpa [mul_assoc] using h

/-- Membership in `conjugationInvariantSubgroup` is the expected invariance
identity. -/
theorem conjugationInvariantSubgroup_apply
    {G X : Type*} [Group G] (f : G → X)
    {g : G}
    (hg : g ∈ conjugationInvariantSubgroup f)
    (x : G) :
    f (g * x * g⁻¹) = f x :=
  hg x

/-- A multiplicative equivalence induces an equivalence of conjugacy-class
quotients. -/
def conjugacyClassesEquivOfMulEquiv
    {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) :
    ConjClasses G ≃ ConjClasses H where
  toFun := ConjClasses.map equivalence.toMonoidHom
  invFun := ConjClasses.map equivalence.symm.toMonoidHom
  left_inv := by
    intro conjugacyClass
    obtain ⟨g, rfl⟩ :=
      ConjClasses.mk_surjective conjugacyClass
    change
      ConjClasses.mk (equivalence.symm (equivalence g)) =
        ConjClasses.mk g
    rw [equivalence.symm_apply_apply]
  right_inv := by
    intro conjugacyClass
    obtain ⟨h, rfl⟩ :=
      ConjClasses.mk_surjective conjugacyClass
    change
      ConjClasses.mk (equivalence (equivalence.symm h)) =
        ConjClasses.mk h
    rw [equivalence.apply_symm_apply]

end GroupTheory
end McKayConjecture
