/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Orbits under a product with a trivially acting subgroup

If every ambient element is a product `k h` and `K` acts trivially on the
whole action space, then ambient orbits are exactly `H`-orbits.  The
corresponding orbit quotients are therefore canonically equivalent.

For character theory, `K` is typically a normal subgroup acting by inner
automorphisms on `Irr(K)`; that action is trivial because characters are
class functions.
-/

noncomputable section

universe u v

namespace McKayConjecture.GroupTheory

variable {A : Type u} [Group A]
variable {X : Type v} [MulAction A X]

/-- Ambient and subgroup orbits agree when the ambient group factors as
`K H` and `K` acts trivially on every point. -/
theorem orbit_eq_subgroup_orbit_of_product_of_trivial
    (K H : Subgroup A)
    (hfactor :
      ∀ a : A, ∃ k : K, ∃ h : H,
        (k : A) * (h : A) = a)
    (htrivial :
      ∀ (k : K) (x : X), (k : A) • x = x)
    (x : X) :
    MulAction.orbit A x =
      MulAction.orbit H x := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha⟩ :=
      MulAction.mem_orbit_iff.mp hy
    obtain ⟨k, h, hkh⟩ := hfactor a
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨h, ?_⟩
    calc
      (h : A) • x =
          (k : A) • ((h : A) • x) := by
        rw [htrivial]
      _ = ((k : A) * (h : A)) • x := by
        rw [mul_smul]
      _ = a • x := by rw [hkh]
      _ = y := ha
  · intro hy
    obtain ⟨h, hh⟩ :=
      MulAction.mem_orbit_iff.mp hy
    exact
      MulAction.mem_orbit_iff.mpr
        ⟨(h : A), hh⟩

/-- The orbit relation for the ambient action is the orbit relation for
`H` under the same hypotheses. -/
theorem orbitRel_iff_subgroup_orbitRel_of_product_of_trivial
    (K H : Subgroup A)
    (hfactor :
      ∀ a : A, ∃ k : K, ∃ h : H,
        (k : A) * (h : A) = a)
    (htrivial :
      ∀ (k : K) (x : X), (k : A) • x = x)
    (x y : X) :
    MulAction.orbitRel A X x y ↔
      MulAction.orbitRel H X x y := by
  simp only [MulAction.orbitRel_apply]
  rw [orbit_eq_subgroup_orbit_of_product_of_trivial
    K H hfactor htrivial y]

/-- Canonical identification of the ambient orbit quotient with the
`H`-orbit quotient.  The map is induced by the identity on the action
space. -/
def orbitQuotientEquivSubgroupOfProductOfTrivial
    (K H : Subgroup A)
    (hfactor :
      ∀ a : A, ∃ k : K, ∃ h : H,
        (k : A) * (h : A) = a)
    (htrivial :
      ∀ (k : K) (x : X), (k : A) • x = x) :
    MulAction.orbitRel.Quotient A X ≃
      MulAction.orbitRel.Quotient H X :=
  Quotient.congrRight
    (orbitRel_iff_subgroup_orbitRel_of_product_of_trivial
      K H hfactor htrivial)

@[simp]
theorem orbitQuotientEquivSubgroupOfProductOfTrivial_mk
    (K H : Subgroup A)
    (hfactor :
      ∀ a : A, ∃ k : K, ∃ h : H,
        (k : A) * (h : A) = a)
    (htrivial :
      ∀ (k : K) (x : X), (k : A) • x = x)
    (x : X) :
    orbitQuotientEquivSubgroupOfProductOfTrivial
        K H hfactor htrivial (Quotient.mk'' x) =
      Quotient.mk'' x :=
  rfl

end McKayConjecture.GroupTheory
