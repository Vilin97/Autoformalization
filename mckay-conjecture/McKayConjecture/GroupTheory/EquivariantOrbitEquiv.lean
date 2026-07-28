/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Equivariant equivalences and orbit spaces

An equivariant equivalence identifies orbit spaces and preserves
stabilizers.  These elementary facts are used to turn equivariant
character correspondences on normal subgroups into equivalences of the
Clifford-orbit indices.
-/

noncomputable section

universe u v w

namespace McKayConjecture.GroupTheory

variable {A : Type u} [Group A]
variable {X : Type v} {Y : Type w}
variable [MulAction A X] [MulAction A Y]

/-- An equivariant equivalence induces an equivalence of orbit
quotients. -/
def equivariantOrbitQuotientEquiv
    (e : X ≃ Y)
    (he : ∀ (a : A) (x : X), e (a • x) = a • e x) :
    MulAction.orbitRel.Quotient A X ≃
      MulAction.orbitRel.Quotient A Y :=
  Quotient.congr e fun x y ↦ by
    simp only [MulAction.orbitRel_apply,
      MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← he]
      exact congrArg e ha
    · rintro ⟨a, ha⟩
      refine ⟨a, e.injective ?_⟩
      rw [he]
      exact ha

@[simp]
theorem equivariantOrbitQuotientEquiv_mk
    (e : X ≃ Y)
    (he : ∀ (a : A) (x : X), e (a • x) = a • e x)
    (x : X) :
    equivariantOrbitQuotientEquiv e he
        (Quotient.mk'' x) =
      Quotient.mk'' (e x) :=
  rfl

/-- An equivariant equivalence sends each orbit onto the corresponding
orbit. -/
theorem image_orbit_eq_of_equivariant_equiv
    (e : X ≃ Y)
    (he : ∀ (a : A) (x : X), e (a • x) = a • e x)
    (x : X) :
    Set.image e (MulAction.orbit A x) =
      MulAction.orbit A (e x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, rfl⟩ :=
      MulAction.mem_orbit_iff.mp hz
    rw [he]
    exact MulAction.mem_orbit _ _
  · intro hy
    obtain ⟨a, ha⟩ :=
      MulAction.mem_orbit_iff.mp hy
    refine ⟨a • x, MulAction.mem_orbit _ _, ?_⟩
    rw [he]
    exact ha

/-- Stabilizers are literally equal under an equivariant equivalence
for actions of the same group. -/
theorem stabilizer_eq_of_equivariant_equiv
    (e : X ≃ Y)
    (he : ∀ (a : A) (x : X), e (a • x) = a • e x)
    (x : X) :
    MulAction.stabilizer A (e x) =
      MulAction.stabilizer A x := by
  ext a
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro ha
    apply e.injective
    rw [he, ha]
  · intro ha
    rw [← he, ha]

end McKayConjecture.GroupTheory
