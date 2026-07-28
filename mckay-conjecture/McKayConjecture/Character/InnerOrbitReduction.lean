/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Index
import McKayConjecture.Character.Inertia
import McKayConjecture.GroupTheory.OrbitProduct

/-!
# Reduction of character orbits modulo inner automorphisms

Let `N` be a normal subgroup of `A`.  Every element of `N` acts trivially
on `Irr(N)`, and hence also on `Irr_{p'}(N)`, because inner conjugation
does not change a character.  Consequently, if `A = N H`, equivalently
`N ⊔ H = ⊤`, then the `A`-orbits on these character spaces are exactly
the `H`-orbits.

This file specializes the abstract product-orbit results in
`McKayConjecture.GroupTheory.OrbitProduct` to the conjugation actions
defined in `McKayConjecture.Character.Inertia`.
-/

noncomputable section

universe u

namespace McKayConjecture

variable {A : Type u} [Group A]

namespace IrreducibleCharacter

/-- An element of a normal subgroup acts trivially on every irreducible
character of that subgroup. -/
theorem normalSubgroup_smul_eq
    (N : Subgroup A) [N.Normal]
    (n : N) (θ : IrreducibleCharacter N) :
    (n : A) • θ = θ := by
  exact
    (mem_inertia_iff N θ (n : A)).mp
      (subgroup_le_inertia N θ n.2)

/-- If `A = N H`, ambient conjugacy orbits on `Irr(N)` are the
`H`-conjugacy orbits. -/
theorem orbit_eq_subgroup_orbit_of_sup_eq_top
    (N H : Subgroup A) [N.Normal]
    (hsup : N ⊔ H = ⊤)
    (θ : IrreducibleCharacter N) :
    MulAction.orbit A θ = MulAction.orbit H θ := by
  apply
    GroupTheory.orbit_eq_subgroup_orbit_of_product_of_trivial
      N H
  · intro a
    have ha : a ∈ N ⊔ H := by
      rw [hsup]
      exact Subgroup.mem_top a
    obtain ⟨n, hn, h, hh, hnh⟩ :=
      Subgroup.mem_sup_of_normal_left.mp ha
    exact ⟨⟨n, hn⟩, ⟨h, hh⟩, hnh⟩
  · exact fun n χ ↦ normalSubgroup_smul_eq N n χ

/-- If `A = N H`, the orbit quotient of `Irr(N)` by `A` is canonically
equivalent to its orbit quotient by `H`. -/
def orbitQuotientEquivSubgroupOfSupEqTop
    (N H : Subgroup A) [N.Normal]
    (hsup : N ⊔ H = ⊤) :
    MulAction.orbitRel.Quotient A (IrreducibleCharacter N) ≃
      MulAction.orbitRel.Quotient H (IrreducibleCharacter N) :=
  GroupTheory.orbitQuotientEquivSubgroupOfProductOfTrivial
    N H
    (fun a ↦ by
      have ha : a ∈ N ⊔ H := by
        rw [hsup]
        exact Subgroup.mem_top a
      obtain ⟨n, hn, h, hh, hnh⟩ :=
        Subgroup.mem_sup_of_normal_left.mp ha
      exact ⟨⟨n, hn⟩, ⟨h, hh⟩, hnh⟩)
    (fun n χ ↦ normalSubgroup_smul_eq N n χ)

@[simp]
theorem orbitQuotientEquivSubgroupOfSupEqTop_mk
    (N H : Subgroup A) [N.Normal]
    (hsup : N ⊔ H = ⊤)
    (θ : IrreducibleCharacter N) :
    orbitQuotientEquivSubgroupOfSupEqTop N H hsup
        (Quotient.mk'' θ) =
      Quotient.mk'' θ :=
  rfl

end IrreducibleCharacter

namespace PPrimeIrreducibleCharacter

/-- An element of a normal subgroup acts trivially on every
prime-to-`p` irreducible character of that subgroup. -/
theorem normalSubgroup_smul_eq
    (N : Subgroup A) [N.Normal] (p : ℕ)
    (n : N) (θ : PPrimeIrreducibleCharacter N p) :
    (n : A) • θ = θ := by
  apply Subtype.ext
  exact
    IrreducibleCharacter.normalSubgroup_smul_eq
      N n θ.1

/-- If `A = N H`, ambient conjugacy orbits on `Irr_{p'}(N)` are the
`H`-conjugacy orbits. -/
theorem orbit_eq_subgroup_orbit_of_sup_eq_top
    (N H : Subgroup A) [N.Normal] (p : ℕ)
    (hsup : N ⊔ H = ⊤)
    (θ : PPrimeIrreducibleCharacter N p) :
    MulAction.orbit A θ = MulAction.orbit H θ := by
  apply
    GroupTheory.orbit_eq_subgroup_orbit_of_product_of_trivial
      N H
  · intro a
    have ha : a ∈ N ⊔ H := by
      rw [hsup]
      exact Subgroup.mem_top a
    obtain ⟨n, hn, h, hh, hnh⟩ :=
      Subgroup.mem_sup_of_normal_left.mp ha
    exact ⟨⟨n, hn⟩, ⟨h, hh⟩, hnh⟩
  · exact fun n χ ↦ normalSubgroup_smul_eq N p n χ

/-- If `A = N H`, the orbit quotient of `Irr_{p'}(N)` by `A` is
canonically equivalent to its orbit quotient by `H`. -/
def orbitQuotientEquivSubgroupOfSupEqTop
    (N H : Subgroup A) [N.Normal] (p : ℕ)
    (hsup : N ⊔ H = ⊤) :
    MulAction.orbitRel.Quotient A
        (PPrimeIrreducibleCharacter N p) ≃
      MulAction.orbitRel.Quotient H
        (PPrimeIrreducibleCharacter N p) :=
  GroupTheory.orbitQuotientEquivSubgroupOfProductOfTrivial
    N H
    (fun a ↦ by
      have ha : a ∈ N ⊔ H := by
        rw [hsup]
        exact Subgroup.mem_top a
      obtain ⟨n, hn, h, hh, hnh⟩ :=
        Subgroup.mem_sup_of_normal_left.mp ha
      exact ⟨⟨n, hn⟩, ⟨h, hh⟩, hnh⟩)
    (fun n χ ↦ normalSubgroup_smul_eq N p n χ)

@[simp]
theorem orbitQuotientEquivSubgroupOfSupEqTop_mk
    (N H : Subgroup A) [N.Normal] (p : ℕ)
    (hsup : N ⊔ H = ⊤)
    (θ : PPrimeIrreducibleCharacter N p) :
    orbitQuotientEquivSubgroupOfSupEqTop N H p hsup
        (Quotient.mk'' θ) =
      Quotient.mk'' θ :=
  rfl

/-- Under `A = N H`, the ambient and `H`-orbit cardinalities of a
prime-to-`p` character agree. -/
theorem orbit_ncard_eq_subgroup_orbit_ncard_of_sup_eq_top
    (N H : Subgroup A) [N.Normal] (p : ℕ)
    (hsup : N ⊔ H = ⊤)
    (θ : PPrimeIrreducibleCharacter N p) :
    (MulAction.orbit A θ).ncard =
      (MulAction.orbit H θ).ncard := by
  rw [orbit_eq_subgroup_orbit_of_sup_eq_top N H p hsup θ]

/-- Under `A = N H`, the inertia index for the ambient action equals
the stabilizer index for the restricted `H`-action. -/
theorem stabilizer_index_eq_subgroup_stabilizer_index_of_sup_eq_top
    (N H : Subgroup A) [N.Normal] (p : ℕ)
    (hsup : N ⊔ H = ⊤)
    (θ : PPrimeIrreducibleCharacter N p) :
    (MulAction.stabilizer A θ).index =
      (MulAction.stabilizer H θ).index := by
  rw [MulAction.index_stabilizer,
    MulAction.index_stabilizer,
    orbit_eq_subgroup_orbit_of_sup_eq_top N H p hsup θ]

end PPrimeIrreducibleCharacter

end McKayConjecture
