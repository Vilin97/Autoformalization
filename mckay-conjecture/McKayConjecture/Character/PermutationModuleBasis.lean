/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotient
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Permutation bases for linear group actions

This file packages a basis which is permuted by a linear group action.
It also records the elementary coordinate identities used to describe
the invariant subspace orbit by orbit.
-/

noncomputable section

open scoped BigOperators

namespace Representation

variable {k P V ι : Type}
variable [CommRing k] [Group P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι]

/-- A basis of a linear `P`-module which is permuted by `P`. -/
structure PermutationModuleBasis where
  /-- The underlying module basis. -/
  basis : Module.Basis ι k V
  /-- The action on vectors agrees with the action on basis indices. -/
  smul_basis : ∀ (g : P) (i : ι), g • basis i = basis (g • i)

namespace PermutationModuleBasis

variable (B : PermutationModuleBasis (k := k) (P := P) (V := V) (ι := ι))

/-- The representation underlying the given compatible scalar action. -/
abbrev representation
    (_B : PermutationModuleBasis
      (k := k) (P := P) (V := V) (ι := ι)) :
    Representation k P V :=
  Representation.ofDistribMulAction k P V

@[simp]
theorem representation_apply (g : P) (v : V) :
    B.representation g v = g • v :=
  rfl

variable [Finite ι]

noncomputable local instance permutationModuleBasisIndexFintype :
    Fintype ι :=
  Fintype.ofFinite ι

/-- Applying a group element permutes the coordinates of a vector in
the same way as it permutes the basis. -/
theorem coord_smul (g : P) (i : ι) (v : V) :
    B.basis.coord (g • i) (g • v) = B.basis.coord i v := by
  have hsmul :
      g • v =
        ∑ j : ι,
          B.basis.coord j v • B.basis (g • j) := by
    calc
      g • v =
          g • ∑ j : ι,
            B.basis.coord j v • B.basis j := by
              simpa only [Module.Basis.coord_apply] using
                congrArg (fun w : V => g • w)
                  (B.basis.sum_repr v).symm
      _ = ∑ j : ι,
          g • (B.basis.coord j v • B.basis j) :=
            Finset.smul_sum
      _ = ∑ j : ι,
          B.basis.coord j v • B.basis (g • j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [smul_comm, B.smul_basis]
  rw [hsmul, map_sum]
  simp only [map_smul]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    have hne : g • j ≠ g • i := by
      exact (MulAction.toPerm g).injective.ne hj
    simp [hne]

/-- Equivalent contravariant form of `coord_smul`. -/
theorem coord_smul_eq (g : P) (i : ι) (v : V) :
    B.basis.coord i (g • v) =
      B.basis.coord (g⁻¹ • i) v := by
  simpa using B.coord_smul g (g⁻¹ • i) v

/-- The coordinates of an invariant vector are constant on every
`P`-orbit of basis indices. -/
theorem coord_eq_of_mem_invariants
    {v : V}
    (hv : v ∈ invariants B.representation)
    (g : P) (i : ι) :
    B.basis.coord (g • i) v = B.basis.coord i v := by
  have hvg : g • v = v := by
    simpa only [representation_apply] using hv g
  calc
    B.basis.coord (g • i) v =
        B.basis.coord (g • i) (g • v) := by
          rw [hvg]
    _ = B.basis.coord i v :=
      B.coord_smul g i v

/-- A globally fixed basis index gives an invariant basis vector. -/
def fixedBasisVector
    (i : MulAction.fixedPoints P ι) :
    invariants B.representation :=
  ⟨B.basis i, fun g => by
    change g • B.basis i = B.basis i
    rw [B.smul_basis, i.property g]⟩

omit [Finite ι] in
@[simp]
theorem fixedBasisVector_coe
    (i : MulAction.fixedPoints P ι) :
    (B.fixedBasisVector i : V) = B.basis i :=
  rfl

end PermutationModuleBasis
end Representation
