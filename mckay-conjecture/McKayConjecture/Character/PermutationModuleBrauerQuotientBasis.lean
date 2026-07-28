/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleBrauerTrace
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The Brauer quotient basis of a permutation module

For a finite `p`-group acting on a permutation module over a field of
characteristic `p`, the Brauer quotient has the images of the globally
fixed basis vectors as a basis.
-/

noncomputable section

open scoped BigOperators

namespace Representation
namespace PermutationModuleBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V ι : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis (k := k) (P := P) (V := V) (ι := ι))

local notation "Fix" =>
  MulAction.fixedPoints P ι

noncomputable local instance brauerQuotientBasisGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

noncomputable local instance brauerQuotientBasisIndexFintype :
    Fintype ι :=
  Fintype.ofFinite ι

noncomputable local instance fixedIndexFintype :
    Fintype Fix :=
  Fintype.ofFinite Fix

noncomputable local instance fixedIndexDecidableEq :
    DecidableEq Fix :=
  Classical.decEq Fix

/-- Coordinates at the globally fixed basis indices. -/
def fixedCoordinates :
    invariants B.representation →ₗ[k] (Fix → k) where
  toFun x i := B.basis.coord i (x : V)
  map_add' x y := by
    funext i
    exact map_add (B.basis.coord i) (x : V) (y : V)
  map_smul' a x := by
    funext i
    exact map_smul (B.basis.coord i) a (x : V)

omit [Finite P] [Finite ι] in
@[simp]
theorem fixedCoordinates_apply
    (x : invariants B.representation)
    (i : Fix) :
    B.fixedCoordinates x i =
      B.basis.coord i (x : V) :=
  rfl

omit [Finite P] in
/-- Every family of coefficients at the fixed indices is realized by
a linear combination of the corresponding basis vectors. -/
theorem fixedCoordinates_surjective :
    Function.Surjective B.fixedCoordinates := by
  intro f
  refine
    ⟨∑ i : Fix, f i • B.fixedBasisVector i, ?_⟩
  funext j
  change
    B.basis.coord j
        ((↑(∑ i : Fix,
          f i • B.fixedBasisVector i) : V)) =
      f j
  simp only [map_sum, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, map_smul,
    B.fixedBasisVector_coe,
    Module.Basis.coord_apply]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro i hi
    have hval : (i : ι) ≠ (j : ι) := by
      intro h
      apply hi
      exact Subtype.ext h
    simp [hval]

/-- The kernel of the fixed-coordinate map is the Brauer trace
submodule. -/
theorem ker_fixedCoordinates
    (hP : IsPGroup p P) :
    LinearMap.ker B.fixedCoordinates =
      brauerTraceSubmodule B.representation := by
  apply le_antisymm
  · intro y hy
    rw [B.brauerTraceSubmodule_eq_span_nonfixedOrbitSum hP]
    rw [← B.sum_orbitSum_eq y]
    apply Submodule.sum_mem
    intro ω _
    by_cases hω :
        ω.out ∈ MulAction.fixedPoints P ι
    · have hfun :
          B.fixedCoordinates y = 0 :=
        LinearMap.mem_ker.mp hy
      have hzero :
          B.basis.coord ω.out (y : V) = 0 := by
        simpa only [fixedCoordinates_apply,
          Pi.zero_apply] using
          congrFun hfun ⟨ω.out, hω⟩
      rw [hzero, zero_smul]
      exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨⟨ω, hω⟩, rfl⟩
  · intro y hy
    rw [LinearMap.mem_ker]
    funext i
    exact
      B.coord_fixed_eq_zero_of_mem_brauerTraceSubmodule
        hP i y hy

/-- The Brauer quotient is canonically identified with the space of
functions on the globally fixed basis indices. -/
def brauerQuotientEquivFixedCoordinates
    (hP : IsPGroup p P) :
    BrauerQuotient B.representation ≃ₗ[k] (Fix → k) :=
  (Submodule.quotEquivOfEq
      (brauerTraceSubmodule B.representation)
      (LinearMap.ker B.fixedCoordinates)
      (B.ker_fixedCoordinates hP).symm).trans
    (B.fixedCoordinates.quotKerEquivOfSurjective
      B.fixedCoordinates_surjective)

/-- The quotient equivalence sends the class of an invariant vector to
its fixed-index coordinates. -/
@[simp]
theorem brauerQuotientEquivFixedCoordinates_brauerProjection
    (hP : IsPGroup p P)
    (x : invariants B.representation) :
    B.brauerQuotientEquivFixedCoordinates hP
        (brauerProjection B.representation x) =
      B.fixedCoordinates x := by
  simp only [brauerQuotientEquivFixedCoordinates,
    brauerProjection, Submodule.mkQ_apply,
    LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Basis of the Brauer quotient indexed by the globally fixed basis
indices. -/
def brauerQuotientFixedBasis
    (hP : IsPGroup p P) :
    Module.Basis Fix k (BrauerQuotient B.representation) :=
  Module.Basis.ofEquivFun
    (B.brauerQuotientEquivFixedCoordinates hP)

/-- Each vector in the Brauer-quotient basis is the image of the
corresponding globally fixed basis vector. -/
@[simp]
theorem brauerQuotientFixedBasis_apply
    (hP : IsPGroup p P)
    (i : Fix) :
    B.brauerQuotientFixedBasis hP i =
      brauerProjection B.representation
        (B.fixedBasisVector i) := by
  apply
    (B.brauerQuotientEquivFixedCoordinates hP).injective
  funext j
  rw [← Module.Basis.ofEquivFun_repr_apply
    (B.brauerQuotientEquivFixedCoordinates hP)]
  simp only [brauerQuotientFixedBasis,
    Module.Basis.repr_self_apply,
    B.brauerQuotientEquivFixedCoordinates_brauerProjection,
    fixedCoordinates_apply, B.fixedBasisVector_coe,
    Module.Basis.coord_apply,
    Module.Basis.repr_self_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : (i : ι) ≠ (j : ι) := by
      intro h
      apply hij
      exact Subtype.ext h
    simp [hij, hval]

/-- Dimension form of the permutation-module Brauer quotient theorem. -/
theorem finrank_brauerQuotient_eq_card_fixedPoints
    (hP : IsPGroup p P) :
    Module.finrank k (BrauerQuotient B.representation) =
      Fintype.card Fix :=
  Module.finrank_eq_card_basis
    (B.brauerQuotientFixedBasis hP)

end PermutationModuleBasis
end Representation
