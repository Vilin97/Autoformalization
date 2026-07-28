/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Relative syzygy modules

Let `Q` be a subgroup of a group `P` and let `k` be a commutative
semiring.  The
permutation module on the left cosets `P ⧸ Q` is the finitely supported
function module

`(P ⧸ Q) →₀ k`.

Its augmentation map sends a finitely supported function to the sum of
its coefficients.  The relative syzygy module `Ω_{P/Q}(k)` is the
kernel of this map.  This file constructs the natural `P`-action on the
permutation module, proves that augmentation is invariant, and restricts
the action to the relative syzygy module.
-/

noncomputable section

namespace Representation

variable (k P : Type*) [Group P]

section Basic

variable [CommSemiring k]

/-- The permutation module over `k` on the left cosets `P ⧸ Q`. -/
abbrev CosetPermutationModule (Q : Subgroup P) :=
  MonoidAlgebra k (P ⧸ Q)

/-- The natural permutation representation of `P` on the left cosets
`P ⧸ Q`. -/
def cosetPermutationRepresentation (Q : Subgroup P) :
    Representation k P (CosetPermutationModule k P Q) :=
  Representation.ofMulAction k P (P ⧸ Q)

/-- The augmentation map on the permutation module: the sum of all
coefficients. -/
def cosetAugmentation (Q : Subgroup P) :
    CosetPermutationModule k P Q →ₗ[k] k :=
  (Finsupp.lsum k fun _ => LinearMap.id).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp]
theorem cosetAugmentation_apply
    (Q : Subgroup P)
    (v : CosetPermutationModule k P Q) :
    cosetAugmentation k P Q v =
      v.coeff.sum fun _ a => a := by
  rfl

@[simp]
theorem cosetAugmentation_single
    (Q : Subgroup P)
    (x : P ⧸ Q)
    (a : k) :
    cosetAugmentation k P Q (MonoidAlgebra.single x a) = a := by
  simp [cosetAugmentation]

/-- Augmentation is invariant under the natural permutation action. -/
theorem cosetAugmentation_comp_action
    (Q : Subgroup P)
    (g : P) :
    cosetAugmentation k P Q ∘ₗ
      cosetPermutationRepresentation k P Q g =
      cosetAugmentation k P Q := by
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  simp [cosetPermutationRepresentation]

@[simp]
theorem cosetAugmentation_action
    (Q : Subgroup P)
    (g : P)
    (v : CosetPermutationModule k P Q) :
    cosetAugmentation k P Q
        (cosetPermutationRepresentation k P Q g v) =
      cosetAugmentation k P Q v :=
  LinearMap.congr_fun (cosetAugmentation_comp_action k P Q g) v

/-- The relative syzygy module `Ω_{P/Q}(k)`, defined as the augmentation
kernel of the permutation module on `P ⧸ Q`. -/
def relativeSyzygy (Q : Subgroup P) :
    Submodule k (CosetPermutationModule k P Q) :=
  LinearMap.ker (cosetAugmentation k P Q)

@[simp]
theorem mem_relativeSyzygy
    (Q : Subgroup P)
    {v : CosetPermutationModule k P Q} :
    v ∈ relativeSyzygy k P Q ↔
      cosetAugmentation k P Q v = 0 :=
  LinearMap.mem_ker

/-- The augmentation kernel is invariant under the natural `P`-action. -/
theorem action_mem_relativeSyzygy
    (Q : Subgroup P)
    (g : P)
    {v : CosetPermutationModule k P Q}
    (hv : v ∈ relativeSyzygy k P Q) :
    cosetPermutationRepresentation k P Q g v ∈
      relativeSyzygy k P Q := by
  rw [mem_relativeSyzygy, cosetAugmentation_action]
  exact (mem_relativeSyzygy k P Q).mp hv

/-- Submodule-form invariance of the relative syzygy, suitable for
`Representation.subrepresentation`. -/
theorem relativeSyzygy_le_comap
    (Q : Subgroup P)
    (g : P) :
    relativeSyzygy k P Q ≤
      (relativeSyzygy k P Q).comap
        (cosetPermutationRepresentation k P Q g) := by
  intro v hv
  exact action_mem_relativeSyzygy k P Q g hv

/-- The natural `P`-representation on the relative syzygy module. -/
def relativeSyzygyRepresentation (Q : Subgroup P) :
    Representation k P (relativeSyzygy k P Q) :=
  (cosetPermutationRepresentation k P Q).subrepresentation
    (relativeSyzygy k P Q)
    (relativeSyzygy_le_comap k P Q)

@[simp]
theorem relativeSyzygyRepresentation_apply_coe
    (Q : Subgroup P)
    (g : P)
    (v : relativeSyzygy k P Q) :
    ((relativeSyzygyRepresentation k P Q g v :
        relativeSyzygy k P Q) :
      CosetPermutationModule k P Q) =
      cosetPermutationRepresentation k P Q g
        (v : CosetPermutationModule k P Q) :=
  rfl

/-- Augmentation is onto: a scalar is the augmentation of the
corresponding multiple of any coset basis vector. -/
theorem cosetAugmentation_surjective
    (Q : Subgroup P) :
    Function.Surjective (cosetAugmentation k P Q) := by
  intro a
  refine
    ⟨MonoidAlgebra.single
      (QuotientGroup.mk (1 : P)) a, ?_⟩
  simp

end Basic

section Finite

variable [Field k] [Finite P]

/-- The relative syzygy of a finite group is finite-dimensional. -/
instance relativeSyzygy_finiteDimensional
    (Q : Subgroup P) :
    FiniteDimensional k (relativeSyzygy k P Q) := by
  infer_instance

end Finite

end Representation
