/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Endopermutation.RelativeSyzygy
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Basic structure of relative syzygy modules

This file records elementary structural properties of the relative
syzygy module:

* its dimension is one less than the number of cosets;
* the relative syzygy for the top subgroup vanishes;
* equivalences of indexing sets transport augmentation kernels;
* the bottom-subgroup construction agrees with the ordinary
  group-algebra augmentation ideal.
-/

noncomputable section

namespace Representation

section AugmentationNaturality

variable (k : Type*) [CommSemiring k]

/-- Augmentation of the free `k`-module on an arbitrary indexing type. -/
def permutationAugmentation (X : Type*) :
    MonoidAlgebra k X →ₗ[k] k :=
  (Finsupp.lsum k fun _ => LinearMap.id).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp]
theorem permutationAugmentation_apply
    (X : Type*)
    (v : MonoidAlgebra k X) :
    permutationAugmentation k X v =
      v.coeff.sum fun _ a => a :=
  rfl

@[simp]
theorem permutationAugmentation_single
    (X : Type*)
    (x : X)
    (a : k) :
    permutationAugmentation k X
        (MonoidAlgebra.single x a) = a := by
  simp [permutationAugmentation]

variable {X Y : Type*}

/-- Relabelling a permutation basis preserves augmentation. -/
theorem permutationAugmentation_mapDomainLinearEquiv
    (e : X ≃ Y)
    (v : MonoidAlgebra k X) :
    permutationAugmentation k Y
        (MonoidAlgebra.mapDomainLinearEquiv k k e v) =
      permutationAugmentation k X v := by
  have h :
      permutationAugmentation k Y ∘ₗ
          (MonoidAlgebra.mapDomainLinearEquiv k k e).toLinearMap =
        permutationAugmentation k X := by
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro a
    simp
  exact LinearMap.congr_fun h v

/-- The augmentation kernel of the free `k`-module on `X`. -/
def augmentationKernel (X : Type*) :
    Submodule k (MonoidAlgebra k X) :=
  LinearMap.ker (permutationAugmentation k X)

@[simp]
theorem mem_augmentationKernel
    (X : Type*)
    {v : MonoidAlgebra k X} :
    v ∈ augmentationKernel k X ↔
      permutationAugmentation k X v = 0 :=
  LinearMap.mem_ker

/-- An equivalence of indexing sets induces a linear equivalence of
augmentation kernels. -/
def augmentationKernelEquiv
    (e : X ≃ Y) :
    augmentationKernel k X ≃ₗ[k] augmentationKernel k Y where
  toFun v :=
    ⟨MonoidAlgebra.mapDomainLinearEquiv k k e v,
      by
        rw [mem_augmentationKernel,
          permutationAugmentation_mapDomainLinearEquiv]
        exact (mem_augmentationKernel k X).mp v.property⟩
  invFun v :=
    ⟨MonoidAlgebra.mapDomainLinearEquiv k k e.symm v,
      by
        rw [mem_augmentationKernel,
          permutationAugmentation_mapDomainLinearEquiv]
        exact (mem_augmentationKernel k Y).mp v.property⟩
  left_inv v := by
    apply Subtype.ext
    exact
      (MonoidAlgebra.mapDomainLinearEquiv k k e).left_inv v
  right_inv v := by
    apply Subtype.ext
    exact
      (MonoidAlgebra.mapDomainLinearEquiv k k e).right_inv v
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' _ _ := by
    apply Subtype.ext
    exact map_smul _ _ _

@[simp]
theorem augmentationKernelEquiv_apply_coe
    (e : X ≃ Y)
    (v : augmentationKernel k X) :
    ((augmentationKernelEquiv k e v :
        augmentationKernel k Y) :
      MonoidAlgebra k Y) =
      MonoidAlgebra.mapDomainLinearEquiv k k e
        (v : MonoidAlgebra k X) :=
  rfl

end AugmentationNaturality

section RelativeNaturality

variable (k : Type*) [CommSemiring k]
variable (P P' : Type*) [Group P] [Group P']
variable (Q : Subgroup P) (Q' : Subgroup P')

/-- The relative syzygy is the augmentation kernel on its coset set. -/
def relativeSyzygyEquivAugmentationKernel :
    relativeSyzygy k P Q ≃ₗ[k]
      augmentationKernel k (P ⧸ Q) :=
  LinearEquiv.refl k _

/-- An equivalence between two coset sets transports the corresponding
relative syzygy modules. -/
def relativeSyzygyEquivOfCosetEquiv
    (e : (P ⧸ Q) ≃ (P' ⧸ Q')) :
    relativeSyzygy k P Q ≃ₗ[k]
      relativeSyzygy k P' Q' :=
  relativeSyzygyEquivAugmentationKernel k P Q ≪≫ₗ
    augmentationKernelEquiv k e ≪≫ₗ
    (relativeSyzygyEquivAugmentationKernel k P' Q').symm

@[simp]
theorem relativeSyzygyEquivOfCosetEquiv_apply_coe
    (e : (P ⧸ Q) ≃ (P' ⧸ Q'))
    (v : relativeSyzygy k P Q) :
    ((relativeSyzygyEquivOfCosetEquiv
          k P P' Q Q' e v :
        relativeSyzygy k P' Q') :
      CosetPermutationModule k P' Q') =
      MonoidAlgebra.mapDomainLinearEquiv k k e
        (v : CosetPermutationModule k P Q) :=
  rfl

end RelativeNaturality

section Dimension

variable (k P : Type*) [Field k] [Group P] [Finite P]

noncomputable local instance cosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- The dimension of the relative syzygy plus one is the number of
left cosets. -/
theorem finrank_relativeSyzygy_add_one
    (Q : Subgroup P) :
    Module.finrank k (relativeSyzygy k P Q) + 1 =
      Nat.card (P ⧸ Q) := by
  have hrange :
      LinearMap.range (cosetAugmentation k P Q) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (cosetAugmentation_surjective k P Q)
  have hrank :=
    LinearMap.finrank_range_add_finrank_ker
      (cosetAugmentation k P Q)
  have hambient :
      Module.finrank k (CosetPermutationModule k P Q) =
        Nat.card (P ⧸ Q) := by
    calc
      Module.finrank k (CosetPermutationModule k P Q) =
          Module.finrank k ((P ⧸ Q) →₀ k) :=
        (MonoidAlgebra.coeffLinearEquiv
          (S := k) (M := P ⧸ Q) k).finrank_eq
      _ = Fintype.card (P ⧸ Q) :=
        Module.finrank_finsupp_self k
      _ = Nat.card (P ⧸ Q) :=
        Nat.card_eq_fintype_card.symm
  rw [hrange] at hrank
  rw [finrank_top, CommSemiring.finrank_self, hambient] at hrank
  have hrank' :
      1 + Module.finrank k (relativeSyzygy k P Q) =
        Nat.card (P ⧸ Q) := by
    change
      1 + Module.finrank k
          (LinearMap.ker (cosetAugmentation k P Q)) =
        Nat.card (P ⧸ Q)
    exact hrank
  rw [Nat.add_comm]
  exact hrank'

/-- Subtraction form of the relative-syzygy dimension formula. -/
theorem finrank_relativeSyzygy
    (Q : Subgroup P) :
    Module.finrank k (relativeSyzygy k P Q) =
      Nat.card (P ⧸ Q) - 1 :=
  Nat.eq_sub_of_add_eq
    (finrank_relativeSyzygy_add_one k P Q)

/-- Index form of the relative-syzygy dimension formula. -/
theorem finrank_relativeSyzygy_add_one_eq_index
    (Q : Subgroup P) :
    Module.finrank k (relativeSyzygy k P Q) + 1 =
      Q.index := by
  rw [finrank_relativeSyzygy_add_one,
    Q.index_eq_card]

end Dimension

section Top

variable (k P : Type*) [CommSemiring k] [Group P]

/-- Augmentation on the one-point coset space `P ⧸ ⊤` is injective. -/
theorem cosetAugmentation_top_injective :
    Function.Injective
      (cosetAugmentation k P (⊤ : Subgroup P)) := by
  let q₀ : P ⧸ (⊤ : Subgroup P) :=
    QuotientGroup.mk (1 : P)
  letI : Subsingleton (P ⧸ (⊤ : Subgroup P)) :=
    QuotientGroup.subsingleton_quotient_top
  letI : Unique (P ⧸ (⊤ : Subgroup P)) :=
    { default := q₀
      uniq := fun _ => Subsingleton.elim _ _ }
  intro v w hvw
  apply (MonoidAlgebra.coeffLinearEquiv k).injective
  apply Finsupp.ext
  intro x
  have hx : x = (default : P ⧸ (⊤ : Subgroup P)) :=
    Subsingleton.elim _ _
  subst x
  simpa [Finsupp.sum_unique] using hvw

/-- The relative syzygy for the top subgroup is the zero submodule. -/
theorem relativeSyzygy_top_eq_bot :
    relativeSyzygy k P (⊤ : Subgroup P) = ⊥ := by
  unfold relativeSyzygy
  exact
    LinearMap.ker_eq_bot_of_injective
      (cosetAugmentation_top_injective k P)

/-- The relative syzygy for the top subgroup is a subsingleton. -/
theorem relativeSyzygy_top_subsingleton :
    Subsingleton
      (relativeSyzygy k P (⊤ : Subgroup P)) := by
  rw [relativeSyzygy_top_eq_bot k P]
  infer_instance

end Top

section Bottom

variable (k P : Type*) [CommRing k] [Group P]

/-- The ordinary augmentation algebra homomorphism on the group
algebra `k[P]`. -/
def groupAlgebraAugmentation :
    MonoidAlgebra k P →ₐ[k] k :=
  MonoidAlgebra.lift k k P (1 : P →* k)

@[simp]
theorem groupAlgebraAugmentation_single
    (g : P)
    (a : k) :
    groupAlgebraAugmentation k P
        (MonoidAlgebra.single g a) = a := by
  simp [groupAlgebraAugmentation]

@[simp]
theorem groupAlgebraAugmentation_apply
    (v : MonoidAlgebra k P) :
    groupAlgebraAugmentation k P v =
      v.coeff.sum fun _ a => a := by
  simp [groupAlgebraAugmentation,
    MonoidAlgebra.lift_apply]

/-- The ordinary augmentation ideal of the group algebra. -/
def groupAlgebraAugmentationIdeal :
    Ideal (MonoidAlgebra k P) :=
  RingHom.ker (groupAlgebraAugmentation k P).toRingHom

/-- The ordinary augmentation ideal, regarded as a `k`-submodule of
the group algebra. -/
def groupAlgebraAugmentationSubmodule :
    Submodule k (MonoidAlgebra k P) :=
  (groupAlgebraAugmentationIdeal k P).restrictScalars k

@[simp]
theorem mem_groupAlgebraAugmentationSubmodule
    {v : MonoidAlgebra k P} :
    v ∈ groupAlgebraAugmentationSubmodule k P ↔
      groupAlgebraAugmentation k P v = 0 := by
  simp [groupAlgebraAugmentationSubmodule,
    groupAlgebraAugmentationIdeal]

/-- The free-module augmentation agrees with the usual algebra
augmentation on a group algebra. -/
theorem permutationAugmentation_eq_groupAlgebraAugmentation :
    permutationAugmentation k P =
      (groupAlgebraAugmentation k P).toLinearMap := by
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext
  intro a
  simp

/-- The generic augmentation kernel is the ordinary augmentation ideal,
viewed as a `k`-submodule. -/
theorem augmentationKernel_eq_groupAlgebraAugmentationSubmodule :
    augmentationKernel k P =
      groupAlgebraAugmentationSubmodule k P := by
  ext v
  rw [mem_augmentationKernel,
    mem_groupAlgebraAugmentationSubmodule]
  rw [LinearMap.congr_fun
    (permutationAugmentation_eq_groupAlgebraAugmentation k P) v]
  simp only [AlgHom.toLinearMap_apply]

/-- For `Q = ⊥`, the relative syzygy is the ordinary augmentation
ideal of `k[P]`. -/
def relativeSyzygyBotEquivGroupAlgebraAugmentation :
    relativeSyzygy k P (⊥ : Subgroup P) ≃ₗ[k]
      groupAlgebraAugmentationSubmodule k P :=
  relativeSyzygyEquivAugmentationKernel
      k P (⊥ : Subgroup P) ≪≫ₗ
    augmentationKernelEquiv k
      (QuotientGroup.quotientEquivSelf P) ≪≫ₗ
    LinearEquiv.ofEq
      (augmentationKernel k P)
      (groupAlgebraAugmentationSubmodule k P)
      (augmentationKernel_eq_groupAlgebraAugmentationSubmodule k P)

@[simp]
theorem relativeSyzygyBotEquivGroupAlgebraAugmentation_apply_coe
    (v : relativeSyzygy k P (⊥ : Subgroup P)) :
    ((relativeSyzygyBotEquivGroupAlgebraAugmentation
          k P v :
        groupAlgebraAugmentationSubmodule k P) :
      MonoidAlgebra k P) =
      MonoidAlgebra.mapDomainLinearEquiv k k
        (QuotientGroup.quotientEquivSelf P)
        (v : CosetPermutationModule
          k P (⊥ : Subgroup P)) :=
  rfl

end Bottom

end Representation
