/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.LayerLocalSubgroup

/-!
# Coordinate products mapping onto layer-local subgroups

The subgroup `piLocalSubgroup M` is canonically the indexed product of the
coordinate subgroup carriers `M i`.  Using this equivalence, component
multiplication restricts to a surjective homomorphism

`(∀ K, M K) →* layerLocalSubgroup G M`.

Its kernel is the preimage of the ambient layer multiplication kernel; no
equality between subgroups of different ambient products is asserted.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

variable {ι : Type u}
variable {A : ι → Type v} [∀ i, Group (A i)]

/-- The indexed product of subgroup carriers is canonically isomorphic to
the coordinatewise product subgroup. -/
def piLocalSubgroupMulEquiv
    (M : ∀ i, Subgroup (A i)) :
    (∀ i, M i) ≃* piLocalSubgroup M where
  toFun x :=
    ⟨fun i ↦ (x i : A i),
      (mem_piLocalSubgroup M _).2 fun i ↦ (x i).property⟩
  invFun x :=
    fun i ↦
      ⟨x.1 i, (mem_piLocalSubgroup M x.1).1 x.2 i⟩
  left_inv x := by
    funext i
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    rfl
  map_mul' x y := by
    apply Subtype.ext
    funext i
    rfl

@[simp]
theorem piLocalSubgroupMulEquiv_apply_coe
    (M : ∀ i, Subgroup (A i))
    (x : ∀ i, M i) :
    ((piLocalSubgroupMulEquiv M x :
        piLocalSubgroup M) : ∀ i, A i) =
      fun i ↦ (x i : A i) :=
  rfl

@[simp]
theorem piLocalSubgroupMulEquiv_symm_apply
    (M : ∀ i, Subgroup (A i))
    (x : piLocalSubgroup M) (i : ι) :
    ((piLocalSubgroupMulEquiv M).symm x i : A i) =
      x.1 i :=
  rfl

/-- Coordinatewise inclusion of the local subgroup carriers into the
product of their ambient groups. -/
def piLocalSubgroupInclusion
    (M : ∀ i, Subgroup (A i)) :
    (∀ i, M i) →* ∀ i, A i :=
  (piLocalSubgroup M).subtype.comp
    (piLocalSubgroupMulEquiv M).toMonoidHom

@[simp]
theorem piLocalSubgroupInclusion_apply
    (M : ∀ i, Subgroup (A i))
    (x : ∀ i, M i) :
    piLocalSubgroupInclusion M x =
      fun i ↦ (x i : A i) :=
  rfl

variable (G : Type u) [Group G] [Finite G]
variable (M : ∀ K : ComponentIndex G, Subgroup K.1)

/-- Component multiplication restricted to the chosen coordinate local
subgroups and corestricted to its exact image. -/
def layerLocalProductHom :
    (∀ K : ComponentIndex G, M K) →*
      layerLocalSubgroup G M := by
  let raw :
      (∀ K : ComponentIndex G, M K) →* layer G :=
    (layerProductHom G).comp
      (piLocalSubgroupInclusion M)
  exact raw.codRestrict (layerLocalSubgroup G M) fun x ↦ by
    refine ⟨piLocalSubgroupInclusion M x, ?_, rfl⟩
    exact
      (piLocalSubgroupMulEquiv M x).property

@[simp]
theorem layerLocalProductHom_apply_coe
    (x : ∀ K : ComponentIndex G, M K) :
    ((layerLocalProductHom G M x :
        layerLocalSubgroup G M) : layer G) =
      layerProductHom G (fun K ↦ (x K : K.1)) :=
  rfl

/-- The restricted component product is surjective onto the image-defined
layer-local subgroup. -/
theorem layerLocalProductHom_surjective :
    Function.Surjective (layerLocalProductHom G M) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.property
  let xM : piLocalSubgroup M := ⟨x, hx⟩
  refine ⟨(piLocalSubgroupMulEquiv M).symm xM, ?_⟩
  apply Subtype.ext
  change layerProductHom G x = y.1
  exact hxy

/-- Membership in the restricted kernel is exactly membership of the
coordinatewise inclusion in the ambient layer multiplication kernel. -/
@[simp]
theorem mem_layerLocalProductHom_ker_iff
    (x : ∀ K : ComponentIndex G, M K) :
    x ∈ (layerLocalProductHom G M).ker ↔
      piLocalSubgroupInclusion M x ∈
        (layerProductHom G).ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- The restricted kernel is the preimage, not an untyped equality, of
the ambient layer multiplication kernel. -/
theorem layerLocalProductHom_ker :
    (layerLocalProductHom G M).ker =
      (layerProductHom G).ker.comap
        (piLocalSubgroupInclusion M) := by
  ext x
  exact mem_layerLocalProductHom_ker_iff G M x

end GroupTheory
end McKayConjecture
