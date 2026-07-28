/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.QuotientGroup.Basic
import McKayConjecture.GroupTheory.GeneralizedFittingAction

/-!
# The layer as a central product of its components

For a finite group `G`, multiplication of all components gives a surjective
homomorphism from their external direct product onto the layer `E(G)`.
Its kernel is central, so `E(G)` is the corresponding central-product
quotient.  No injectivity of the multiplication map is asserted.
-/

noncomputable section

open scoped commutatorElement

universe u v

namespace McKayConjecture.GroupTheory

variable {G : Type u} [Group G]

/-- The kernel of the multiplication map from a finite pairwise commuting
family of subgroups is central in the external direct product. -/
theorem ker_noncommPiCoprod_le_center
    {ι : Type v} [Fintype ι] {H : ι → Subgroup G}
    (hcomm : Pairwise fun i j : ι =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) :
    (Subgroup.noncommPiCoprod hcomm).ker ≤
      Subgroup.center (∀ i, H i) := by
  classical
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  funext i
  have hsingle :
      ⁅x, Pi.mulSingle (M := fun i => H i) i (y i)⁆ =
        Pi.mulSingle (M := fun i => H i) i ⁅x i, y i⁆ := by
    funext j
    change
      ⁅x j, (Pi.mulSingle (M := fun i => H i) i (y i)) j⁆ =
        (Pi.mulSingle (M := fun i => H i) i ⁅x i, y i⁆) j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  have hmap :
      Subgroup.noncommPiCoprod hcomm
          ⁅x, Pi.mulSingle (M := fun i => H i) i (y i)⁆ = 1 := by
    rw [map_commutatorElement, MonoidHom.mem_ker.mp hx]
    simp
  rw [hsingle, Subgroup.noncommPiCoprod_mulSingle] at hmap
  have hi : ⁅x i, y i⁆ = 1 := by
    apply Subtype.ext
    exact hmap
  exact (commutatorElement_eq_one_iff_commute.mp hi).eq.symm

/-- A finite group has only finitely many components. -/
instance componentIndex_finite (G : Type u) [Group G] [Finite G] :
    Finite (ComponentIndex G) := by
  letI : Finite (Set G) := inferInstance
  letI : Finite (Subgroup G) :=
    Finite.of_injective
      (fun H : Subgroup G => (H : Set G))
      SetLike.coe_injective
  infer_instance

/-- Distinct component subgroups commute elementwise. -/
theorem components_pairwise_commute_elements
    [Finite G] :
    Pairwise fun C D : ComponentIndex G =>
      ∀ x y : G, x ∈ C.1 → y ∈ D.1 → Commute x y := by
  intro C D hCD x y hx hy
  have hsubgroup_ne : C.1 ≠ D.1 := by
    intro h
    exact hCD (Subtype.ext h)
  have hbot :
      ⁅C.1, D.1⁆ = (⊥ : Subgroup G) :=
    (show IsComponent C.1 from C.2).commutator_eq_bot_of_ne
      (show IsComponent D.1 from D.2) hsubgroup_ne
  have hmem :
      ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact Subgroup.commutator_mem_commutator hx hy
  exact commutatorElement_eq_one_iff_commute.mp
    (Subgroup.mem_bot.mp hmem)

/-- Multiplication of all components, before restricting its codomain to
the layer. -/
def layerProductHomToAmbient
    (G : Type u) [Group G] [Finite G] :
    (∀ K : ComponentIndex G, K.1) →* G := by
  classical
  letI := Fintype.ofFinite (ComponentIndex G)
  exact Subgroup.noncommPiCoprod
    (components_pairwise_commute_elements (G := G))

/-- Before codomain restriction, the range of component multiplication is
exactly the layer. -/
theorem layerProductHomToAmbient_range
    (G : Type u) [Group G] [Finite G] :
    (layerProductHomToAmbient G).range = layer G := by
  classical
  letI := Fintype.ofFinite (ComponentIndex G)
  rw [layerProductHomToAmbient,
    Subgroup.noncommPiCoprod_range,
    ← layer_eq_iSup_components]

/-- Multiplication of all components as a homomorphism onto the layer. -/
def layerProductHom
    (G : Type u) [Group G] [Finite G] :
    (∀ K : ComponentIndex G, K.1) →* layer G :=
  (layerProductHomToAmbient G).codRestrict
    (layer G) fun x => by
      rw [← layerProductHomToAmbient_range G]
      exact ⟨x, rfl⟩

/-- Component multiplication is surjective onto the layer. -/
theorem layerProductHom_surjective
    (G : Type u) [Group G] [Finite G] :
    Function.Surjective (layerProductHom G) := by
  intro z
  have hz :
      (z : G) ∈ (layerProductHomToAmbient G).range := by
    rw [layerProductHomToAmbient_range G]
    exact z.2
  obtain ⟨x, hx⟩ := hz
  exact ⟨x, Subtype.ext hx⟩

/-- The relations among the components in their multiplication map are
central in the external direct product. -/
theorem layerProductHom_ker_le_center
    (G : Type u) [Group G] [Finite G] :
    (layerProductHom G).ker ≤
      Subgroup.center (∀ K : ComponentIndex G, K.1) := by
  classical
  letI := Fintype.ofFinite (ComponentIndex G)
  rw [layerProductHom, MonoidHom.ker_codRestrict]
  exact ker_noncommPiCoprod_le_center
    (components_pairwise_commute_elements (G := G))

/-- The layer is the quotient of the external direct product of its
components by the central kernel of component multiplication. -/
def layerProductQuotientEquiv
    (G : Type u) [Group G] [Finite G] :
    ((∀ K : ComponentIndex G, K.1) ⧸
        (layerProductHom G).ker) ≃* layer G :=
  QuotientGroup.quotientKerEquivOfSurjective
    (layerProductHom G)
    (layerProductHom_surjective G)

end McKayConjecture.GroupTheory
