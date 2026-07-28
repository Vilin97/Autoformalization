/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.LayerCentralProduct

/-!
# Coordinate residuals in the layer central product

After removing one coordinate from the product of component elements, the
remaining ambient element centralizes that component.  This is the precise
replacement for falsely treating the layer as a direct product.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

variable {G : Type} [Group G] [Finite G]

/-- The family obtained by replacing one component coordinate by `1`. -/
def omitLayerCoordinate
    (x : ∀ K : ComponentIndex G, K.1)
    (K : ComponentIndex G) :
    ∀ J : ComponentIndex G, J.1 := by
  classical
  exact Function.update x K 1

@[simp]
theorem omitLayerCoordinate_same
    (x : ∀ K : ComponentIndex G, K.1)
    (K : ComponentIndex G) :
    omitLayerCoordinate x K K = 1 := by
  simp [omitLayerCoordinate]

@[simp]
theorem omitLayerCoordinate_ne
    (x : ∀ K : ComponentIndex G, K.1)
    {J K : ComponentIndex G} (hJK : J ≠ K) :
    omitLayerCoordinate x K J = x J := by
  simp [omitLayerCoordinate, hJK]

/-- Splitting off one coordinate before component multiplication. -/
theorem layerProductHomToAmbient_eq_coordinate_mul_omit
    (x : ∀ K : ComponentIndex G, K.1)
    (K : ComponentIndex G) :
    layerProductHomToAmbient G x =
      (x K : G) *
        layerProductHomToAmbient G (omitLayerCoordinate x K) := by
  classical
  have hfamily :
      x =
        Pi.mulSingle K (x K) *
          omitLayerCoordinate x K := by
    funext J
    by_cases hJK : J = K
    · subst J
      simp
    · simp [omitLayerCoordinate, hJK]
  calc
    layerProductHomToAmbient G x =
        layerProductHomToAmbient G
          (Pi.mulSingle K (x K) *
            omitLayerCoordinate x K) :=
      congrArg (layerProductHomToAmbient G) hfamily
    _ =
        layerProductHomToAmbient G (Pi.mulSingle K (x K)) *
          layerProductHomToAmbient G
            (omitLayerCoordinate x K) := by
      rw [map_mul]
    _ = (x K : G) *
          layerProductHomToAmbient G
            (omitLayerCoordinate x K) := by
      rw [layerProductHomToAmbient]
      simp

/-- The product with one coordinate omitted centralizes that component. -/
theorem layerProductHomToAmbient_omit_mem_centralizer
    (x : ∀ K : ComponentIndex G, K.1)
    (K : ComponentIndex G) :
    layerProductHomToAmbient G (omitLayerCoordinate x K) ∈
      Subgroup.centralizer (K.1 : Set G) := by
  classical
  letI : Fintype (ComponentIndex G) :=
    Fintype.ofFinite _
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let yK : K.1 := ⟨y, hy⟩
  have hcommute :
      Commute (yK : G)
        (layerProductHomToAmbient G
          (omitLayerCoordinate x K)) := by
    rw [layerProductHomToAmbient,
      Subgroup.noncommPiCoprod_apply]
    apply Finset.noncommProd_induction
    · intro a b ha hb
      exact ha.mul_right hb
    · exact Commute.one_right _
    · intro J _
      by_cases hJK : J = K
      · subst J
        simp
      · exact
          components_pairwise_commute_elements
            (show K ≠ J from Ne.symm hJK)
            (yK : G)
            (omitLayerCoordinate x K J : G)
            yK.2 (omitLayerCoordinate x K J).2
  exact hcommute.eq

/-- Removing the selected coordinate from the full product leaves exactly
a centralizer residual. -/
theorem layerProduct_coordinateResidual_mem_centralizer
    (x : ∀ K : ComponentIndex G, K.1)
    (K : ComponentIndex G) :
    layerProductHomToAmbient G x * (x K : G)⁻¹ ∈
      Subgroup.centralizer (K.1 : Set G) := by
  let r :=
    layerProductHomToAmbient G (omitLayerCoordinate x K)
  have hr :
      r ∈ Subgroup.centralizer (K.1 : Set G) :=
    layerProductHomToAmbient_omit_mem_centralizer x K
  have hcomm :
      Commute (x K : G) r := by
    rw [Subgroup.mem_centralizer_iff] at hr
    exact hr (x K : G) (x K).2
  have hproduct :=
    layerProductHomToAmbient_eq_coordinate_mul_omit x K
  rw [hproduct, hcomm.eq]
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hr

/-- On the selected component, conjugation by the full component product is
exactly conjugation by its selected coordinate. -/
theorem layerProductHomToAmbient_conjugate_component
    (x : ∀ K : ComponentIndex G, K.1)
    (K : ComponentIndex G)
    (y : K.1) :
    layerProductHomToAmbient G x * (y : G) *
          (layerProductHomToAmbient G x)⁻¹ =
      (x K : G) * (y : G) * (x K : G)⁻¹ := by
  let r :=
    layerProductHomToAmbient G (omitLayerCoordinate x K)
  have hr :
      r ∈ Subgroup.centralizer (K.1 : Set G) :=
    layerProductHomToAmbient_omit_mem_centralizer x K
  have hry : r * (y : G) = (y : G) * r :=
    (Subgroup.mem_centralizer_iff.mp hr (y : G) y.2).symm
  have hrconj : r * (y : G) * r⁻¹ = (y : G) := by
    rw [hry]
    simp
  rw [layerProductHomToAmbient_eq_coordinate_mul_omit x K]
  calc
    ((x K : G) * r) * (y : G) * ((x K : G) * r)⁻¹ =
        (x K : G) * (r * (y : G) * r⁻¹) * (x K : G)⁻¹ := by
      group
    _ = (x K : G) * (y : G) * (x K : G)⁻¹ := by
      rw [hrconj]

/-- The inverse-conjugation form of
`layerProductHomToAmbient_conjugate_component`. -/
theorem layerProductHomToAmbient_inv_conjugate_component
    (x : ∀ K : ComponentIndex G, K.1)
    (K : ComponentIndex G)
    (y : K.1) :
    (layerProductHomToAmbient G x)⁻¹ * (y : G) *
          layerProductHomToAmbient G x =
      (x K : G)⁻¹ * (y : G) * (x K : G) := by
  let r :=
    layerProductHomToAmbient G (omitLayerCoordinate x K)
  have hr :
      r ∈ Subgroup.centralizer (K.1 : Set G) :=
    layerProductHomToAmbient_omit_mem_centralizer x K
  let z : K.1 := (x K)⁻¹ * y * x K
  have hzr : (z : G) * r = r * (z : G) :=
    Subgroup.mem_centralizer_iff.mp hr (z : G) z.2
  have hrconj : r⁻¹ * (z : G) * r = (z : G) := by
    calc
      r⁻¹ * (z : G) * r = r⁻¹ * ((z : G) * r) := by
        rw [mul_assoc]
      _ = r⁻¹ * (r * (z : G)) := by rw [hzr]
      _ = (z : G) := by simp
  rw [layerProductHomToAmbient_eq_coordinate_mul_omit x K]
  calc
    ((x K : G) * r)⁻¹ * (y : G) * ((x K : G) * r) =
        r⁻¹ * ((x K : G)⁻¹ * (y : G) * (x K : G)) * r := by
      group
    _ = r⁻¹ * (z : G) * r := by rfl
    _ = (z : G) := hrconj
    _ = (x K : G)⁻¹ * (y : G) * (x K : G) := by rfl

/-- Conjugating one component product by another acts on a selected
component through the corresponding coordinatewise conjugate. -/
theorem layerProductHomToAmbient_conjugateProduct_component
    (x y : ∀ K : ComponentIndex G, K.1)
    (K : ComponentIndex G)
    (z : K.1) :
    ((layerProductHomToAmbient G y)⁻¹ *
          layerProductHomToAmbient G x *
          layerProductHomToAmbient G y) *
          (z : G) *
          ((layerProductHomToAmbient G y)⁻¹ *
            layerProductHomToAmbient G x *
            layerProductHomToAmbient G y)⁻¹ =
      ((y K : G)⁻¹ * (x K : G) * (y K : G)) *
          (z : G) *
          ((y K : G)⁻¹ * (x K : G) * (y K : G))⁻¹ := by
  let z₁ : K.1 := y K * z * (y K)⁻¹
  let z₂ : K.1 := x K * z₁ * (x K)⁻¹
  have hy :
      layerProductHomToAmbient G y * (z : G) *
            (layerProductHomToAmbient G y)⁻¹ =
        (z₁ : G) := by
    change
      layerProductHomToAmbient G y * (z : G) *
            (layerProductHomToAmbient G y)⁻¹ =
        (y K : G) * (z : G) * (y K : G)⁻¹
    exact layerProductHomToAmbient_conjugate_component y K z
  have hx :
      layerProductHomToAmbient G x * (z₁ : G) *
            (layerProductHomToAmbient G x)⁻¹ =
        (z₂ : G) := by
    change
      layerProductHomToAmbient G x * (z₁ : G) *
            (layerProductHomToAmbient G x)⁻¹ =
        (x K : G) * (z₁ : G) * (x K : G)⁻¹
    exact layerProductHomToAmbient_conjugate_component x K z₁
  have hyInv :
      (layerProductHomToAmbient G y)⁻¹ * (z₂ : G) *
            layerProductHomToAmbient G y =
        (y K : G)⁻¹ * (z₂ : G) * (y K : G) :=
    layerProductHomToAmbient_inv_conjugate_component y K z₂
  calc
    ((layerProductHomToAmbient G y)⁻¹ *
          layerProductHomToAmbient G x *
          layerProductHomToAmbient G y) *
          (z : G) *
          ((layerProductHomToAmbient G y)⁻¹ *
            layerProductHomToAmbient G x *
            layerProductHomToAmbient G y)⁻¹ =
        (layerProductHomToAmbient G y)⁻¹ *
          (layerProductHomToAmbient G x *
            (layerProductHomToAmbient G y * (z : G) *
              (layerProductHomToAmbient G y)⁻¹) *
            (layerProductHomToAmbient G x)⁻¹) *
          layerProductHomToAmbient G y := by
      group
    _ =
        (layerProductHomToAmbient G y)⁻¹ *
          (layerProductHomToAmbient G x * (z₁ : G) *
            (layerProductHomToAmbient G x)⁻¹) *
          layerProductHomToAmbient G y := by rw [hy]
    _ =
        (layerProductHomToAmbient G y)⁻¹ * (z₂ : G) *
          layerProductHomToAmbient G y := by rw [hx]
    _ = (y K : G)⁻¹ * (z₂ : G) * (y K : G) := hyInv
    _ =
        ((y K : G)⁻¹ * (x K : G) * (y K : G)) *
          (z : G) *
          ((y K : G)⁻¹ * (x K : G) * (y K : G))⁻¹ := by
      simp only [z₁, z₂, Subgroup.coe_mul, Subgroup.coe_inv]
      group

end GroupTheory
end McKayConjecture
