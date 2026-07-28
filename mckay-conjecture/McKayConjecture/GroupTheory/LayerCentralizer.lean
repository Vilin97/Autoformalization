/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.GeneralizedFittingCentralizer
import McKayConjecture.GroupTheory.LayerIntermediateStructure

/-!
# The centralizer of the layer in the minimal-counterexample case

If `F(G) = Z(G)`, then centralizing the layer is the same as centralizing
`F*(G) = F(G)E(G)`.  Bender's self-centralizing theorem identifies the latter
centralizer with the ambient image of `Z(F*(G))`.  That image is a normal
nilpotent subgroup, hence lies in `F(G) = Z(G)`.

Consequently the centralizer of the layer lies in every layer intermediate:
the ambient center normalizes every chosen layer Sylow subgroup.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

open scoped IsMulCommutative

variable {G : Type u} [Group G] [Finite G]

/-- The ambient image of the center of the generalized Fitting subgroup is
normal. -/
instance map_center_generalizedFittingSubgroup_normal :
    ((Subgroup.center
        (generalizedFittingSubgroup G)).map
      (generalizedFittingSubgroup G).subtype).Normal :=
  inferInstance

omit [Finite G] in
/-- The ambient image of `Z(F*(G))` is nilpotent. -/
theorem map_center_generalizedFittingSubgroup_isNilpotent :
    Group.IsNilpotent
      ((Subgroup.center
          (generalizedFittingSubgroup G)).map
        (generalizedFittingSubgroup G).subtype) := by
  let e :
      Subgroup.center
          (generalizedFittingSubgroup G) ≃*
        (Subgroup.center
          (generalizedFittingSubgroup G)).map
            (generalizedFittingSubgroup G).subtype :=
    (Subgroup.center
      (generalizedFittingSubgroup G)).equivMapOfInjective
        (generalizedFittingSubgroup G).subtype
        Subtype.coe_injective
  exact Group.nilpotent_of_mulEquiv e

/-- The ambient image of `Z(F*(G))` lies in the Fitting subgroup. -/
theorem map_center_generalizedFittingSubgroup_le_fittingSubgroup :
    (Subgroup.center
        (generalizedFittingSubgroup G)).map
      (generalizedFittingSubgroup G).subtype ≤
        fittingSubgroup G :=
  normal_isNilpotent_le_fittingSubgroup
    ((Subgroup.center
      (generalizedFittingSubgroup G)).map
        (generalizedFittingSubgroup G).subtype)
    inferInstance
    map_center_generalizedFittingSubgroup_isNilpotent

omit [Finite G] in
/-- When `F(G) = Z(G)`, centralizing the layer is equivalent to
centralizing the generalized Fitting subgroup. -/
theorem centralizer_layer_eq_generalizedFittingCentralizer_of_eq_center
    (hF :
      fittingSubgroup G = Subgroup.center G) :
    Subgroup.centralizer (layer G : Set G) =
      generalizedFittingCentralizer G := by
  change
    Subgroup.centralizer (layer G : Set G) =
      Subgroup.centralizer
        (generalizedFittingSubgroup G : Set G)
  simp [centralizer_generalizedFittingSubgroup, hF]

/-- If `F(G) = Z(G)`, then every element centralizing the layer is central
in the ambient group. -/
theorem centralizer_layer_le_center_of_fittingSubgroup_eq_center
    (hF :
      fittingSubgroup G = Subgroup.center G) :
    Subgroup.centralizer (layer G : Set G) ≤
      Subgroup.center G := by
  rw [
    centralizer_layer_eq_generalizedFittingCentralizer_of_eq_center
      hF,
    centralizer_generalizedFittingSubgroup_eq_map_center]
  exact
    map_center_generalizedFittingSubgroup_le_fittingSubgroup.trans_eq
      hF

/-- Under `F(G) = Z(G)`, the centralizer of the layer lies in every layer
intermediate. -/
theorem centralizer_layer_le_layerIntermediate_of_fittingSubgroup_eq_center
    {p : ℕ}
    (Q : Sylow p (layer G))
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hF :
      fittingSubgroup G = Subgroup.center G) :
    Subgroup.centralizer (layer G : Set G) ≤
      layerIntermediate G Q M := by
  apply
    (centralizer_layer_le_center_of_fittingSubgroup_eq_center
      hF).trans
  apply
    (Subgroup.center_le_normalizer
      (Sylow.ambientSubgroup Q : Set G)).trans
  exact
    layerSylowAmbientNormalizer_le_layerIntermediate
      G Q M

end GroupTheory
end McKayConjecture
