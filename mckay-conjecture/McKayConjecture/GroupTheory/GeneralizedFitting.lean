/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.Component
import McKayConjecture.GroupTheory.Fitting

/-!
# The generalized Fitting subgroup

The generalized Fitting subgroup is

`F*(G) = F(G) E(G)`,

represented in the subgroup lattice by the join of the Fitting subgroup and
the layer.  This file records the definition, functoriality, characteristic
property, and elementary centralizer identities.  The self-centralizing
theorem is proved only after the finite Fitting-product and component
commutation layers are available.
-/

noncomputable section

universe u v

namespace McKayConjecture.GroupTheory

variable (G : Type u) [Group G]

/-- The generalized Fitting subgroup `F*(G) = F(G)E(G)`. -/
def generalizedFittingSubgroup : Subgroup G :=
  fittingSubgroup G ⊔ layer G

variable {G}

/-- The Fitting subgroup lies in the generalized Fitting subgroup. -/
theorem fittingSubgroup_le_generalizedFitting :
    fittingSubgroup G ≤ generalizedFittingSubgroup G :=
  le_sup_left

/-- The layer lies in the generalized Fitting subgroup. -/
theorem layer_le_generalizedFitting :
    layer G ≤ generalizedFittingSubgroup G :=
  le_sup_right

/-- The generalized Fitting subgroup is the least subgroup containing the
Fitting subgroup and the layer. -/
theorem generalizedFittingSubgroup_le {K : Subgroup G}
    (hF : fittingSubgroup G ≤ K) (hE : layer G ≤ K) :
    generalizedFittingSubgroup G ≤ K :=
  sup_le hF hE

/-- Isomorphisms map the generalized Fitting subgroup into its counterpart
in the target. -/
theorem map_generalizedFittingSubgroup_le
    {H : Type v} [Group H] (e : G ≃* H) :
    (generalizedFittingSubgroup G).map e.toMonoidHom ≤
      generalizedFittingSubgroup H := by
  rw [generalizedFittingSubgroup, Subgroup.map_sup]
  exact sup_le
    ((map_fittingSubgroup_le e).trans
      fittingSubgroup_le_generalizedFitting)
    ((map_layer_le e).trans layer_le_generalizedFitting)

/-- Isomorphisms map generalized Fitting subgroups exactly. -/
theorem map_generalizedFittingSubgroup_mulEquiv
    {H : Type v} [Group H] (e : G ≃* H) :
    (generalizedFittingSubgroup G).map e.toMonoidHom =
      generalizedFittingSubgroup H := by
  rw [generalizedFittingSubgroup, Subgroup.map_sup,
    map_fittingSubgroup_mulEquiv e, map_layer_mulEquiv e]
  rfl

/-- The generalized Fitting subgroup is characteristic. -/
instance generalizedFittingSubgroup_characteristic :
    (generalizedFittingSubgroup G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  exact map_generalizedFittingSubgroup_le e

/-- The generalized Fitting subgroup is normal. -/
instance generalizedFittingSubgroup_normal :
    (generalizedFittingSubgroup G).Normal :=
  inferInstance

/-- The centralizer of a join is the intersection of the two
centralizers. -/
theorem centralizer_sup (K L : Subgroup G) :
    Subgroup.centralizer ((K ⊔ L : Subgroup G) : Set G) =
      Subgroup.centralizer (K : Set G) ⊓
        Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    constructor
    · intro k hk
      exact hx k (Or.inl hk)
    · intro l hl
      exact hx l (Or.inr hl)
  · rintro ⟨hxK, hxL⟩ y (hyK | hyL)
    · exact hxK y hyK
    · exact hxL y hyL

/-- The centralizer of `F*(G)` is the intersection of the centralizers of
`F(G)` and `E(G)`. -/
theorem centralizer_generalizedFittingSubgroup :
    Subgroup.centralizer
        (generalizedFittingSubgroup G : Set G) =
      Subgroup.centralizer (fittingSubgroup G : Set G) ⊓
        Subgroup.centralizer (layer G : Set G) := by
  rw [generalizedFittingSubgroup]
  exact centralizer_sup (fittingSubgroup G) (layer G)

end McKayConjecture.GroupTheory
