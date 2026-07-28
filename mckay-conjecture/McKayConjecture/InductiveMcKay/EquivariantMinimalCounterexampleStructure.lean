/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer
import McKayConjecture.InductiveMcKay.MinimalCounterexampleStructure

/-!
# Equivariant minimal-counterexample structure

For the full inductive McKay condition the external overgroup is the
canonical semidirect product by `Aut(G)_P`.  Rossi's normal subgroups are
normal in that external overgroup.  Internally, this means that they are
both normal in `G` and invariant under `SylowAutStabilizer P`.

The numerical minimal-counterexample interface may quantify over every
normal subgroup because it takes the external group to be `G` itself.
That stronger assertion is not available in the full equivariant
reduction.  This file records the exact invariant version and derives the
same layer consequences needed later.  The subgroups used in those
consequences—the two cores and the layer—are characteristic, hence satisfy
the required invariance.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open McKayConjecture.GroupTheory
open scoped IsMulCommutative

/-- Structural output of a minimal counterexample to the full inductive
McKay condition, with normal-subgroup conclusions restricted to the
subgroups normalized by the external automorphism overgroup. -/
structure EquivariantMinimalCounterexampleStructure
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : Prop where
  /-- The chosen Sylow normalizer is proper. -/
  normalizer_ne_top :
    Subgroup.normalizer (P : Set G) ≠ ⊤
  /-- The ambient group is noncommutative. -/
  noncommutative :
    ¬IsMulCommutative G
  /-- An `Aut(G)_P`-invariant noncentral normal subgroup and the Sylow
  normalizer generate the whole group. -/
  invariantNormal_sup_sylowNormalizer_eq_top :
    ∀ N : Subgroup G,
      N.Normal →
      AutomorphismInvariant (SylowAutStabilizer P) N →
      ¬N ≤ Subgroup.center G →
      N ⊔ Subgroup.normalizer (P : Set G) = ⊤
  /-- An `Aut(G)_P`-invariant normal subgroup with central Sylow
  intersection is central. -/
  invariantNormal_le_center_of_inf_sylow_le_center :
    ∀ K : Subgroup G,
      K.Normal →
      AutomorphismInvariant (SylowAutStabilizer P) K →
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G →
      K ≤ Subgroup.center G

namespace EquivariantMinimalCounterexampleStructure

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}

omit [Finite G] [Fact p.Prime] in
/-- A characteristic subgroup is invariant under the canonical Sylow
automorphism stabilizer. -/
theorem automorphismInvariant_of_characteristic
    (H : Subgroup G) [H.Characteristic] :
    AutomorphismInvariant (SylowAutStabilizer P) H := by
  intro a
  exact
    Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : H.Characteristic) a.1

/-- The `p`-core is central in a full equivariant minimal counterexample. -/
theorem pCore_le_center
    (h : EquivariantMinimalCounterexampleStructure P) :
    pCore p G ≤ Subgroup.center G := by
  by_contra hnoncentral
  have hgenerate :
      pCore p G ⊔
          Subgroup.normalizer (P : Set G) =
        ⊤ :=
    h.invariantNormal_sup_sylowNormalizer_eq_top
      (pCore p G) inferInstance
      (automorphismInvariant_of_characteristic (P := P)
        (pCore p G))
      hnoncentral
  have htopLe :
      (⊤ : Subgroup G) ≤
        Subgroup.normalizer (P : Set G) := by
    rw [← hgenerate]
    exact
      sup_le
        (GroupTheory.pCore_le_sylowNormalizer P)
        le_rfl
  exact
    h.normalizer_ne_top
      (top_unique htopLe)

/-- The `p′`-core is central in a full equivariant minimal
counterexample. -/
theorem pPrimeCore_le_center
    (h : EquivariantMinimalCounterexampleStructure P) :
    pPrimeCore p G ≤ Subgroup.center G := by
  apply
    h.invariantNormal_le_center_of_inf_sylow_le_center
      (pPrimeCore p G) inferInstance
      (automorphismInvariant_of_characteristic (P := P)
        (pPrimeCore p G))
  rw [GroupTheory.pPrimeCore_inf_sylow_eq_bot]
  exact bot_le

/-- The Fitting subgroup is exactly the center. -/
theorem fittingSubgroup_eq_center
    (h : EquivariantMinimalCounterexampleStructure P) :
    fittingSubgroup G = Subgroup.center G :=
  McKayConjecture.GroupTheory.fittingSubgroup_eq_center_of_pCore_le_center_of_pPrimeCore_le_center
    Fact.out h.pCore_le_center h.pPrimeCore_le_center

/-- The Fitting subgroup is properly contained in the generalized Fitting
subgroup. -/
theorem fittingSubgroup_lt_generalizedFittingSubgroup
    (h : EquivariantMinimalCounterexampleStructure P) :
    fittingSubgroup G < generalizedFittingSubgroup G :=
  McKayConjecture.GroupTheory.fittingSubgroup_lt_generalizedFittingSubgroup_of_eq_center
    h.noncommutative h.fittingSubgroup_eq_center

/-- The layer is noncentral. -/
theorem not_layer_le_center
    (h : EquivariantMinimalCounterexampleStructure P) :
    ¬layer G ≤ Subgroup.center G :=
  McKayConjecture.GroupTheory.not_layer_le_center_of_fittingSubgroup_eq_center
    h.noncommutative h.fittingSubgroup_eq_center

/-- The canonical layer Sylow intersection is noncentral in the ambient
group. -/
theorem not_layerSylowIntersection_le_center
    (h : EquivariantMinimalCounterexampleStructure P) :
    ¬(layerSylowIntersection P :
          Subgroup (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G := by
  intro hQcentral
  apply h.not_layer_le_center
  apply
    h.invariantNormal_le_center_of_inf_sylow_le_center
      (layer G) inferInstance
      (automorphismInvariant_of_characteristic (P := P)
        (layer G))
  have hintersection := hQcentral
  rw [map_layerSylowIntersection_subtype]
    at hintersection
  simpa only [inf_comm] using hintersection

/-- The ambient image of the center of the layer lies in the center of
the ambient group. -/
theorem map_center_layer_le_center
    (h : EquivariantMinimalCounterexampleStructure P) :
    (Subgroup.center (layer G)).map
        (layer G).subtype ≤
      Subgroup.center G :=
  McKayConjecture.GroupTheory.map_center_layer_le_center_of_fittingSubgroup_eq_center
    h.fittingSubgroup_eq_center

end EquivariantMinimalCounterexampleStructure
end InductiveMcKay
end McKayConjecture
