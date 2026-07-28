/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.EquivariantMinimalCounterexampleStructure
import McKayConjecture.InductiveMcKay.LayerIntermediateReduction

/-!
# Layer-intermediate consequences of equivariant minimality

The layer is characteristic, so the invariant-normal-subgroup conclusions
of `EquivariantMinimalCounterexampleStructure` suffice for the same
centralizer containment and properness facts used in the layer reduction.
This file provides the full-reduction variants without conflating them with
the stronger numerical minimal-counterexample interface.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}
variable
  {D :
    LayerSylowCoordinateData G p
      (layerSylowIntersection P)}

namespace ComponentOrbitLocalData

/-- Equivariant minimality puts the centralizer of the layer in the
canonical layer intermediate. -/
theorem centralizer_layer_le_ambientIntermediate_of_equivariantMinimalCounterexample
    (d : ComponentOrbitLocalData D)
    (h : EquivariantMinimalCounterexampleStructure P) :
    Subgroup.centralizer (layer G : Set G) ≤
      d.ambientIntermediate :=
  centralizer_layer_le_layerIntermediate_of_fittingSubgroup_eq_center
    (layerSylowIntersection P) d.intermediate
    h.fittingSubgroup_eq_center

/-- The canonical layer intermediate has strictly smaller central index
under equivariant minimality. -/
theorem centralIndex_ambientIntermediate_lt_of_equivariantMinimalCounterexample
    (d : ComponentOrbitLocalData D)
    (h : EquivariantMinimalCounterexampleStructure P) :
    centralIndex d.ambientIntermediate < centralIndex G :=
  d.centralIndex_ambientIntermediate_lt_of_map_not_le_center
    h.map_center_layer_le_center
    h.not_layerSylowIntersection_le_center

/-- In particular, the canonical layer intermediate is proper. -/
theorem ambientIntermediate_lt_top_of_equivariantMinimalCounterexample
    (d : ComponentOrbitLocalData D)
    (h : EquivariantMinimalCounterexampleStructure P) :
    d.ambientIntermediate < ⊤ :=
  d.ambientIntermediate_lt_top
    (d.exists_intermediate_lt_top_of_map_not_le_center
      h.map_center_layer_le_center
      h.not_layerSylowIntersection_le_center)

end ComponentOrbitLocalData
end InductiveMcKay
end McKayConjecture
