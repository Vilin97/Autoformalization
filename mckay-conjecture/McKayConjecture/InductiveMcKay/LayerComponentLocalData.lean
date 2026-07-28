/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.LayerSylowCoordinates
import McKayConjecture.InductiveMcKay.QuasisimpleHypothesis

/-!
# Inductive-McKay data on the components of the layer

A coordinate lift of a Sylow subgroup of the layer selects a Sylow subgroup
inside every component.  Under the quasisimple inductive-McKay hypothesis,
each coordinate has full local data.  This file packages those choices and
derives the elementary subgroup properties used in the layer construction:

* every coordinate intermediate contains the coordinate Sylow normalizer;
* hence it contains the component center and the Sylow subgroup itself; and
* if the layer Sylow is noncentral, at least one coordinate intermediate is
  proper.

Equivariance between different components is intentionally not asserted here;
it requires coordinating the choices with the ambient normalizer action.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}

/-- Full local data chosen on every component coordinate of a layer Sylow
lift. -/
structure LayerComponentLocalData
    (D : LayerSylowCoordinateData G p Q) where
  /-- The full inductive-McKay datum in one component. -/
  data :
    ∀ K : ComponentIndex G,
      LocalInductiveMcKayData (D.coordinate K)

namespace LayerComponentLocalData

variable {D : LayerSylowCoordinateData G p Q}

/-- Choose component data from the quasisimple inductive-McKay
hypothesis. -/
def ofQuasisimpleHypothesis
    (h : QuasisimpleInductiveMcKayHypothesis.{0} p) :
    LayerComponentLocalData D where
  data K :=
    Classical.choice
      (h K.1 K.2.isQuasisimple (D.coordinate K))

/-- The coordinate-local intermediate subgroup in each component. -/
abbrev intermediate
    (d : LayerComponentLocalData D)
    (K : ComponentIndex G) :
    Subgroup K.1 :=
  (d.data K).intermediate

/-- The coordinate Sylow normalizer lies in its local intermediate. -/
theorem normalizer_le_intermediate
    (d : LayerComponentLocalData D)
    (K : ComponentIndex G) :
    Subgroup.normalizer
        (D.coordinate K : Set K.1) ≤
      d.intermediate K :=
  (d.data K).normalizer_le

/-- The center of every component lies in its local intermediate. -/
theorem center_le_intermediate
    (d : LayerComponentLocalData D)
    (K : ComponentIndex G) :
    Subgroup.center K.1 ≤
      d.intermediate K :=
  (Subgroup.center_le_normalizer
      (D.coordinate K : Set K.1)).trans
    (d.normalizer_le_intermediate K)

/-- The coordinate Sylow subgroup itself lies in its local intermediate. -/
theorem coordinate_le_intermediate
    (d : LayerComponentLocalData D)
    (K : ComponentIndex G) :
    (D.coordinate K : Subgroup K.1) ≤
      d.intermediate K :=
  Subgroup.le_normalizer.trans
    (d.normalizer_le_intermediate K)

/-- A noncentral layer Sylow gives at least one proper coordinate-local
intermediate subgroup. -/
theorem exists_intermediate_lt_top
    (d : LayerComponentLocalData D)
    (hQnoncentral :
      ¬(Q : Subgroup (layer G)) ≤
        Subgroup.center (layer G)) :
    ∃ K : ComponentIndex G,
      d.intermediate K < ⊤ := by
  obtain ⟨K, _hKcentral, hnormalizer⟩ :=
    D.exists_coordinate_normalizer_lt_top
      hQnoncentral
  exact
    ⟨K,
      (d.data K).proper_of_normalizer_ne_top
        hnormalizer.ne⟩

/-- Ambient noncentrality gives a proper coordinate under the exact
center-image hypothesis used by the minimal-counterexample reduction. -/
theorem exists_intermediate_lt_top_of_map_not_le_center
    (d : LayerComponentLocalData D)
    (hcenterImage :
      (Subgroup.center (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G)
    (hQambient :
      ¬(Q : Subgroup (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G) :
    ∃ K : ComponentIndex G,
      d.intermediate K < ⊤ :=
  d.exists_intermediate_lt_top
    (D.not_le_center_layer_of_map_not_le_center
      hcenterImage hQambient)

/-- The local intermediate in a component is invariant under every
automorphism stabilizing the selected coordinate Sylow subgroup. -/
theorem intermediate_invariant
    (d : LayerComponentLocalData D)
    (K : ComponentIndex G) :
    AutomorphismInvariant
      (SylowAutStabilizer (D.coordinate K))
      (d.intermediate K) :=
  (d.data K).intermediate_invariant

/-- The componentwise `p'`-character correspondence. -/
abbrev correspondence
    (d : LayerComponentLocalData D)
    (K : ComponentIndex G) :
    PPrimeIrreducibleCharacter K.1 p ≃
      PPrimeIrreducibleCharacter (d.intermediate K) p :=
  (d.data K).correspondence

end LayerComponentLocalData

end InductiveMcKay
end McKayConjecture
