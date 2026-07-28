/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.FittingPrimeDecomposition
import McKayConjecture.GroupTheory.GeneralizedFittingDegenerate
import McKayConjecture.GroupTheory.LayerCenter
import McKayConjecture.GroupTheory.PCoreNormalizer
import McKayConjecture.GroupTheory.PPrimeCoreSylowIntersection
import McKayConjecture.GroupTheory.SylowQuotient

/-!
# Structural interface for a Rossi minimal counterexample

This file does not claim that the Rossi minimal-counterexample reduction
has been proved.  Instead, `MinimalCounterexampleStructure P` records its
two group-theoretic consequences used below, together with the explicit
nontrivial-case hypotheses on `G` and the Sylow normalizer.

From precisely those inputs and the independently proved finite-group
lemmas, we derive the standard structure:

* `O_p(G)` and `O_{p′}(G)` lie in `Z(G)`;
* `F(G) = Z(G)` and `F(G) < F*(G)`;
* `E(G)` is not central;
* the canonical Sylow intersection with `E(G)` is noncentral in `G`;
* the ambient image of `Z(E(G))` lies in `Z(G)`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open McKayConjecture.GroupTheory
open scoped IsMulCommutative

/-- The explicit group-theoretic output required from the still-external
Rossi minimal-counterexample reduction.

The two final fields are the substantive Rossi consequences.  The first
two fields keep the nontrivial minimal-counterexample case visible. -/
structure MinimalCounterexampleStructure
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : Prop where
  /-- The chosen Sylow normalizer is proper. -/
  normalizer_ne_top :
    Subgroup.normalizer (P : Set G) ≠ ⊤
  /-- The ambient group is noncommutative. -/
  noncommutative :
    ¬IsMulCommutative G
  /-- A noncentral normal subgroup together with the chosen Sylow
  normalizer generates the whole group.

  This is the exact numerical content of Rossi's minimal-counterexample
  Corollary 4.3 (after replacing the normal subgroup by its product with
  the center). -/
  normal_sup_sylowNormalizer_eq_top :
    ∀ N : Subgroup G,
      N.Normal →
      ¬N ≤ Subgroup.center G →
      N ⊔ Subgroup.normalizer (P : Set G) = ⊤
  /-- A normal subgroup whose intersection with the chosen Sylow
  subgroup is central must itself be central. -/
  normal_le_center_of_inf_sylow_le_center :
    ∀ K : Subgroup G,
      K.Normal →
      K ⊓ (P : Subgroup G) ≤
          Subgroup.center G →
      K ≤ Subgroup.center G

/-- The canonical Sylow `p`-subgroup of the layer obtained by
intersecting the chosen ambient Sylow subgroup with `E(G)`. -/
def layerSylowIntersection
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    Sylow p (layer G) :=
  GroupTheory.Sylow.intersectionNormal
    P (layer G)

@[simp, norm_cast]
theorem map_layerSylowIntersection_subtype
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    (layerSylowIntersection P :
        Subgroup (layer G)).map
          (layer G).subtype =
      (P : Subgroup G) ⊓ layer G := by
  simpa only [layerSylowIntersection]
    using
      McKayConjecture.GroupTheory.Sylow.map_intersectionNormal_subtype
        P (layer G)

namespace MinimalCounterexampleStructure

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}

/-- The `p`-core is central. -/
theorem pCore_le_center
    (h : MinimalCounterexampleStructure P) :
    pCore p G ≤ Subgroup.center G := by
  by_contra hnoncentral
  have hgenerate :
      pCore p G ⊔
          Subgroup.normalizer (P : Set G) =
        ⊤ :=
    h.normal_sup_sylowNormalizer_eq_top
      (pCore p G) inferInstance
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

/-- The `p′`-core is central. -/
theorem pPrimeCore_le_center
    (h : MinimalCounterexampleStructure P) :
    pPrimeCore p G ≤
      Subgroup.center G := by
  apply
    h.normal_le_center_of_inf_sylow_le_center
      (pPrimeCore p G) inferInstance
  rw [GroupTheory.pPrimeCore_inf_sylow_eq_bot]
  exact bot_le

/-- The Fitting subgroup is exactly the center. -/
theorem fittingSubgroup_eq_center
    (h : MinimalCounterexampleStructure P) :
    fittingSubgroup G =
      Subgroup.center G :=
  McKayConjecture.GroupTheory.fittingSubgroup_eq_center_of_pCore_le_center_of_pPrimeCore_le_center
      Fact.out h.pCore_le_center
      h.pPrimeCore_le_center

/-- The Fitting subgroup is properly contained in the generalized
Fitting subgroup. -/
theorem fittingSubgroup_lt_generalizedFittingSubgroup
    (h : MinimalCounterexampleStructure P) :
    fittingSubgroup G <
      generalizedFittingSubgroup G :=
  McKayConjecture.GroupTheory.fittingSubgroup_lt_generalizedFittingSubgroup_of_eq_center
      h.noncommutative
      h.fittingSubgroup_eq_center

/-- The layer is not contained in the ambient center. -/
theorem not_layer_le_center
    (h : MinimalCounterexampleStructure P) :
    ¬layer G ≤ Subgroup.center G :=
  McKayConjecture.GroupTheory.not_layer_le_center_of_fittingSubgroup_eq_center
      h.noncommutative
      h.fittingSubgroup_eq_center

/-- The canonical Sylow intersection with `E(G)`, mapped back into
`G`, is not central in `G`. -/
theorem not_layerSylowIntersection_le_center
    (h : MinimalCounterexampleStructure P) :
    ¬(layerSylowIntersection P :
          Subgroup (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G := by
  intro hQcentral
  apply h.not_layer_le_center
  apply
    h.normal_le_center_of_inf_sylow_le_center
      (layer G) inferInstance
  have hintersection := hQcentral
  rw [map_layerSylowIntersection_subtype]
    at hintersection
  simpa only [inf_comm]
    using hintersection

/-- The ambient image of `Z(E(G))` lies in `Z(G)`. -/
theorem map_center_layer_le_center
    (h : MinimalCounterexampleStructure P) :
    (Subgroup.center (layer G)).map
        (layer G).subtype ≤
      Subgroup.center G :=
  McKayConjecture.GroupTheory.map_center_layer_le_center_of_fittingSubgroup_eq_center
      h.fittingSubgroup_eq_center

end MinimalCounterexampleStructure
end InductiveMcKay
end McKayConjecture
