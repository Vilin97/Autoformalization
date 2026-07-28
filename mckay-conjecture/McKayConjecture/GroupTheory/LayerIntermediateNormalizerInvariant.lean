/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.ComponentLocalSubgroupNormalizer
import McKayConjecture.GroupTheory.LayerIntermediate

/-!
# Layer intermediates with only normalizer invariance

The component-local family in the Rossi reduction is equivariant under
`N_G(Q)`, where `Q` is the selected Sylow subgroup of the layer.  It need not
be equivariant under all of `G`.  The relative invariance API proves exactly
the normalizer containment required by the Frattini intermediate argument.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable (G : Type u) [Group G] [Finite G]

/-- The ambient normalizer acting in the layer-intermediate construction. -/
abbrev LayerSylowAmbientNormalizer
    {p : ℕ} (Q : Sylow p (layer G)) :
    Subgroup G :=
  Subgroup.normalizer
    (Sylow.ambientSubgroup Q : Set G)

omit [Finite G] in
/-- Relative equivariance under `N_G(Q)` makes `N_G(Q)` normalize the
component-local subgroup. -/
theorem layerSylowAmbientNormalizer_le_normalizer_componentLocal
    {p : ℕ}
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (Q : Sylow p (layer G))
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M) :
    LayerSylowAmbientNormalizer G Q ≤
      Subgroup.normalizer
        (componentLocalSubgroup G M) :=
  le_normalizer_componentLocalSubgroup
    G (LayerSylowAmbientNormalizer G Q) M hM

/-- The layer intermediate is proper under the exact invariance group
available in the reduction theorem. -/
theorem componentLocal_sup_ambientNormalizer_lt_top_of_normalizerInvariant
    {p : ℕ}
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (Q : Sylow p (layer G))
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M)
    (hcenter :
      ∀ K, Subgroup.center K.1 ≤ M K)
    (hproper :
      ∃ K, M K < ⊤)
    (hQ :
      Subgroup.normalizer
          (Q : Set (layer G)) ≤
        componentLocalSubgroupInLayer G M) :
    componentLocalSubgroup G M ⊔
        LayerSylowAmbientNormalizer G Q <
      ⊤ := by
  have hinvariant :
      LayerSylowAmbientNormalizer G Q ≤
        Subgroup.normalizer
          ((componentLocalSubgroupInLayer G M).map
            (layer G).subtype) := by
    rw [map_componentLocalSubgroupInLayer]
    exact
      layerSylowAmbientNormalizer_le_normalizer_componentLocal
        G M Q hM
  simpa only [map_componentLocalSubgroupInLayer] using
    Sylow.map_sup_ambientNormalizer_lt_top
      (layer G) Q
      (componentLocalSubgroupInLayer G M)
      (componentLocalSubgroupInLayer_lt_top
        G M hcenter hproper)
      hQ hinvariant

/-- Central-index decrease for the normalizer-invariant layer
intermediate. -/
theorem centralIndex_componentLocal_sup_ambientNormalizer_lt_of_normalizerInvariant
    {p : ℕ}
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (Q : Sylow p (layer G))
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M)
    (hcenter :
      ∀ K, Subgroup.center K.1 ≤ M K)
    (hproper :
      ∃ K, M K < ⊤)
    (hQ :
      Subgroup.normalizer
          (Q : Set (layer G)) ≤
        componentLocalSubgroupInLayer G M)
    (hZ :
      Subgroup.center G ≤
        componentLocalSubgroup G M ⊔
          LayerSylowAmbientNormalizer G Q) :
    centralIndex
        ↥(componentLocalSubgroup G M ⊔
          LayerSylowAmbientNormalizer G Q) <
      centralIndex G :=
  centralIndex_lt_of_center_le_of_lt_top
    (componentLocalSubgroup G M ⊔
      LayerSylowAmbientNormalizer G Q)
    hZ
    (componentLocal_sup_ambientNormalizer_lt_top_of_normalizerInvariant
      G M Q hM hcenter hproper hQ)

/-- The center-containment hypothesis in the preceding theorem is automatic:
the ambient center normalizes every subgroup, hence lies in `N_G(Q)`. -/
theorem centralIndex_componentLocal_sup_ambientNormalizer_lt_of_normalizerInvariant'
    {p : ℕ}
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (Q : Sylow p (layer G))
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G (LayerSylowAmbientNormalizer G Q) M)
    (hcenter :
      ∀ K, Subgroup.center K.1 ≤ M K)
    (hproper :
      ∃ K, M K < ⊤)
    (hQ :
      Subgroup.normalizer
          (Q : Set (layer G)) ≤
        componentLocalSubgroupInLayer G M) :
    centralIndex
        ↥(componentLocalSubgroup G M ⊔
          LayerSylowAmbientNormalizer G Q) <
      centralIndex G := by
  apply
    centralIndex_componentLocal_sup_ambientNormalizer_lt_of_normalizerInvariant
      G M Q hM hcenter hproper hQ
  exact
    (Subgroup.center_le_normalizer
      (Sylow.ambientSubgroup Q : Set G)).trans
      le_sup_right

end GroupTheory
end McKayConjecture
