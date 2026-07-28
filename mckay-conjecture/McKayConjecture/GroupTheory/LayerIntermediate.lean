/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.ComponentLocalInvariant
import McKayConjecture.GroupTheory.FrattiniIntermediate

/-!
# Proper intermediate subgroups built from the layer

Let `Q` be a Sylow subgroup of the layer `E(G)`.  An exactly
conjugation-equivariant family of proper component-local subgroups
generates a normal subgroup `M₀ < E(G)`.  If the internal normalizer
`N_{E(G)}(Q)` lies in the pullback of `M₀` to `E(G)`, the Frattini
intersection argument shows that

`M₀ ⊔ N_G(Q)`

is a proper subgroup of `G`.  If it also contains `Z(G)`, its central
index is strictly smaller than that of `G`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable (G : Type u) [Group G] [Finite G]

/-- The component-local subgroup, pulled back from the ambient group to
the carrier of the layer. -/
def componentLocalSubgroupInLayer
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    Subgroup (layer G) :=
  (componentLocalSubgroup G M).comap (layer G).subtype

/-- Mapping the pullback of the component-local subgroup out of the
layer recovers the original ambient subgroup. -/
@[simp]
theorem map_componentLocalSubgroupInLayer
    (M : ∀ K : ComponentIndex G, Subgroup K.1) :
    (componentLocalSubgroupInLayer G M).map
        (layer G).subtype =
      componentLocalSubgroup G M := by
  rw [componentLocalSubgroupInLayer,
    Subgroup.map_comap_eq,
    (layer G).range_subtype,
    inf_eq_right.mpr
      (componentLocalSubgroup_le_layer G M)]

/-- Coordinate center containment and one proper coordinate make the
pulled-back component-local subgroup proper in the layer. -/
theorem componentLocalSubgroupInLayer_lt_top
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hcenter :
      ∀ K, Subgroup.center K.1 ≤ M K)
    (hproper :
      ∃ K, M K < ⊤) :
    componentLocalSubgroupInLayer G M < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hlayer :
      layer G ≤ componentLocalSubgroup G M := by
    rw [← Subgroup.subgroupOf_eq_top]
    simpa only [componentLocalSubgroupInLayer,
      Subgroup.comap_subtype] using htop
  exact
    (componentLocalSubgroup_lt_layer
      G M hcenter hproper).2 hlayer

omit [Finite G] in
/-- Global normality of an equivariant component-local subgroup makes
every ambient subgroup, in particular the ambient Sylow normalizer,
normalize it. -/
theorem ambientNormalizer_le_normalizer_componentLocalSubgroup
    {p : ℕ}
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM : ComponentLocalFamily.IsConjugationEquivariant G M)
    (Q : Sylow p (layer G)) :
    Subgroup.normalizer
        (Sylow.ambientSubgroup Q : Set G) ≤
      Subgroup.normalizer
        (componentLocalSubgroup G M) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr
    (componentLocalSubgroup_normal G M hM)]
  exact le_top

/-- The exact layer intermediate is proper when the internal Sylow
normalizer is contained in the component-local subgroup pulled back to
the layer. -/
theorem componentLocal_sup_ambientNormalizer_lt_top
    {p : ℕ}
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM : ComponentLocalFamily.IsConjugationEquivariant G M)
    (Q : Sylow p (layer G))
    (hcenter :
      ∀ K, Subgroup.center K.1 ≤ M K)
    (hproper :
      ∃ K, M K < ⊤)
    (hQ :
      Subgroup.normalizer
          (Q : Set (layer G)) ≤
        componentLocalSubgroupInLayer G M) :
    componentLocalSubgroup G M ⊔
        Subgroup.normalizer
          (Sylow.ambientSubgroup Q : Set G) <
      ⊤ := by
  have hinvariant :
      Subgroup.normalizer
          (Sylow.ambientSubgroup Q : Set G) ≤
        Subgroup.normalizer
          ((componentLocalSubgroupInLayer G M).map
            (layer G).subtype) := by
    rw [map_componentLocalSubgroupInLayer]
    exact
      ambientNormalizer_le_normalizer_componentLocalSubgroup
        G M hM Q
  simpa only [map_componentLocalSubgroupInLayer] using
    Sylow.map_sup_ambientNormalizer_lt_top
      (layer G) Q
      (componentLocalSubgroupInLayer G M)
      (componentLocalSubgroupInLayer_lt_top
        G M hcenter hproper)
      hQ hinvariant

/-- If the exact proper layer intermediate contains the ambient center,
then it has strictly smaller central index than `G`. -/
theorem centralIndex_componentLocal_sup_ambientNormalizer_lt
    {p : ℕ}
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM : ComponentLocalFamily.IsConjugationEquivariant G M)
    (Q : Sylow p (layer G))
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
          Subgroup.normalizer
            (Sylow.ambientSubgroup Q : Set G)) :
    centralIndex
        ↥(componentLocalSubgroup G M ⊔
          Subgroup.normalizer
            (Sylow.ambientSubgroup Q : Set G)) <
      centralIndex G :=
  centralIndex_lt_of_center_le_of_lt_top
    (componentLocalSubgroup G M ⊔
      Subgroup.normalizer
        (Sylow.ambientSubgroup Q : Set G))
    hZ
    (componentLocal_sup_ambientNormalizer_lt_top
      G M hM Q hcenter hproper hQ)

end GroupTheory
end McKayConjecture
